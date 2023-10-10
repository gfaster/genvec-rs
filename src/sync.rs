#![allow(dead_code)]
use std::{
    cell::UnsafeCell,
    mem::MaybeUninit,
    ops::Deref,
    sync::{
        atomic::{AtomicPtr, AtomicUsize, Ordering},
        Mutex,
    },
};

/// Simple allocator for many identical objects with unknown lifetimes
///
/// This is a potential alternative for [`Rc`][std::rc::Rc] in cases where you have many objects of
/// the same type and you don't want weak pointers to cause a memory leak. unlike
/// [`Rc`][std::rc::Rc], [`GenVec`] allows the memory of objects dropped after their last strong
/// pointer to be reused even while weak pointers exist.
pub struct GenVec<T> {
    /// Contains the arena count, and semantically allows for appending to arena list
    ///
    /// it's nice to have the requirement of a lock to append to the arena list. In the future I
    /// may improve this.
    arena_init_lock: Mutex<u32>,

    /// circularly linked list of arenas
    arena: AtomicPtr<ArenaNode<T>>,

    /// the capacity of each arena
    arena_cap: usize,
}

struct ArenaNode<T> {
    /// current generation: only modified when locked
    generation: UnsafeCell<usize>,

    /// I would like this to be in the same allocation, but that's somewhat annoying in Rust.
    inner: Vec<Inner<T>>,

    free_cnt: AtomicUsize,
    free_head: Mutex<usize>,

    next: AtomicPtr<ArenaNode<T>>,
}
unsafe impl<T: Sync> Sync for ArenaNode<T> {}

impl<T> ArenaNode<T> {
    /// does this allocation need to be dropped
    const DROP_BIT: usize = 1 << (usize::BITS - 1);

    /// Try to increment the reference count of this slot, returning `Ok` if we locked in an
    /// active allocation and `Err` on failure. On success, `dec_ref()` will need to be called to
    /// properly release this reference. Nothing needs to be done on failure.
    ///
    /// Has at least `Acquire` ordering over the slot's `refs`.
    #[inline(always)]
    fn try_inc_ref(&self, idx: usize) -> Result<(), ()> {
        let inner = &self.inner[idx];
        let prev = inner.refs.fetch_add(1, Ordering::Acquire);

        // we check without ignoring the drop bit since if the ref count was zero and the drop bit
        // was set, the allocation is dead and another thread is about to free it regardless of this
        // thread's changes to the ref count. We still need to responsibly decrement in case an
        // item was allocated and dropped after we incremented the ref counter
        if prev > Self::DROP_BIT {
            return Ok(());
        }

        // this was an empty slot, at least at the time of incrementing. As far as we're concerned
        // now, even if another thread increments the ref count, the attempt still failed. However,
        // we still need to take care of freeing the object if the object was dropped in this time
        // frame. There was nothing modified, so relax ordering decrement is fine.
        self.dec_ref(idx, Ordering::Relaxed);

        return Err(());
    }

    /// decrements the ref count, drop+freeing the contained item if necessary.
    #[inline(always)]
    fn dec_ref(&self, idx: usize, ordering: Ordering) {
        let inner = &self.inner[idx];
        let new_val = inner.refs.fetch_sub(1, ordering) - 1;
        // if the new value is has just the drop bit set, then the following holds:
        // 1) this is the last reference to an allocation
        // 2) the allocation is not in the free list
        // 3) it is not a given that this thread will be the one to free the allocation
        if new_val == Self::DROP_BIT {
            self.last_ref(inner, idx);
        }
    }

    /// slow path for `dec_ref`
    fn last_ref(&self, inner: &Inner<T>, idx: usize) {
        // if just the drop bit is still set, then the following holds:
        // 1) this thread will drop the item and add to the free list
        // 2) there are no threads that can create a allocation reference
        if inner
            .refs
            .compare_exchange(Self::DROP_BIT, 0, Ordering::AcqRel, Ordering::Relaxed)
            .is_err()
        {
            // The allocation was incremented from zero by another thread, it will be the one
            // to drop this allocation
            return;
        }

        // Safety: this thread won the drop privileges, and since the drop bit was set, the
        // item is initialized. We atomically ensured that
        unsafe { (&mut *inner.item.get()).assume_init_drop() };

        // I'm uncertain which is faster here I might be able to just rely on the free count
        // decrement at the end of the block.
        // inner.refs.fetch_or(0, Ordering::Release);
        std::sync::atomic::fence(Ordering::Release);

        let mut lock = self.free_head.lock().expect("thread panicked");
        // Safety: we have the allocation write lock
        unsafe { inner.next.get().write(*lock) };
        *lock = idx;
        self.free_cnt.fetch_add(1, Ordering::Release);
        drop(lock);

    }

    /// Creates a new arena and inserts it directly after the current head of the arena list, and
    /// updates the arena pointer to point to the newly created arena. If the current head is null,
    /// then it will be set to the newly created arena. Maintains a circuluarly linked list.
    ///
    /// Needs to acquire a write lock (only competes with other calls to this function).
    fn new_in(genvec: &GenVec<T>) -> *mut Self {
        let ret = Box::into_raw(Box::new(Self {
            generation: 0.into(),
            inner: Vec::from_iter((0..genvec.arena_cap).map(|i| Inner {
                epoch: 0.into(),
                next: (i + 1).into(),
                refs: 0.into(),
                item: MaybeUninit::uninit().into(),
            })),
            free_cnt: genvec.arena_cap.into(),
            free_head: 0.into(),
            next: AtomicPtr::new(std::ptr::null_mut()),
        }));
        let mut lock = genvec.arena_init_lock.lock().unwrap();
        *lock += 1;
        let head = genvec.arena.load(Ordering::Acquire);
        if head.is_null() {
            // Safety: we just created ret
            unsafe { (*ret).next.store(ret, Ordering::Release) };
            genvec.arena.store(ret, Ordering::Release);
        } else {
            // Safety: we can take a shared reference to an arena as no exclusive references will
            // ever be made.
            let head = unsafe { &*head };

            // this must be acquire in case the release ordering set that made head.next non-null
            // hasn't persisted yet
            let next = head.next.load(Ordering::Acquire);

            // Safety: we just created ret
            //
            // This must be release ordering so other threads are sure to not dereference ret.next
            // as a null pointer
            unsafe { (*ret).next.store(next, Ordering::Release) };

            // it's fine if this updates later since it would just skip the new node for a while
            head.next.store(ret, Ordering::Relaxed);
            genvec.arena.store(ret, Ordering::Release);
        }
        ret
    }
}

struct Inner<T> {
    /// generation that this alloc was initialized in. Must be atomic since even though its only
    /// written to under Mutex, it can be read by an old weak pointer.
    epoch: AtomicUsize,

    /// index of next in free list. We let these be `UnsafeCell` since any read or write must have
    /// the lock on the arena. We use `UnsafeCell` over `Cell` since the mutex is somewhere else
    /// and so accesses should be marked `unsafe`.
    next: UnsafeCell<usize>,

    /// Number of strong references to this cell. If this is greater than zero, then there may
    /// exist pointers to the item. Note that it doesn't necessarily imply there exists strong
    /// pointers. A weak pointer from before could be attempting to upgrade. We'll use the high bit
    /// to store the drop flag. If the flag is set, then decrementing to zero (excluding high bit)
    /// requires dropping the inner item. There is a brief moment after decrementing to zero and
    /// before locking in the drop where another thread can promote a weak pointer, in which case
    /// the allocation is not dropped.
    refs: AtomicUsize,

    item: UnsafeCell<MaybeUninit<T>>,
}
unsafe impl<T: Sync> Sync for Inner<T> {}

// /// lock for semantics
// #[derive(Default)]
// struct WriteLock {
//     lock: AtomicBool,
// }
//
// impl WriteLock {
//     #[inline(always)]
//     fn try_lock(&self) -> Option<WriteLockGuard> {
//         if self.lock.compare_exchange_weak(false, true, Ordering::AcqRel, Ordering::Relaxed).is_ok() {
//             Some(WriteLockGuard { lock: &self.lock })
//         } else {
//             None
//         }
//     }
// }
//
// struct WriteLockGuard<'a> {
//     lock: &'a AtomicBool
// }
//
// impl Drop for WriteLockGuard<'_> {
//     #[inline(always)]
//     fn drop(&mut self) {
//         debug_assert_eq!(self.lock.load(Ordering::Relaxed), true);
//         self.lock.store(false, Ordering::Release);
//     }
// }

/// Strong reference to an item
pub struct Ref<'a, T> {
    index: usize,
    source: &'a ArenaNode<T>,
}

/// Weak reference to an item. Call [`Self::upgrade`] to access the item
pub struct Weak<'a, T> {
    index: usize,
    epoch: usize,

    source: &'a ArenaNode<T>,
}

impl<'a, T> Weak<'a, T> {
    /// Attempt to upgrade to a [`Ref`]. Will return [`None`] if the referenced item has been
    /// dropped
    #[inline]
    pub fn upgrade(self) -> Option<Ref<'a, T>> {
        self.source.try_inc_ref(self.index).ok()?;

        let inner = &self.source.inner[self.index];
        if inner.epoch.load(Ordering::Acquire) != self.epoch {
            self.source.dec_ref(self.index, Ordering::Relaxed);
            return None;
        };
        Some(Ref {
            index: self.index,
            source: self.source,
        })
    }
}

impl<'a, T> Clone for Weak<'a, T> {
    fn clone(&self) -> Self {
        Self {
            index: self.index,
            epoch: self.epoch,
            source: self.source,
        }
    }
}

impl<'a, T> Copy for Weak<'a, T> {}

impl<T> GenVec<T> {
    /// Create a new `GenVec` with `arenas` of seperate arenas that can each hold `capacity` objects.
    ///
    /// Each allocation or deallocation locks an arena, so more arenas should lead to less lock
    /// contention, however, more arenas can mean more time spent traversing the arena list.
    pub fn new(capacity: usize, arenas: usize) -> Self {
        let ret = Self {
            arena_init_lock: 0.into(),
            arena: AtomicPtr::new(std::ptr::null_mut()),
            arena_cap: capacity,
        };
        for _ in 0..arenas {
            ArenaNode::new_in(&ret);
        }
        ret
    }

    /// insert an object into the GenVec.
    ///
    /// if the allocation fails due to lack of capacity, a new arena will be created.
    #[must_use]
    pub fn alloc(&self, item: T) -> Ref<T> {
        let mut orig_head = self.arena.load(Ordering::Acquire);
        let mut head = orig_head;
        loop {
            'attempt: {
                // Safety: linked list is valid
                let head = unsafe { &*head };

                // do an initial check to discard full arenas
                if head.free_cnt.load(Ordering::Relaxed) == 0 {
                    break 'attempt;
                }
                let mut lock = match head.free_head.try_lock() {
                    Ok(lock) => lock,
                    Err(std::sync::TryLockError::Poisoned(e)) => {
                        panic!("thread panicked: {e}");
                    }
                    Err(std::sync::TryLockError::WouldBlock) => break 'attempt,
                };
                if head.free_cnt.load(Ordering::Acquire) == 0 {
                    break 'attempt;
                }
                head.free_cnt.fetch_sub(1, Ordering::Relaxed);
                let idx = *lock;
                let slot = &head.inner[idx];

                // Safety: this slot is in the free list and is therefore free and has no readers
                // or writers to non-atomic fields.
                unsafe {
                    (*slot.item.get()).write(item);
                    *lock = slot.next.get().read();
                    let generation = head.generation.get();
                    *generation = (*generation).wrapping_add(1);
                    slot.epoch.store(generation.read(), Ordering::Relaxed);
                }
                slot.refs
                    .fetch_add(ArenaNode::<T>::DROP_BIT | 1, Ordering::Release);
                return Ref {
                    index: idx,
                    source: head,
                };
            };

            // Safety: linked list is valid
            let next = unsafe { (*head).next.load(Ordering::Acquire) };
            if orig_head == next {
                // another thread can still win a race here, and theoretically even fill it
                // entirely before the next loop.
                head = ArenaNode::new_in(self);
                orig_head = head;
            } else {
                head = next;
            }
        }
    }

    /// gets the maximum capacity
    #[inline]
    pub fn capacity(&self) -> usize {
        unimplemented!();
    }

    /// gets the number of free slots, loaded with Acquire ordering.
    #[inline]
    pub fn free(&self) -> usize {
        unimplemented!();
    }

    /// gets the number of objects in the GenVec, loaded with Acquire ordering.
    #[inline]
    pub fn allocated(&self) -> usize {
        unimplemented!();
    }
}

impl<T> Deref for Ref<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // Safety: there are no mutable references to self.source and there will never be a mutable
        // reference to data. Since this is a strong reference, the data is initialized.
        unsafe { (*self.source.inner[self.index].item.get()).assume_init_ref() }
    }
}

impl<T> Clone for Ref<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        // this can be relaxed ordering since we know the ref count is at least one on this thread.
        //
        // FIXME: verify this claim
        // Dropping a ref, if it's the last reference, is (all together) AcqRel, so there is no
        // risk of another thread not seeing something.
        //
        // Coming from a strong reference also allows us to forgo try_inc_ref
        self.source.inner[self.index]
            .refs
            .fetch_add(1, Ordering::Relaxed);
        Self {
            index: self.index,
            source: self.source,
        }
    }
}

impl<T> Drop for Ref<'_, T> {
    fn drop(&mut self) {
        self.source.dec_ref(self.index, Ordering::Release);
    }
}

impl<'a, T> Ref<'a, T> {
    /// Create a weak reference
    pub fn weak(&'_ self) -> Weak<'a, T> {
        // relaxed since the existence of a strong reference means that epoch won't be changed
        let epoch = self.source.inner[self.index].epoch.load(Ordering::Relaxed);
        Weak {
            index: self.index,
            epoch,
            source: self.source,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn allocate_single() {
        let allocator = GenVec::new(1, 1);
        let item = allocator.alloc(42);
        assert_eq!(*item, 42)
    }

    #[test]
    fn make_weak_reference() {
        let allocator = GenVec::new(1, 1);
        let item = allocator.alloc(42);
        let weak = item.weak();
        assert_eq!(*weak.upgrade().unwrap(), 42);
        std::mem::drop(item)
    }

    #[test]
    fn no_strong_references_invalidates_weak_references() {
        let allocator = GenVec::new(1, 1);
        let item = allocator.alloc(42);
        let weak = item.weak();
        std::mem::drop(item);
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn strong_references_keep_alive() {
        let allocator = GenVec::new(1, 1);
        let item = allocator.alloc(42);
        let weak = item.weak();
        let item_dup = item.clone();
        std::mem::drop(item);
        assert_eq!(*item_dup, 42);
        assert_eq!(*weak.upgrade().unwrap(), 42);
        std::mem::drop(item_dup);
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn dropping_reference_frees_space() {
        let allocator = GenVec::new(1, 1);
        let item = allocator.alloc(42);

        let _ = allocator.alloc(33);

        std::mem::drop(item);

        let item = allocator.alloc(23);
        assert_eq!(*item, 23)
    }

    #[test]
    fn weak_reference_fails_on_replacement() {
        let allocator = GenVec::new(1, 1);
        let item = allocator.alloc(42);
        let weak = item.weak();
        std::mem::drop(item);
        let new_item = allocator.alloc(33);
        assert!(weak.upgrade().is_none());
        std::mem::drop(new_item)
    }

    #[test]
    #[ignore = "expensive"]
    fn fuzz() {
        let size = 1 << 20;

        fn task(
            allocator: &GenVec<usize>,
            thread_id: usize,
            thread_cnt: usize,
            size: usize,
            epoch: &AtomicUsize,
        ) {
            let mut rand = fastrand::Rng::with_seed(12345 + thread_id as u64);
            let mut refs = Vec::from_iter(
                (0..(2 * size / thread_cnt))
                    .map(|_| allocator.alloc(epoch.fetch_add(1, Ordering::Relaxed))),
            );
            let mut weaks = Vec::with_capacity(3 * size);
            let mut cnt = 100_000;
            while cnt > 0 {
                cnt -= 1;
                match rand.u8(0..=7) {
                    0 if refs.len() > 0 => {
                        let _ = refs.swap_remove(rand.usize(0..refs.len()));
                    }
                    1 => (),
                    2..=3 if weaks.len() > 0 => {
                        let (weak, expected): (Weak<usize>, _) =
                            weaks.swap_remove(rand.usize(0..weaks.len()));
                        if let Some(tref) = weak.upgrade() {
                            assert_eq!(*tref, expected);
                        }
                    }
                    4..=5 if weaks.len() < 3 * size && refs.len() > 0 => {
                        let tref = &refs[rand.usize(0..refs.len())];
                        weaks.push((tref.weak(), **tref));
                    }
                    6 if refs.len() < size => {
                        let res = allocator.alloc(epoch.fetch_add(1, Ordering::Relaxed));
                        refs.push(res);
                    }
                    7 if refs.len() < size && refs.len() > 0 => {
                        let tref = &refs[rand.usize(0..refs.len())];
                        refs.push(tref.clone());
                    }
                    8.. => unreachable!(),
                    _ => {
                        cnt += 1;
                    }
                };
            }
        }

        let epoch = AtomicUsize::new(0);
        let tcnt = std::thread::available_parallelism().map_or(4, |c| {
            <usize as From<std::num::NonZeroUsize>>::from(c).max(4)
        });
        // let tcnt = 8;
        let allocator = GenVec::new(size, tcnt / 2);
        let tids = Vec::from_iter(0..tcnt);
        std::thread::scope(|s| {
            for t in &tids {
                s.spawn(|| task(&allocator, *t, tcnt, size, &epoch));
            }
        });
    }
}
