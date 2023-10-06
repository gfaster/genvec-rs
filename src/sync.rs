#![allow(dead_code)]
use std::{sync::atomic::{AtomicUsize, Ordering, fence}, mem::MaybeUninit, ops::Deref, cell::UnsafeCell};


/// Direct Access List that is Sync
struct Dal {
    size: AtomicUsize,
    lptr: Vec<AtomicUsize>,
    lind: Vec<AtomicUsize>,
}

/// Simple allocator for many identical objects with unknown lifetimes
///
/// This is a potential alternative for [`Rc`][std::rc::Rc] in cases where you have many objects of
/// the same type and you don't want weak pointers to cause a memory leak. unlike
/// [`Rc`][std::rc::Rc], [`GenVec`] allows the memory of objects dropped after their last strong
/// pointer to be reused even while weak pointers exist.
pub struct GenVec<T> {
    /// current generation of the allocator
    generation: AtomicUsize,

    /// number of free slots
    free: AtomicUsize,

    /// first free slot index. Not having a tail node has a few benefits and drawbacks. It means
    /// that we need fewer operations to allocate or free, but it also means that frees will
    /// contend with allocations.
    free_head: AtomicUsize,

    /// underlying data of the GenVec.
    data: Vec<Inner<T>>
}

struct Inner<T> {
    epoch: AtomicUsize,

    /// index of next in free list
    next: AtomicUsize,

    /// Number of strong references to this cell. If this is greater than zero, then there may
    /// exist pointers to the item.
    refs: AtomicUsize,

    item: UnsafeCell<MaybeUninit<T>>,
}

unsafe impl<T: Sync> Sync for Inner<T> {}

/// Strong reference to an item
pub struct Ref<'a, T> {
    index: usize,
    source: &'a GenVec<T>,
}

/// Weak reference to an item. Call [`Self::upgrade()`] to access the item
#[derive(Clone, Copy)]
pub struct Weak<'a, T> {
    index: usize,
    epoch: usize,
    source: &'a GenVec<T>,
}

impl<'a, T> Weak<'a, T> {
    #[inline]
    /// Attempt to upgrade to a [`Ref`]. Will return [`None`] if the referenced item has been
    /// dropped
    pub fn upgrade(self) -> Option<Ref<'a, T>> {
        // I need to be careful to avoid an ABA bug here. 
        //
        // T1 upgrade | T2 drop last Ref
        // chk epoch  | 
        // chk Ref    | 
        //            | dec Ref
        //            | chk Ref
        //            | unset epoch
        // inc Ref    | drop
        // chk epoch  | alloc
        //            | set epoch
        //            | inc Ref
        let inner = &self.source.data[self.index];
        if inner.epoch.load(Ordering::Acquire) != self.epoch {
            // something else here
            return None;
        };
        if inner.refs.fetch_add(1, Ordering::AcqRel) == 0 {
            inner.refs.fetch_sub(1, Ordering::Relaxed);
            // has been dropped
            return None;
        };
        if inner.epoch.load(Ordering::Acquire) != self.epoch {
            // something else here - we check again to make sure nothing happened in between the
            // last two checks. 
            inner.refs.fetch_sub(1, Ordering::Relaxed);
            return None;
        };
        // we've effectively locked the slot at this point
        // FIXME: no we definitely haven't

        Some(
            Ref { index: self.index, source: self.source }
        )
    }
}

impl<T> GenVec<T> {
    /// create a new [`GenVec`] with the capacity to hold `capacity` objects
    pub fn new(capacity: usize) -> Self {
        Self {
            generation: 0.into(),

            free: capacity.into(),
            free_head: 0.into(),

            data: Vec::from_iter((0..capacity).map(|i| Inner {
                epoch: 0.into(),
                refs: 0.into(),
                next: (i + 1).into(),
                item: MaybeUninit::uninit().into(),
            }).take(capacity))
        }
    }


    /// insert an object into the GenVec.
    ///
    /// if the allocation fails due to lack of capacity, the item will be returned in the `Err()`
    /// variant
    #[must_use]
    pub fn alloc(&self, item: T) -> Result<Ref<T>, T>{
        let Ok(_free) = self.free.fetch_update(Ordering::Acquire, Ordering::Relaxed, |f| f.checked_sub(1)) else {
            return Err(item);
        };

        let idx = {
            loop { 
                let head = self.free_head.load(Ordering::Acquire);
                let next = self.data[head].next.load(Ordering::Relaxed);
                let res = self.free_head.compare_exchange(head, next, Ordering::Release, Ordering::Relaxed);
                match res {
                    Ok(_) => break head,
                    Err(_) => continue,
                }
            }
        };
        
        let epoch = self.generation.fetch_add(1, Ordering::Relaxed);

        // we make these seqcst because we'll rely on epoch being updated before refs are made
        // nonzero.
        self.data[idx].epoch.store(epoch, Ordering::SeqCst);
        self.data[idx].refs.store(1, Ordering::SeqCst);

        // Safety: the item in the slot was free
        unsafe { (*self.data[idx].item.get()).write(item) };

        Ok(Ref { index: idx, source: self })
    }

    /// gets the maximum capacity
    #[inline]
    pub fn capacity(&self) -> usize {
        self.data.len()
    }

    /// gets the number of free slots, loaded with Acquire ordering.
    #[inline]
    pub fn free(&self) -> usize {
        self.free.load(Ordering::Acquire)
    }
    
    /// gets the number of objects in the GenVec, loaded with Acquire ordering.
    #[inline]
    pub fn allocated(&self) -> usize {
        self.data.len() - self.free.load(Ordering::Acquire)
    }
}

impl<T> Deref for Ref<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // Safety: there are no mutable references to self.source and there will never be a mutable
        // reference to data. Since this is a strong reference, the data is initialized.
        unsafe {(*self.source.data[self.index].item.get()).assume_init_ref()}
    }
}

impl<T> Clone for Ref<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        // this can be relaxed ordering since we know the ref count is at least one on this thread.
        self.source.data[self.index].refs.fetch_add(1, Ordering::Relaxed);
        Self {
            index: self.index,
            source: self.source
        }
    }
}

impl<T> Drop for Ref<'_, T>  {
    fn drop(&mut self) {
        
        let slot = &self.source.data[self.index];

        if slot.refs.fetch_sub(1, Ordering::Relaxed) == 1 {
            // last ref

            // Safety: this is the last reference to this slot, and the data was initialized
            unsafe { (*slot.item.get()).assume_init_drop() }

            // I'm not certain this is needed, but there is no data dependence between the drop and
            // re-adding self to the free list. If all memory accesses aren't persisted, there
            // could be a race condition in the partially-freed slot.
            fence(Ordering::AcqRel);

            let _ = self.source.free_head.fetch_update(Ordering::Release, Ordering::Relaxed, |f| {
                slot.next.store(f, Ordering::Release);
                Some(self.index)
            });

            self.source.free.fetch_add(1, Ordering::Release);
        }
    }
}

impl<'a, T> Ref<'a, T> {
    /// Create a weak reference
    pub fn weak(&'_ self) -> Weak<'a, T> {
        // relaxed since the existence of a strong reference means that epoch won't be changed
        let epoch = self.source.data[self.index].epoch.load(Ordering::Relaxed);
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
        let allocator = GenVec::new(1);
        let item = allocator.alloc(42).unwrap();
        assert_eq!(*item, 42)
    }

    #[test]
    fn make_weak_reference() {
        let allocator = GenVec::new(1);
        let item = allocator.alloc(42).unwrap();
        let weak = item.weak();
        assert_eq!(*weak.upgrade().unwrap(), 42);
        std::mem::drop(item)
    }


    #[test]
    fn no_strong_references_invalidates_weak_references() {
        let allocator = GenVec::new(1);
        let item = allocator.alloc(42).unwrap();
        let weak = item.weak();
        std::mem::drop(item);
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn strong_references_keep_alive() {
        let allocator = GenVec::new(1);
        let item = allocator.alloc(42).unwrap();
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
        let allocator = GenVec::new(1);
        let item = allocator.alloc(42).unwrap();

        assert!(allocator.alloc(33).is_err());

        std::mem::drop(item);

        let item = allocator.alloc(23).unwrap();
        assert_eq!(*item, 23)
    }

    #[test]
    fn weak_reference_fails_on_replacement() {
        let allocator = GenVec::new(1);
        let item = allocator.alloc(42).unwrap();
        let weak = item.weak();
        std::mem::drop(item);
        let new_item = allocator.alloc(33).unwrap();
        assert!(weak.upgrade().is_none());
        std::mem::drop(new_item)
    }

    #[test]
    fn fuzz() {
        let size = 64;

        fn task(allocator: &GenVec<usize>, thread_id: usize, thread_cnt: usize, size: usize, epoch: &AtomicUsize) {
            let mut rand = fastrand::Rng::with_seed(12345 + thread_id as u64);
            let mut refs = Vec::from_iter((0..(2 * size / thread_cnt)).filter_map(|_| allocator.alloc( epoch.fetch_add(1, Ordering::Relaxed)).ok()));
            let mut weaks = Vec::with_capacity(3*size);
            let mut cnt = 10000;
            while cnt > 0 {
                cnt -= 1;
                match rand.u8(0..6) {
                    0 if refs.len() > 0 => {
                        let _ = refs.swap_remove(rand.usize(0..refs.len()));
                    },
                    1..=2 if weaks.len() > 0 => {
                        let (weak, expected): (Weak<usize>, _) = weaks.swap_remove(rand.usize(0..weaks.len()));
                        if let Some(tref) = weak.upgrade() {
                            assert_eq!(*tref, expected);
                        }
                    },
                    3..=4 if weaks.len() < 3 * size && refs.len() > 0 => {
                        let tref = &refs[rand.usize(0..refs.len())];
                        weaks.push((tref.weak(), **tref));
                    },
                    5 if refs.len() < size / 2 => {
                        let Ok(res) = allocator.alloc(epoch.fetch_add(1, Ordering::Relaxed)) else { continue };
                        refs.push(res);
                    },
                    6.. => unreachable!(),
                    _ => {
                        cnt += 1;
                    }
                };
            }
        }
        
        let epoch = AtomicUsize::new(0);
        let allocator = GenVec::new(size);
        // let tcnt = std::thread::available_parallelism().map_or(4, |c| <usize as From<std::num::NonZeroUsize>>::from(c).max(4));
        let tcnt = 8;
        let tids = Vec::from_iter(0..tcnt);
        std::thread::scope(|s| {
            for t in &tids {
                s.spawn(|| task(&allocator, *t, tcnt, size, &epoch));
            };
        });
    }
}
