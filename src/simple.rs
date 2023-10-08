use std::mem::MaybeUninit;
use std::{cell::{Cell, UnsafeCell}, ops::Deref};

/// Simple allocator for many identical objects with unknown lifetimes
///
/// This is a potential alternative for [`Rc`][std::rc::Rc] in cases where you have many objects of
/// the same type and you don't want weak pointers to cause a memory leak. unlike
/// [`Rc`][std::rc::Rc], [`GenVec`] allows the memory of objects dropped after their last strong
/// pointer to be reused even while weak pointers exist.
pub struct GenVec<T> {
    /// current generation of the allocator
    generation: Cell<usize>,


    /// number of total slots. Can only be changed with an exclusive reference due to the
    /// possibility of dangling pointers. Consider the following sequence:
    ///
    /// 1. GenVec is full
    /// 2. [`Deref`] is called on a handle, and a reference is created to the interior item
    /// 3. A new item is added, and `data` is reallocated
    /// 4. reference created in step 2 is now invalid
    capacity: usize,

    /// number of free slots
    free: Cell<usize>,
    /// index of head of free list
    free_head: Cell<usize>,

    data: Vec<Inner<T>>
}

struct Inner<T> {
    epoch: Cell<usize>,

    next: Cell<usize>,

    /// Number of strong references to this cell. I may change this to mimic refcell semantics.
    refs: Cell<usize>,

    /// stored item
    item: UnsafeCell<MaybeUninit<T>>,
}

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
    /// Attempt to upgrade to a [`GenRef`]. Will return [`None`] if the referenced item has been
    /// dropped
    pub fn upgrade(self) -> Option<Ref<'a, T>> {
        let inner = self.source.data.get(self.index)?;

        if inner.epoch.get() != self.epoch { return None }
        if inner.refs.get() == 0 { return None }

        inner.refs.set(inner.refs.get() + 1);
        Some(Ref { index: self.index, source: self.source })
    }
}

impl<T> GenVec<T> {
    /// create a new [`GenVec`] with the capacity to hold `capacity` objects
    #[inline]
    pub fn new(capacity: usize) -> Self {
        Self {
            generation: 1.into(),
            capacity,
            free: capacity.into(),
            free_head: 0.into(),
            data: Vec::from_iter(
                (0..capacity).map(|i| Inner { next: (i + 1).into(), epoch: 0.into(), refs:
                    0.into(), item: MaybeUninit::uninit().into() })
            )
        }
    }

    /// insert an object into the GenVec.
    ///
    /// if the allocation fails due to lack of capacity, the item will be returned in the `Err()`
    /// variant
    #[must_use]
    pub fn alloc(&self, item: T) -> Result<Ref<T>, T>{
        // this should be fine for all non-pathological programs
        let gen = self.generation.get().wrapping_add(1);

        let free = self.free.get();
        if free == 0 {
            return Err(item)
        }

        // We don't need to update (can just leave junk data in) free_ptr and free_ind since we
        // always just take from the end and we never check residency (that's done by the
        // Option<Inner>). It is sufficient to simply decrement the len.
        self.free.set(free - 1);

        let pos = self.free_head.get();
        let inner = &self.data[pos];
        self.free_head.swap(&inner.next);
        inner.epoch.set(gen);
        inner.refs.set(1);

        self.generation.set(gen);

        // Safety: this is the only pointer to this free cell
        unsafe { (&mut *inner.item.get()).write(item) };

        Ok(Ref { index: pos, source: self })
    }

    /// gets the maximum capacity
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// gets the number of free slots
    #[inline]
    pub fn free(&self) -> usize {
        self.free.get()
    }
    
    /// gets the number of objects in the GenVec
    #[inline]
    pub fn allocated(&self) -> usize {
        self.capacity - self.free.get()
    }
}

impl<T> Deref for Ref<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // Safety: there are no mutable references to self.source and there will never be a mutable
        // reference to data, and strong references refer to initialized objects.
        unsafe {(&*self.source.data[self.index].item.get()).assume_init_ref()}
    }
}

impl<T> Clone for Ref<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        let refs = &self.source.data[self.index].refs;
        refs.set(refs.get() + 1);
        Self {
            index: self.index,
            source: self.source
        }
    }
}

impl<T> Drop for Ref<'_, T>  {
    fn drop(&mut self) {
        let cell = &self.source.data[self.index];
        let refs = &cell.refs;
        refs.set(refs.get() - 1);

        if refs.get() == 0 {
            // Safety: this is the last reference to the cell, so we can get a mutable reference
            // and strong references imply the item is initialized
            unsafe { (&mut *cell.item.get()).assume_init_drop()};

            let free = self.source.free.get();
            self.source.free.set(free + 1);
            cell.next.set(self.source.free_head.get());
            self.source.free_head.set(self.index);
        }
    }
}

impl<'a, T> Ref<'a, T> {
    /// Create a weak reference
    pub fn weak(&'_ self) -> Weak<'a, T> {
        // Safety: there are no mutable references to the data and we do not leak the reference
        let epoch = self.source.data[self.index].epoch.get();
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
    // #[ignore = "temp"]
    fn fuzz() {
        let size = 1 << 8;
        let iter = 10000;

        let allocator = GenVec::new(size);
        let mut epoch = 0;
        let mut rand = fastrand::Rng::with_seed(12345);
        let mut refs = Vec::from_iter((0..(size / 2)).map(|_| allocator.alloc({epoch += 1; epoch}).unwrap()));
        let mut weaks = Vec::with_capacity(3*size);
        let mut remain = iter;
        let mut cnt = 0;
        while remain > 0 {
            remain -= 1;
            cnt += 1;
            if cnt > 2 * iter {
                panic!("took too long")
            }
            match rand.u8(0..=7) {
                0..=1 if refs.len() > 0 => {
                    let _ = refs.swap_remove(rand.usize(0..refs.len()));
                },
                // 1 => (),
                2..=3 if weaks.len() > 0 => {
                    let (weak, expected): (Weak<usize>, _) = weaks.swap_remove(rand.usize(0..weaks.len()));
                    if let Some(tref) = weak.upgrade() {
                        assert_eq!(*tref, expected);
                    }
                },
                4..=5 if weaks.len() < 3 * size && refs.len() > 0 => {
                    let tref = &refs[rand.usize(0..refs.len())];
                    weaks.push((tref.weak(), **tref));
                },
                6 if refs.len() < size => {
                    let res = allocator.alloc({epoch +=1; epoch}).unwrap();
                    refs.push(res);
                },
                7 if refs.len() < size => {
                    let tref = &refs[rand.usize(0..refs.len())];
                    refs.push(tref.clone());
                },
                8.. => unreachable!(),
                _ => {
                    remain += 1;
                }
            };
        }
    }
}
