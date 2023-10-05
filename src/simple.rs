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

    /// number of free slots, this is different from `free_slots.len()` since that does not change
    free: Cell<usize>,

    /// len should always == `capacity`
    free_ptr: Vec<Cell<usize>>,
    free_ind: Vec<Cell<usize>>,

    /// underlying data of the GenVec.
    data: Vec<UnsafeCell<Option<Inner<T>>>>
}

struct Inner<T> {
    epoch: usize,

    /// Number of strong references to this cell. I may change this to mimic refcell semantics.
    refs: Cell<usize>,

    /// stored item, may change to `UnsafeCell` if I want to make this a RefCell.
    item: T,
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
        let cell = self.source.data.get(self.index)?;

        // Safety: while there may be other shared references to the item, there are no
        // mutable aliases (unless T contains an UnsafeCell, but that's ok too).
        // 
        // if this were multithreaded, there would be a race condition with the ref increment
        let inner = unsafe { &*cell.get() }.as_ref()?;
        if inner.epoch != self.epoch { return None }

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
            // TODO: try benchmarking reversing this iterator
            free_ptr: Vec::from_iter((0..capacity).map(|x| x.into())),
            free_ind: Vec::from_iter((0..capacity).map(|x| x.into())),
            data: Vec::from_iter(std::iter::repeat_with(|| None.into()).take(capacity))
        }
    }

    /// insert an object into the GenVec.
    ///
    /// if the allocation fails due to lack of capacity, the item will be returned in the `Err()`
    /// variant
    #[must_use]
    pub fn alloc(&self, item: T) -> Result<Ref<T>, T>{
        let position;

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
        position = self.free_ind[free - 1].get();

        // Safety: we can take a shared reference to the slot
        debug_assert!(unsafe {&*self.data[position].get()}.is_none(), "Free for slot {position} was lost");

        let inner = Inner { epoch: gen, refs: 1.into(), item };
        self.generation.set(gen);

        // Safety: the item in the slot will have no references to the inner type
        unsafe { *self.data[position].get() = Some(inner) };

        Ok(Ref { index: position, source: self })
    }

    /// change the capacity of the GenVec
    #[inline]
    pub fn resize(&mut self, new_size: usize) {
        self.data.resize_with(new_size, || None.into());
        self.capacity = new_size;
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
        // reference to data
        let cell = unsafe {&* self.source.data[self.index].get()};
        &cell.as_ref().expect("strong references should imply cell is occupied").item
    }
}

impl<T> Clone for Ref<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        // Safety: there are no mutable references to self.source and there will never be a mutable
        // reference to data. We also keep no references to Inner, so modifying it is ok.
        let cell = unsafe {&* self.source.data[self.index].get()};
        let refs = &cell.as_ref().expect("strong references should imply cell is occupied").refs;
        refs.set(refs.get() + 1);
        Self {
            index: self.index,
            source: self.source
        }
    }
}

impl<T> Drop for Ref<'_, T>  {
    fn drop(&mut self) {
        // Safety: there are no mutable references to self. source and there will never be a mutable
        // reference to data.
        let cell = unsafe {&* self.source.data[self.index].get()};

        let refs = &cell.as_ref().expect("strong references should imply cell is occupied").refs;
        refs.set(refs.get() - 1);

        if refs.get() == 0 {
            // Safety: this is the last reference to the cell, so we can get a mutable reference
            let cell = self.source.data[self.index].get();
            unsafe { *cell = None };

            let free = self.source.free.get();
            self.source.free_ind[free].set(self.index);
            self.source.free_ptr[self.index].set(free);
            self.source.free.set(free + 1);
        }
    }
}

impl<'a, T> Ref<'a, T> {
    /// Create a weak reference
    pub fn weak(&'_ self) -> Weak<'a, T> {
        // Safety: there are no mutable references to the data and we do not leak the reference
        let cell = unsafe {&* self.source.data[self.index].get()};
        let epoch = cell.as_ref().expect("strong references should imply cell is occupied").epoch;
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
        let mut epoch = 0;
        let mut rand = fastrand::Rng::with_seed(12345);
        let allocator = GenVec::new(size);
        let mut allocations = Vec::from_iter((0..size).map(|_| allocator.alloc({ epoch += 1; epoch})));
        for _ in 0..200000 {
            if allocations.len() == size || (allocations.len() > 0 && rand.bool()) {
                let _ = allocations.swap_remove(rand.usize(0..allocations.len()));
            } else {
                allocations.push(allocator.alloc({epoch += 1; epoch}));
            }
        }
    }
}
