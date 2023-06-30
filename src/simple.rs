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

    /// number of free slots
    free: Cell<usize>,

    /// number of total slots. Can only be changed with an exclusive reference due to the
    /// possibility of dangling pointers. Consider the following sequence:
    ///
    /// 1. GenVec is full
    /// 2. [`Deref`] is called on a handle, and a reference is created to the interior item
    /// 3. A new item is added, and `data` is reallocated
    /// 4. reference created in step 2 is now invalid
    capacity: usize,


    /// underlying data of the GenVec.
    data: Vec<UnsafeCell<Option<Inner<T>>>>
}

struct Inner<T> {
    epoch: usize,

    /// Number of strong references to this cell. If this is greater than zero, then there may
    /// exist pointers to the item.
    ///
    /// This is a Cell because it must be able to be mutated while references exist to the item -
    /// and thus creating a mutable reference to all of Inner would be illegal
    refs: Cell<usize>,

    item: T,
}

/// Strong reference to an item
pub struct GenRef<'a, T> {
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
    pub fn upgrade(self) -> Option<GenRef<'a, T>> {
        let cell = self.source.data.get(self.index)?;

        // Safety: while there may be other shared references to the item, there are no
        // mutable aliases (unless T contains an UnsafeCell, but that's ok too).
        let inner = unsafe { &*cell.get() }.as_ref()?;
        if inner.epoch != self.epoch { return None }

        inner.refs.set(inner.refs.get() + 1);
        Some(GenRef { index: self.index, source: self.source })
    }
}

impl<T> GenVec<T> {
    /// create a new [`GenVec`] with the capacity to hold `capacity` objects
    #[inline]
    pub fn new(capacity: usize) -> Self {
        Self {
            generation: 1.into(),
            free: capacity.into(),
            capacity,
            data: Vec::from_iter(std::iter::repeat_with(|| None.into()).take(capacity))
        }
    }

    /// insert an object into the GenVec.
    ///
    /// if the allocation fails due to lack of capacity, the item will be returned in the `Err()`
    /// variant
    #[must_use]
    pub fn alloc(&self, item: T) -> Result<GenRef<T>, T>{
        let position;

        if self.free.get() > 0 {
            position = self.data.iter().position(|x| {
                // Safety: while there may be other shared references to the item, there are no
                // mutable aliases (unless T contains an UnsafeCell, but that's ok too).
                unsafe { &*x.get() }.is_none()
            }).expect("genvec should have free slots, but none were found");
        } else {
            return Err(item)
        }

        let inner = Inner { epoch: self.generation.get(), refs: 1.into(), item };
        self.generation.set(self.generation.get() + 1);

        // Safety: the item in the slot will have no references to the inner type
        unsafe { *self.data[position].get() = Some(inner) };

        self.free.set(self.free.get() - 1);

        Ok(GenRef { index: position, source: self })
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

impl<T> Deref for GenRef<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // Safety: there are no mutable references to self.source and there will never be a mutable
        // reference to data
        let cell = unsafe {&* self.source.data[self.index].get()};
        &cell.as_ref().expect("strong references should imply cell is occupied").item
    }
}

impl<T> Clone for GenRef<'_, T> {
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

impl<T> Drop for GenRef<'_, T>  {
    fn drop(&mut self) {
        // Safety: there are no mutable references to self. source and there will never be a mutable
        // reference to data.
        let cell = unsafe {&* self.source.data[self.index].get()};

        let refs = &cell.as_ref().expect("strong references should imply cell is occupied").refs;
        refs.set(refs.get() - 1);

        if refs.get() == 0 {
            // Safety: this is the last reference to the cell, so we can get a mutable reference
            let cell = unsafe {&mut *self.source.data[self.index].get()};
            *cell = None;

            self.source.free.set(self.source.free.get() + 1)
        }
    }
}

impl<'a, T> GenRef<'a, T> {
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
}
