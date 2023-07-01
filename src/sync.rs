#![allow(dead_code)]
use std::{sync::{atomic::{AtomicUsize, AtomicPtr, Ordering, AtomicBool}, Mutex, RwLock}, mem, ops::Deref, pin::Pin, iter::repeat_with, ptr::{null, null_mut}};

pub struct GenVecSync<T> {
    generation: AtomicUsize,
    arena: AtomicPtr<Arena<T>>,
    construction: AtomicBool,

    stale_arenas: Mutex<Vec<Option<Pin<Box<Arena<T>>>>>>
}

struct Arena<T> {
    cap: usize,
    count: AtomicUsize,
    stale: AtomicBool,
    allocs: Box<[Inner<T>]>
}

impl<T> GenVecSync<T> {
    pub fn new() -> Self {
        Self::new_with_capacity(64)
    }

    pub fn new_with_capacity(capacity: usize) -> Self {
        let arena = Arena {
            cap: capacity,
            count: 0.into(),
            stale: false.into(),
            allocs: Vec::from_iter(repeat_with(|| Inner {
                epoch: 0.into(),
                refs: 0.into(),
                item: null_mut::<T>().into(),
            }).take(capacity)).into_boxed_slice()
        };
        let arena = Box::leak(Box::new(arena)) as *mut Arena<T>;
        Self {
            generation: 1.into(),
            arena: arena.into(),
            construction: false.into(),
            stale_arenas: Mutex::new(Vec::new()),
        }
    }

    fn expand_arena(&self, amt: usize) {

    }


    pub fn alloc(&self, item: T) -> GenRef<T> {
        todo!()
    }
}

pub struct GenRef<'a, T> {
    arena: &'a Arena<T>,
    index: usize,
}

impl<T> Deref for GenRef<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        todo!()
    }
}




struct Inner<T> {
    epoch: AtomicUsize,

    /// Number of strong references to this cell. If this is greater than zero, then there may
    /// exist pointers to the item.
    refs: AtomicUsize,

    item: AtomicPtr<T>,
}

impl<T> Inner<T> {
    fn new(epoch: usize, item: T) -> Self {
        Inner {
            epoch: epoch.into(),
            refs: 1.into(),
            item: (Box::leak(Box::new(item)) as *mut T).into()
        }
    }
}

#[test]
fn test() {
}
