#![allow(dead_code)]
use genvec::*;
use std::{
    ops::Deref,
    rc::Rc,
    sync::{Arc, Mutex},
};

macro_rules! inc {
    ($var:expr) => {{
        $var = $var.wrapping_add(1);
        $var
    }};
}

mod traits {
    use super::*;

    pub trait Allocator<'a, T, P>
    where
        P: RefCountPtr<'a, T>,
    {
        fn alloc(&'a self, val: T) -> Option<P>;
    }

    impl<'a, T> Allocator<'a, T, sync::Ref<'a, T>> for sync::GenVec<T> {
        fn alloc(&'a self, val: T) -> Option<sync::Ref<'a, T>> {
            Some(sync::GenVec::<T>::alloc(self, val))
        }
    }

    impl<'a, T, P> Allocator<'a, T, P> for ()
    where
        P: RefCountPtr<'a, T>,
    {
        fn alloc(&'a self, _val: T) -> Option<P> {
            None
        }
    }

    pub trait RefCountWeak<'alloc, T, S: RefCountPtr<'alloc, T, Weak = Self>>: Clone {
        fn upgrade(&self) -> Option<S>;
    }

    impl<'alloc, T> RefCountWeak<'alloc, T, Arc<T>> for std::sync::Weak<T> {
        fn upgrade(&self) -> Option<Arc<T>> {
            self.upgrade()
        }
    }

    impl<'alloc, T> RefCountWeak<'alloc, T, sync::Ref<'alloc, T>> for sync::Weak<'alloc, T> {
        fn upgrade(&self) -> Option<sync::Ref<'alloc, T>> {
            sync::Weak::upgrade(*self)
        }
    }

    pub trait RefCountPtr<'alloc, T>: Clone + Deref<Target = T> {
        type Weak: RefCountWeak<'alloc, T, Self>;

        fn make_weak(&self) -> Self::Weak;
        fn new<A>(allocator: &'alloc A, val: T) -> Option<Self>
        where
            A: Allocator<'alloc, T, Self>;
    }

    impl<'alloc, T> RefCountPtr<'alloc, T> for Arc<T> {
        type Weak = std::sync::Weak<T>;

        fn make_weak(&self) -> Self::Weak {
            Arc::downgrade(self)
        }

        fn new<A>(_allocator: &'alloc A, val: T) -> Option<Self>
        where
            A: Allocator<'alloc, T, Self>,
        {
            Some(Arc::new(val))
        }
    }

    impl<'alloc, T> RefCountPtr<'alloc, T> for sync::Ref<'alloc, T> {
        type Weak = sync::Weak<'alloc, T>;

        fn make_weak(&self) -> Self::Weak {
            Self::weak(self)
        }

        fn new<A>(allocator: &'alloc A, val: T) -> Option<Self>
        where
            A: Allocator<'alloc, T, Self>,
        {
            allocator.alloc(val)
        }
    }
}
use traits::*;

fn task<'a, A, T, R, W, F>(
    allocator: &'a A,
    rand: &mut fastrand::Rng,
    refs: (&mut Vec<R>, &mut Vec<R>),
    weaks: (&mut Vec<(W, T)>, &mut Vec<(W, T)>),
    size: usize,
    val: F,
) -> bool
where
    T: Clone,
    F: FnOnce() -> T,
    T: std::fmt::Debug + Eq,
    R: RefCountPtr<'a, T, Weak = W>,
    W: RefCountWeak<'a, T, R>,
    A: Allocator<'a, T, R>,
{
    let (refs, weaks) = match rand.u8(0..=3) {
        0 => (refs.0, weaks.0),
        1 => (refs.1, weaks.0),
        2 => (refs.1, weaks.1),
        3 => (refs.0, weaks.1),
        _ => unreachable!(),
    };
    match rand.u8(0..=7) {
        0 if refs.len() > 0 => {
            let _ = refs.swap_remove(rand.usize(0..refs.len()));
        }
        1 => (),
        2..=3 if weaks.len() > 0 => {
            let (weak, expected): (W, _) = weaks.swap_remove(rand.usize(0..weaks.len()));
            if let Some(tref) = weak.upgrade() {
                assert_eq!(*tref, expected);
            }
        }
        4..=5 if weaks.len() < 3 * size && refs.len() > 0 => {
            let tref = &refs[rand.usize(0..refs.len())];
            weaks.push((tref.make_weak(), (**tref).clone()));
        }
        6 if refs.len() < size => {
            let Some(res) = R::new(allocator, val()) else {
                return false;
            };
            refs.push(res);
        }
        7 if refs.len() < size && refs.len() > 0 => {
            let tref = &refs[rand.usize(0..refs.len())];
            refs.push(tref.clone());
        }
        8.. => unreachable!(),
        _ => {
            return false;
        }
    };
    return true;
}

fn fuzz() {
    type Item = Box<usize>;
    fn ttask<'a>(
        allocator: &'a sync::GenVec<Item>,
        avec: &[Mutex<(Vec<(sync::Weak<'a, Item>, Item)>, Vec<sync::Ref<'a, Item>>)>],
        thread_id: usize,
        size: usize,
    ) {
        let mut rand = fastrand::Rng::with_seed(12345 + thread_id as u64);
        let mut epoch = rand.usize(..);
        let mut cnt = ITER_CNT_SYNC;
        while cnt > 0 {
            let idx_1 = rand.usize(0..(avec.len() - 1));
            let idx_2 = rand.usize((idx_1 + 1)..avec.len());
            let mut lock_1 = match avec[idx_1].lock() {
                Ok(l) => l,
                Err(_) => panic!(),
            };
            let mut lock_2 = match avec[idx_2].lock() {
                Ok(l) => l,
                Err(_) => panic!(),
            };
            let (weaks_1, refs_1) = &mut *lock_1;
            let (weaks_2, refs_2) = &mut *lock_2;
            let res = task(allocator, &mut rand, (refs_1, refs_2), (weaks_1, weaks_2), size, || {
                inc!(epoch).into()
            });
            drop(lock_1);
            if res {
                cnt -= 1
            }
        }
    }

    // let tcnt = std::thread::available_parallelism().map_or(4, |c| <usize as From<std::num::NonZeroUsize>>::from(c).max(4));
    let tcnt = THREAD_CNT_SYNC;
    let allocator = sync::GenVec::new(SIZE_SYNC / tcnt, tcnt);
    let tids = Vec::from_iter(0..tcnt);
    let mut epoch: usize = 0;
    let arenas = Vec::from_iter((0..(tcnt * 16)).map(|_| {
        Mutex::new((
            Vec::with_capacity(3 * SIZE_SYNC),
            Vec::from_iter(
                (0..(2 * SIZE_SYNC / tcnt)).map(|_| allocator.alloc(inc!(epoch).into())),
            ),
        ))
    }));
    std::thread::scope(|s| {
        for t in &tids {
            s.spawn(|| ttask(&allocator, (&arenas).as_slice(), *t, SIZE_SYNC));
        }
    });
}

fn fuzz_alloc() {
    fn ttask(thread_id: usize, thread_cnt: usize, size: usize) {
        let mut rand = fastrand::Rng::with_seed(12345 + thread_id as u64);
        let mut epoch = rand.usize(..);
        let mut _refs = Vec::from_iter((0..(2 * size / thread_cnt)).map(|_| Arc::new(inc!(epoch))));
        // let mut weaks = Vec::with_capacity(3 * size);
        let mut cnt = ITER_CNT_SYNC;
        while cnt > 0 {
            // let res = task(&(), &mut rand, &mut refs, &mut weaks, size, || inc!(epoch));
            let res = true;
            if res {
                cnt -= 1;
            }
        }
    }

    // let tcnt = std::thread::available_parallelism().map_or(4, |c| <usize as From<std::num::NonZeroUsize>>::from(c).max(4));
    let tcnt = THREAD_CNT_SYNC;
    let tids = Vec::from_iter(0..tcnt);
    std::thread::scope(|s| {
        for t in &tids {
            s.spawn(|| ttask(*t, tcnt, SIZE_SYNC));
        }
    });
}

fn fuzz_single() {
    let allocator = simple::GenVec::new(SIZE_SINGLE);
    let mut epoch = 0;
    let mut rand = fastrand::Rng::with_seed(12345);
    let mut refs = Vec::from_iter((0..(SIZE_SINGLE / 2)).map(|_| {
        allocator
            .alloc({
                epoch += 1;
                epoch
            })
            .unwrap()
    }));
    let mut weaks = Vec::with_capacity(3 * SIZE_SINGLE);
    let mut remain = ITER_CNT_SINGLE;
    let mut cnt = 0;
    while remain > 0 {
        remain -= 1;
        cnt += 1;
        if cnt > 2 * ITER_CNT_SINGLE {
            panic!("took too long")
        }
        match rand.u8(0..=7) {
            0..=1 if refs.len() > 0 => {
                let _ = refs.swap_remove(rand.usize(0..refs.len()));
            }
            // 1 => (),
            2..=3 if weaks.len() > 0 => {
                let (weak, expected): (simple::Weak<usize>, _) =
                    weaks.swap_remove(rand.usize(0..weaks.len()));
                if let Some(tref) = weak.upgrade() {
                    assert_eq!(*tref, expected);
                }
            }
            4..=5 if weaks.len() < 3 * SIZE_SINGLE && refs.len() > 0 => {
                let tref = &refs[rand.usize(0..refs.len())];
                weaks.push((tref.weak(), **tref));
            }
            6 if refs.len() < SIZE_SINGLE => {
                let res = allocator
                    .alloc({
                        epoch += 1;
                        epoch
                    })
                    .unwrap();
                refs.push(res);
            }
            7 if refs.len() < SIZE_SINGLE && refs.len() > 0 => {
                let tref = &refs[rand.usize(0..refs.len())];
                refs.push(tref.clone());
            }
            8.. => unreachable!(),
            _ => {
                remain += 1;
            }
        };
    }
}

fn fuzz_single_alloc() {
    let mut epoch = 0;
    let mut rand = fastrand::Rng::with_seed(12345);
    let mut refs = Vec::from_iter((0..(SIZE_SINGLE / 2)).map(|_| {
        epoch += 1;
        Rc::new(epoch)
    }));
    let mut weaks = Vec::with_capacity(3 * SIZE_SINGLE);
    let mut remain = ITER_CNT_SINGLE;
    let mut cnt = 0;
    while remain > 0 {
        remain -= 1;
        cnt += 1;
        if cnt > 2 * ITER_CNT_SINGLE {
            panic!("took too long")
        }
        match rand.u8(0..=7) {
            0..=1 if refs.len() > 0 => {
                let _ = refs.swap_remove(rand.usize(0..refs.len()));
            }
            // 1 => (),
            2..=3 if weaks.len() > 0 => {
                let (weak, expected): (std::rc::Weak<usize>, _) =
                    weaks.swap_remove(rand.usize(0..weaks.len()));
                if let Some(tref) = weak.upgrade() {
                    assert_eq!(*tref, expected);
                }
            }
            4..=5 if weaks.len() < 3 * SIZE_SINGLE && refs.len() > 0 => {
                let tref = &refs[rand.usize(0..refs.len())];
                weaks.push((Rc::downgrade(tref), **tref));
            }
            6 if refs.len() < SIZE_SINGLE => {
                let res = Rc::new({
                    epoch += 1;
                    epoch
                });
                refs.push(res);
            }
            7 if refs.len() < SIZE_SINGLE && refs.len() > 0 => {
                let tref = &refs[rand.usize(0..refs.len())];
                refs.push(tref.clone());
            }
            8.. => unreachable!(),
            _ => {
                remain += 1;
            }
        };
    }
}

const ITER_CNT_SINGLE: i64 = 10_000;
const SIZE_SINGLE: usize = 1000;

const THREAD_CNT_SYNC: usize = 12;
const ITER_CNT_SYNC: i64 = 100_000_000;
const SIZE_SYNC: usize = 1000;
fn main() {
    // fuzz_single()
    // fuzz_single_alloc()
    fuzz()
    // fuzz_alloc()
}
