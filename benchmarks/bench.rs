use genvec::sync::Weak;
use std::{sync::atomic::Ordering, sync::Arc};
use genvec::sync::GenVec;
use std::sync::atomic::AtomicUsize;

#[allow(dead_code)]
fn fuzz() {
    let size = 1 << 26;

    fn task(allocator: &GenVec<usize>, thread_id: usize, thread_cnt: usize, size: usize, epoch: &AtomicUsize) {
        let mut rand = fastrand::Rng::with_seed(12345 + thread_id as u64);
        let mut refs = Vec::from_iter((0..(2 * size / thread_cnt)).filter_map(|_| allocator.alloc( epoch.fetch_add(1, Ordering::Relaxed)).ok()));
        let mut weaks = Vec::with_capacity(3*size);
        let mut cnt = 100_000;
        while cnt > 0 {
            cnt -= 1;
            match rand.u8(0..=7) {
                0 if refs.len() > 0 => {
                    let _ = refs.swap_remove(rand.usize(0..refs.len()));
                },
                1 => (),
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
                    let Ok(res) = allocator.alloc(epoch.fetch_add(1, Ordering::Relaxed)) else { continue };
                    refs.push(res);
                },
                7 if refs.len() < size && refs.len() > 0 => {
                    let tref = &refs[rand.usize(0..refs.len())];
                    refs.push(tref.clone());
                },
                8.. => unreachable!(),
                _ => {
                    cnt += 1;
                }
            };
        }
    }

    let epoch = AtomicUsize::new(0);
    let allocator = GenVec::new(size);
    let tcnt = std::thread::available_parallelism().map_or(4, |c| <usize as From<std::num::NonZeroUsize>>::from(c).max(4));
    // let tcnt = 8;
    let tids = Vec::from_iter(0..tcnt);
    std::thread::scope(|s| {
        for t in &tids {
            s.spawn(|| task(&allocator, *t, tcnt, size, &epoch));
        };
    });
}

#[allow(dead_code)]
fn fuzz_alloc() {
    let size = 1 << 26;

    fn task(thread_id: usize, thread_cnt: usize, size: usize, epoch: &AtomicUsize) {
        let mut rand = fastrand::Rng::with_seed(12345 + thread_id as u64);
        let mut refs = Vec::from_iter((0..(2 * size / thread_cnt)).map(|_| Arc::new(epoch.fetch_add(1, Ordering::Relaxed))));
        let mut weaks = Vec::with_capacity(3*size);
        let mut cnt = 100_000;
        while cnt > 0 {
            cnt -= 1;
            match rand.u8(0..=7) {
                0 if refs.len() > 0 => {
                    let _ = refs.swap_remove(rand.usize(0..refs.len()));
                },
                1 => (),
                2..=3 if weaks.len() > 0 => {
                    let (weak, expected): (std::sync::Weak<usize>, _) = weaks.swap_remove(rand.usize(0..weaks.len()));
                    if let Some(tref) = weak.upgrade() {
                        assert_eq!(*tref, expected);
                    }
                },
                4..=5 if weaks.len() < 3 * size && refs.len() > 0 => {
                    let tref = &refs[rand.usize(0..refs.len())];
                    weaks.push((Arc::downgrade(tref), **tref));
                },
                6 if refs.len() < size => {
                    refs.push(Arc::new(epoch.fetch_add(1, Ordering::Relaxed)));
                },
                7 if refs.len() < size && refs.len() > 0 => {
                    let tref = &refs[rand.usize(0..refs.len())];
                    refs.push(tref.clone());
                },
                8.. => unreachable!(),
                _ => {
                    cnt += 1;
                }
            };
        }
    }

    let epoch = AtomicUsize::new(0);
    let tcnt = std::thread::available_parallelism().map_or(4, |c| <usize as From<std::num::NonZeroUsize>>::from(c).max(4));
    // let tcnt = 8;
    let tids = Vec::from_iter(0..tcnt);
    std::thread::scope(|s| {
        for t in &tids {
            s.spawn(|| task(*t, tcnt, size, &epoch));
        };
    });
}

fn main() {
    // fuzz_alloc()
    fuzz()
}

