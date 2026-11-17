// SPDX-License-Identifier: MIT

//! User-space atomics, uncontended mutex fast-path, sequential/random memory copy, and raw
//! hardware ticks microbenchmarks mapped from Fuchsia `src/tests/microbenchmarks` (`atomics.cc`,
//! `mutex.cc`, `memcpy.cc`, `random_memcpy.cc`, `stdcompat.cc`, and `clock.cc` `TicksGet`,
//! BSD-2-Clause) onto Atmosphere (`design/synthetic-benchmark-suite/`).

use alloc::format;
use alloc::vec::Vec;
use core::hint::black_box;
use core::sync::atomic::{AtomicU32, AtomicU64, Ordering};

use abench::counter::read_tsc_fenced;
use abench::runner::{Registry, RepeatState};

/// Sequential `Memcpy/*` payload sizes matching Fuchsia `memcpy.cc`.
const MEMCPY_SIZES: [usize; 2] = [1000, 100_000];

/// Random `RandomMemcpy/*` block sizes matching the mapped slice/block copy subset.
const RANDOM_MEMCPY_SIZES: [usize; 2] = [64, 4096];

/// Per-buffer size (1 MiB each for disjoint `src` and `dst`, 2 MiB working set total) sized to
/// fit inside `dom0`'s 4 MiB `aeager`/`aheap` heap alongside runner state and offset tables.
const RANDOM_BUFFER_BYTES: usize = 1024 * 1024;

/// Number of precomputed random `(src, dst)` pairs cycled during `RandomMemcpy/*`.
const RANDOM_SEQ_LEN: usize = 1024;
const _: () = assert!(RANDOM_SEQ_LEN.is_power_of_two());

/// Cache-line isolated wrapper avoiding false sharing on both x86_64 and aarch64.
#[repr(C, align(128))]
struct Aligned<T>(T);

trait AtomicWord: Sized {
    type Word: Copy + Eq;
    const ZERO: Self::Word;
    fn new(val: Self::Word) -> Self;
    fn fetch_inc(&self);
    fn cas_inc(&self, expected: Self::Word) -> Option<Self::Word>;
    fn load_gt_zero(&self) -> bool;
    fn load_eq(&self, expected: Self::Word) -> bool;
}

macro_rules! impl_atomic_word {
    ($atomic:ty, $word:ty) => {
        impl AtomicWord for $atomic {
            type Word = $word;
            const ZERO: $word = 0;

            fn new(val: $word) -> Self {
                <$atomic>::new(val)
            }

            #[inline(always)]
            fn fetch_inc(&self) {
                self.fetch_add(1, Ordering::SeqCst);
            }

            #[inline(always)]
            fn cas_inc(&self, expected: $word) -> Option<$word> {
                let next = expected.wrapping_add(1);
                self.compare_exchange(expected, next, Ordering::SeqCst, Ordering::SeqCst)
                    .ok()
                    .map(|_| next)
            }

            fn load_gt_zero(&self) -> bool {
                self.load(Ordering::Relaxed) > 0
            }

            fn load_eq(&self, expected: $word) -> bool {
                self.load(Ordering::Relaxed) == expected
            }
        }
    };
}

impl_atomic_word!(AtomicU32, u32);
impl_atomic_word!(AtomicU64, u64);

fn run_atomic_increment<A: AtomicWord>(state: &mut RepeatState<'_>) -> bool {
    let cell = Aligned(A::new(A::ZERO));
    while state.keep_running() {
        cell.0.fetch_inc();
        black_box(&cell.0);
    }
    cell.0.load_gt_zero()
}

fn run_atomic_cmpxchg<A: AtomicWord>(state: &mut RepeatState<'_>) -> bool {
    let cell = Aligned(A::new(A::ZERO));
    let mut expected = A::ZERO;
    while state.keep_running() {
        let Some(next) = cell.0.cas_inc(expected) else {
            return false;
        };
        expected = next;
        black_box(&cell.0);
    }
    expected != A::ZERO && cell.0.load_eq(expected)
}

fn run_diff_core_cmpxchg(state: &mut RepeatState<'_>) -> bool {
    crate::core_bench::with_diff_core_cas(|counter| {
        while state.keep_running() {
            let expected = counter.load(Ordering::Relaxed);
            let res = counter.compare_exchange(
                expected,
                expected.wrapping_add(1),
                Ordering::SeqCst,
                Ordering::Relaxed,
            );
            let _ = black_box(res);
        }
        true
    })
}

fn run_mutex_fast_lock_unlock(state: &mut RepeatState<'_>) -> bool {
    let mutex = Aligned(astd::sync::Mutex::new(0u64));
    while state.keep_running() {
        let guard = mutex.0.lock();
        black_box(&*guard);
        drop(guard);
    }
    let unlocked = mutex.0.try_lock().is_some();
    unlocked
}

fn alloc_buffer(size: usize, patterned: bool) -> Option<Vec<u8>> {
    let mut buf = Vec::new();
    buf.try_reserve_exact(size).ok()?;
    buf.resize(size, 0);
    if patterned {
        for (i, byte) in buf.iter_mut().enumerate() {
            // Keep every byte non-zero so post-loop verification distinguishes copied data from zeroed dst.
            *byte = ((i as u8).wrapping_mul(37)) | 1;
        }
    }
    Some(buf)
}

fn run_memcpy(state: &mut RepeatState<'_>, size: usize) -> bool {
    let Some(src) = alloc_buffer(size, true) else {
        return false;
    };
    let Some(mut dst) = alloc_buffer(size, false) else {
        return false;
    };
    let src_ptr = src.as_ptr();
    let dst_ptr = dst.as_mut_ptr();
    while state.keep_running() {
        // Safety: `src_ptr` and `dst_ptr` point to disjoint `size`-byte allocations alive for the loop.
        unsafe {
            core::ptr::copy_nonoverlapping(src_ptr, dst_ptr, size);
        }
        black_box(src_ptr);
        black_box(dst_ptr);
    }
    dst == src
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn run_random_memcpy(state: &mut RepeatState<'_>, block_size: usize) -> bool {
    if block_size > RANDOM_BUFFER_BYTES {
        return false;
    }
    let Some(src) = alloc_buffer(RANDOM_BUFFER_BYTES, true) else {
        return false;
    };
    let Some(mut dst) = alloc_buffer(RANDOM_BUFFER_BYTES, false) else {
        return false;
    };
    let mut src_ptrs = Vec::new();
    let mut dst_ptrs = Vec::new();
    if src_ptrs.try_reserve_exact(RANDOM_SEQ_LEN).is_err()
        || dst_ptrs.try_reserve_exact(RANDOM_SEQ_LEN).is_err()
    {
        return false;
    }
    let span = RANDOM_BUFFER_BYTES - block_size + 1;
    let mut rng = 0x517c_c1b7_2722_0a95_u64 ^ (block_size as u64);
    let src_base = src.as_ptr();
    let dst_base = dst.as_mut_ptr();
    for _ in 0..RANDOM_SEQ_LEN {
        let src_off = (splitmix64(&mut rng) as usize) % span;
        let dst_off = (splitmix64(&mut rng) as usize) % span;
        // Safety: `src_off + block_size <= src.len()` and `dst_off + block_size <= dst.len()`.
        unsafe {
            src_ptrs.push(src_base.add(src_off));
            dst_ptrs.push(dst_base.add(dst_off));
        }
    }

    let mut idx = 0usize;
    let mut last = 0usize;
    while state.keep_running() {
        let src_ptr = src_ptrs[idx];
        let dst_ptr = dst_ptrs[idx];
        // Safety: `src` and `dst` are disjoint heap buffers and both sub-slices lie within `RANDOM_BUFFER_BYTES`.
        unsafe {
            core::ptr::copy_nonoverlapping(src_ptr, dst_ptr, block_size);
        }
        black_box(src_ptr);
        black_box(dst_ptr);
        last = idx;
        idx = (idx + 1) & (RANDOM_SEQ_LEN - 1);
    }

    // Safety: `src_ptrs[last]` and `dst_ptrs[last]` are valid `block_size`-byte ranges inside `src` and `dst`.
    unsafe {
        core::slice::from_raw_parts(dst_ptrs[last], block_size)
            == core::slice::from_raw_parts(src_ptrs[last], block_size)
    }
}

fn run_ticks_get(state: &mut RepeatState<'_>) -> bool {
    let t0 = read_tsc_fenced();
    let mut last = t0;
    while state.keep_running() {
        last = black_box(read_tsc_fenced());
    }
    last >= t0
}

/// Registers user-space atomics, uncontended mutex, memcpy/random memcpy, and `TicksGet`.
pub(crate) fn register(registry: &mut Registry) -> bool {
    let registered = registry
        .register("Atomic/Increment/32bit", run_atomic_increment::<AtomicU32>)
        .is_ok()
        && registry
            .register("Atomic/Increment/64bit", run_atomic_increment::<AtomicU64>)
            .is_ok()
        && registry
            .register("Atomic/Cmpxchg/32bit", run_atomic_cmpxchg::<AtomicU32>)
            .is_ok()
        && registry
            .register("Atomic/Cmpxchg/64bit", run_atomic_cmpxchg::<AtomicU64>)
            .is_ok()
        && (crate::core_bench::core_count() < 2
            || registry
                .register("Atomic/ContendedCmpxchg/DiffCore", run_diff_core_cmpxchg)
                .is_ok())
        && registry
            .register("Mutex/FastLockUnlock", run_mutex_fast_lock_unlock)
            .is_ok()
        && MEMCPY_SIZES.into_iter().all(|size| {
            registry
                .register(format!("Memcpy/{size}bytes"), move |state| {
                    run_memcpy(state, size)
                })
                .is_ok()
        })
        && RANDOM_MEMCPY_SIZES.into_iter().all(|block_size| {
            registry
                .register(format!("RandomMemcpy/{block_size}bytes"), move |state| {
                    run_random_memcpy(state, block_size)
                })
                .is_ok()
        })
        && registry.register("TicksGet", run_ticks_get).is_ok();

    registered
}
