//! The queue lock holding a value, and the boot test that both cores contend for it.

use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut};
use core::sync::atomic::{AtomicUsize, Ordering};

use verified::queue_lock::QueueLock;

use crate::cpu;

/// A value only the core holding the lock can reach.
pub struct Locked<T> {
    lock: QueueLock,
    value: UnsafeCell<T>,
}

// The lock gives one core at a time the value.
unsafe impl<T: Send> Sync for Locked<T> {}

impl<T> Locked<T> {
    pub const fn new(value: T) -> Self {
        Self { lock: QueueLock::new(), value: UnsafeCell::new(value) }
    }

    pub fn lock(&self) -> Guard<'_, T> {
        let cpu = cpu::get_cpu_id();
        self.lock.acquire(cpu);
        Guard { locked: self, cpu }
    }
}

pub struct Guard<'a, T> {
    locked: &'a Locked<T>,
    cpu: usize,
}

impl<T> Deref for Guard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.locked.value.get() }
    }
}

impl<T> DerefMut for Guard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.locked.value.get() }
    }
}

impl<T> Drop for Guard<'_, T> {
    fn drop(&mut self) {
        self.locked.lock.release(self.cpu);
    }
}

/// Increments per core in the contention test.
const CONTENTION_ROUNDS: usize = 200_000;

/// A pair that matches whenever the lock is free: holding it, a core breaks the match and restores it,
/// so another core inside at the same moment would see them differ, or lose an increment.
static CONTENDED: Locked<(u64, u64)> = Locked::new((0, 0));
static ARRIVED: AtomicUsize = AtomicUsize::new(0);
static FINISHED: AtomicUsize = AtomicUsize::new(0);

/// Both cores call this. Panics if the lock let them in together.
pub fn contend() {
    ARRIVED.fetch_add(1, Ordering::SeqCst);
    while ARRIVED.load(Ordering::SeqCst) < 2 {
        core::hint::spin_loop();
    }
    for _ in 0..CONTENTION_ROUNDS {
        let mut pair = CONTENDED.lock();
        assert_eq!(pair.0, pair.1, "two cores inside the lock");
        // Volatile, so neither write folds into the other and the window stays open.
        unsafe { core::ptr::write_volatile(&mut pair.0, pair.0 + 1) };
        core::hint::spin_loop();
        unsafe { core::ptr::write_volatile(&mut pair.1, pair.1 + 1) };
    }
    FINISHED.fetch_add(1, Ordering::SeqCst);
}

/// CPU 0 calls this after contend, to wait for the other core and report.
pub fn report_contention() {
    while FINISHED.load(Ordering::SeqCst) < 2 {
        core::hint::spin_loop();
    }
    let pair = CONTENDED.lock();
    assert_eq!(pair.0, pair.1, "two cores inside the lock");
    assert_eq!(pair.0, 2 * CONTENTION_ROUNDS as u64, "lost an increment");
    log::info!("lock contended by 2 cores: pair intact at {}", pair.0);
}
