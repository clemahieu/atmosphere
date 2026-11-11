// SPDX-License-Identifier: MIT

//! The queue lock holding a value, and the boot test that both cores contend for it.

use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut};
use core::sync::atomic::{AtomicUsize, Ordering};

use verified::queue_lock::{Core, QueueLock};
use vstd::prelude::Tracked;

use crate::cpu::{self, spin_until};

/// A value only the core holding the lock can reach.
pub struct Locked<T> {
    lock: QueueLock,
    value: UnsafeCell<T>,
    #[cfg(feature = "lock_stats")]
    stats: UnsafeCell<stats::LockStats>,
}

// The lock gives one core at a time the value.
unsafe impl<T: Send> Sync for Locked<T> {}

impl<T> Locked<T> {
    /// `name` labels this lock's reports in a lock_stats build. The lock's per-core tokens go nowhere:
    /// a static cannot hand them out, so each call conjures the core's token, as the kernel conjures
    /// its boot permissions.
    pub const fn new(name: &'static str, value: T) -> Self {
        #[cfg(not(feature = "lock_stats"))]
        let _ = name;
        let (lock, _cores) = QueueLock::new();
        Self {
            lock,
            value: UnsafeCell::new(value),
            #[cfg(feature = "lock_stats")]
            stats: UnsafeCell::new(stats::LockStats::new(name)),
        }
    }

    pub fn lock(&self) -> Guard<'_, T> {
        let cpu = cpu::get_cpu_id();
        #[cfg(feature = "lock_stats")]
        let asked = stats::now();
        let core: Tracked<&mut Core> = Tracked::assume_new();
        self.lock.acquire(cpu, core);
        #[cfg(feature = "lock_stats")]
        let held_from = {
            let held_from = stats::now();
            // Holding the lock, so this is the only core touching the stats.
            unsafe { (*self.stats.get()).waited(held_from - asked) };
            held_from
        };
        Guard {
            locked: self,
            cpu,
            #[cfg(feature = "lock_stats")]
            held_from,
        }
    }
}

pub struct Guard<'a, T> {
    locked: &'a Locked<T>,
    cpu: usize,
    #[cfg(feature = "lock_stats")]
    held_from: u64,
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
        #[cfg(feature = "lock_stats")]
        let report = {
            // Holding the lock, so this is the only core touching the stats.
            let stats = unsafe { &mut *self.locked.stats.get() };
            stats.held(stats::now() - self.held_from);
            stats.report_due().then(|| *stats)
        };
        let core: Tracked<&mut Core> = Tracked::assume_new();
        self.locked.lock.release(self.cpu, core);
        // After the release, so that logging is not part of what it measures.
        #[cfg(feature = "lock_stats")]
        if let Some(stats) = report {
            stats.log();
        }
    }
}

/// Times each hold of a lock and each wait for it. A build option, since three reads of the cycle counter per hold is
/// a real share of a syscall and would change the numbers it sits beside.
#[cfg(feature = "lock_stats")]
mod stats {
    /// How many holds between reports. dom0 ends the boot by a port write the kernel does not see, so
    /// the last report before that is the one to read.
    const REPORT_EVERY: u64 = 4096;

    pub fn now() -> u64 {
        crate::arch::cycles()
    }

    #[derive(Clone, Copy)]
    pub struct LockStats {
        name: &'static str,
        holds: u64,
        held_total: u64,
        held_max: u64,
        waited_total: u64,
        waited_max: u64,
    }

    impl LockStats {
        pub const fn new(name: &'static str) -> Self {
            Self { name, holds: 0, held_total: 0, held_max: 0, waited_total: 0, waited_max: 0 }
        }

        pub fn waited(&mut self, cycles: u64) {
            self.waited_total += cycles;
            self.waited_max = self.waited_max.max(cycles);
        }

        pub fn held(&mut self, cycles: u64) {
            self.holds += 1;
            self.held_total += cycles;
            self.held_max = self.held_max.max(cycles);
        }

        pub fn report_due(&self) -> bool {
            self.holds % REPORT_EVERY == 0
        }

        pub fn log(&self) {
            log::info!(
                "{} lock: {} holds, held mean {} max {}, waited mean {} max {} cycles",
                self.name,
                self.holds,
                self.held_total / self.holds,
                self.held_max,
                self.waited_total / self.holds,
                self.waited_max,
            );
        }
    }
}

/// Increments per core in the contention test, and by CPU 0 alone before it.
const CONTENTION_ROUNDS: usize = 200_000;

/// A pair that matches whenever the lock is free: holding it, a core breaks the match and restores it,
/// so another core inside at the same moment would see them differ, or lose an increment.
static CONTENDED: Locked<(u64, u64)> = Locked::new("contention test", (0, 0));
/// The same, for CPU 0 to hold alone before the other core starts: the loop without a handoff.
static ALONE: Locked<(u64, u64)> = Locked::new("alone test", (0, 0));
/// What each core's contended loop took, by core, set before the core counts itself finished.
static TOOK: Locked<[Option<Took>; 2]> = Locked::new("contention results", [None; 2]);
static ARRIVED: AtomicUsize = AtomicUsize::new(0);
static FINISHED: AtomicUsize = AtomicUsize::new(0);

/// The cycle count and performance counters 0 to 3 at a moment, or how far they moved between two. The
/// counters are what each core counts from bring-up, where it has them: cycles not in halt, retired
/// instructions, data cache fills, and the fills that came from another CCX's cache, which on a part
/// with one CCX per CCD are the lines that crossed a CCD.
#[derive(Clone, Copy)]
struct Took {
    ticks: u64,
    counts: Option<[u64; 4]>,
}

impl Took {
    fn now() -> Self {
        Self { ticks: crate::arch::cycles(), counts: crate::arch::counters() }
    }

    /// How far each moved from `start` to now. Counters zeroed at bring-up do not wrap in a boot test.
    fn since(start: Self) -> Self {
        let end = Self::now();
        Self {
            ticks: end.ticks - start.ticks,
            counts: start.counts.zip(end.counts).map(|(a, b)| core::array::from_fn(|n| b[n] - a[n])),
        }
    }

    /// Logs this, taken over CONTENTION_ROUNDS acquisitions, per acquisition.
    fn log(&self, what: &str, cpu: usize) {
        let per = PerRound;
        match self.counts {
            Some([cycles, instructions, fills, ccx_fills]) => log::info!(
                "lock {} on CPU {}, per acquisition: {} ticks, {} cycles, {} instructions, {} fills, {} ccx fills",
                what,
                cpu,
                per(self.ticks),
                per(cycles),
                per(instructions),
                per(fills),
                per(ccx_fills),
            ),
            None => log::info!("lock {} on CPU {}, per acquisition: {} ticks, no counters", what, cpu, per(self.ticks)),
        }
    }
}

/// A total over CONTENTION_ROUNDS, printed per round to two decimal places.
struct PerRound(u64);

impl core::fmt::Display for PerRound {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let hundredths = self.0 * 100 / CONTENTION_ROUNDS as u64;
        write!(f, "{}.{:02}", hundredths / 100, hundredths % 100)
    }
}

/// Takes `locked` CONTENTION_ROUNDS times, breaking and restoring its pair each time, and returns what
/// that took. Panics if the lock let two cores in together.
fn hold_rounds(locked: &Locked<(u64, u64)>) -> Took {
    let start = Took::now();
    for _ in 0..CONTENTION_ROUNDS {
        let mut pair = locked.lock();
        assert_eq!(pair.0, pair.1, "two cores inside the lock");
        // Volatile, so neither write folds into the other and the window stays open.
        unsafe { core::ptr::write_volatile(&mut pair.0, pair.0 + 1) };
        core::hint::spin_loop();
        unsafe { core::ptr::write_volatile(&mut pair.1, pair.1 + 1) };
    }
    Took::since(start)
}

/// CPU 0 calls this before the other core starts, and logs what the loop takes with no handoff.
pub fn time_alone() {
    hold_rounds(&ALONE).log("alone", cpu::get_cpu_id());
}

/// Both cores call this. Panics if the lock let them in together.
pub fn contend() {
    ARRIVED.fetch_add(1, Ordering::SeqCst);
    spin_until(|| ARRIVED.load(Ordering::SeqCst) >= 2);
    let took = hold_rounds(&CONTENDED);
    TOOK.lock()[cpu::get_cpu_id()] = Some(took);
    FINISHED.fetch_add(1, Ordering::SeqCst);
}

/// CPU 0 calls this after contend, to wait for the other core and report.
pub fn report_contention() {
    spin_until(|| FINISHED.load(Ordering::SeqCst) >= 2);
    let pair = CONTENDED.lock();
    assert_eq!(pair.0, pair.1, "two cores inside the lock");
    assert_eq!(pair.0, 2 * CONTENTION_ROUNDS as u64, "lost an increment");
    log::info!("lock contended by 2 cores: pair intact at {}", pair.0);
    for (cpu, took) in TOOK.lock().iter().enumerate() {
        took.expect("a core finished without its result").log("contended", cpu);
    }
}
