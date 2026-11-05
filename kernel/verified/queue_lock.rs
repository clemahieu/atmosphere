//! The queue lock over the kernel's state. Each waiter spins on its own cache line, so the line holding
//! the lock's word does not bounce between every waiter on each handover. On this host a lock every
//! waiter spins on fell well below a queue lock across two CCDs, in the simulation recorded on the
//! multicore decision, atmo-6x9.6.8. This is an MCS lock with one node per core: a core holds the lock
//! at most once, since interrupts are off while it does.
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use vstd::prelude::*;

use crate::define::NUM_CPUS;

/// One core's place in the queue, on its own cache line.
#[repr(align(64))]
struct Node {
    /// The next waiter's core plus one, or 0.
    next: AtomicUsize,
    /// True while this core waits.
    waiting: AtomicBool,
}

const NEW_NODE: Node = Node { next: AtomicUsize::new(0), waiting: AtomicBool::new(false) };

verus! {

#[verifier::external_body]
pub struct QueueLock {
    /// The last waiter's core plus one, or 0 when the lock is free.
    tail: AtomicUsize,
    nodes: [Node; NUM_CPUS],
}

impl QueueLock {
    #[verifier(external_body)]
    // external_body(unproven): builds the atomics of a lock whose mutual exclusion is not proven yet
    pub const fn new() -> Self {
        Self { tail: AtomicUsize::new(0), nodes: [NEW_NODE; NUM_CPUS] }
    }

    /// Waits for the lock on behalf of `cpu`, which must not hold it.
    #[verifier(external_body)]
    // external_body(unproven): atomics of a lock whose mutual exclusion is not proven yet
    pub fn acquire(&self, cpu: usize)
        requires
            cpu < NUM_CPUS,
    {
        let node = &self.nodes[cpu];
        node.next.store(0, Ordering::Relaxed);
        node.waiting.store(true, Ordering::Relaxed);
        let previous = self.tail.swap(cpu + 1, Ordering::AcqRel);
        if previous != 0 {
            self.nodes[previous - 1].next.store(cpu + 1, Ordering::Release);
            while node.waiting.load(Ordering::Acquire) {
                core::hint::spin_loop();
            }
        }
    }

    /// Hands the lock on from `cpu`, which must hold it.
    #[verifier(external_body)]
    // external_body(unproven): atomics of a lock whose mutual exclusion is not proven yet
    pub fn release(&self, cpu: usize)
        requires
            cpu < NUM_CPUS,
    {
        let node = &self.nodes[cpu];
        let mut next = node.next.load(Ordering::Acquire);
        if next == 0 {
            if self.tail.compare_exchange(cpu + 1, 0, Ordering::Release, Ordering::Relaxed).is_ok() {
                return;
            }
            // A waiter has swapped the tail and is about to link itself.
            while next == 0 {
                core::hint::spin_loop();
                next = node.next.load(Ordering::Acquire);
            }
        }
        self.nodes[next - 1].waiting.store(false, Ordering::Release);
    }
}

} // verus!
