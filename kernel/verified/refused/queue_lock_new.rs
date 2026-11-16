// SPDX-License-Identifier: MIT

//! QueueLock::new's ensures at a core map in which core 0 holds the lock. Every core is in the domain,
//! with its cpu and this lock, which is what new ensures of the cores besides idle, and idle is open
//! where the lock's wf is closed. design/refused-claim-per-way/.
//!
//! covers: kernel/verified/queue_lock.rs	QueueLock::new	returns
//! refused: wrong: forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] cores.dom().contains(c) && cores[c].idle() && cores[c].cpu == c && cores[c].for_lock(lock)

use vstd::prelude::*;

verus! {

use crate::queue_lock::{Core, QueueLock};

impl super::QueueLockNew for () {
    proof fn wrong(lock: QueueLock, cores: Map<int, Core>) {}
}

} // verus!
