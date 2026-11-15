// SPDX-License-Identifier: MIT

//! Acquire's success meets no unchanged lock and no unchanged core. The operation borrows the lock,
//! so the claim has that one value, and the core keeps the idle state, the ids and the ticket
//! counters it started with. It is not holding, and the ticket bound is not established.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/queue_lock.rs	QueueLock::acquire	returns
//! refused: unchanged: post_core.holding() && post_core.swapped <= post_core.granted && post_core.granted <= post_core.swapped + NUM_CPUS - 1

use vstd::prelude::*;

verus! {

use crate::queue_lock::{Core, QueueLock};

impl super::QueueLockAcquire for () {
    proof fn unchanged(lock: &QueueLock, cpu: usize, pre_core: Core, post_core: Core) {}
}

} // verus!
