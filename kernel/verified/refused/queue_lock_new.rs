// SPDX-License-Identifier: MIT

//! QueueLock::new's ensures at a lock whose fields are not the ones it ensures. The core map is idle
//! and belongs to the lock, which is what new ensures of the cores, and the lock is not well-formed.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/queue_lock.rs	QueueLock::new	returns
//! refused: wrong: lock.wf()

use vstd::prelude::*;

verus! {

use crate::queue_lock::{Core, QueueLock};

impl super::QueueLockNew for () {
    proof fn wrong(lock: QueueLock, cores: Map<int, Core>) {}
}

} // verus!
