// SPDX-License-Identifier: MIT

//! Release's success meets no unchanged lock and no unchanged core. The operation borrows the lock,
//! so the claim has that one value, and the core keeps the holding state and the ids it started
//! with. It is not idle.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/queue_lock.rs	QueueLock::release	returns
//! refused: unchanged: post_core.idle()

use vstd::prelude::*;

verus! {

use crate::queue_lock::{Core, QueueLock};

impl super::QueueLockRelease for () {
    proof fn unchanged(lock: &QueueLock, cpu: usize, pre_core: Core, post_core: Core) {}
}

} // verus!
