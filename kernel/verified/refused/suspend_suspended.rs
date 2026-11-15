// SPDX-License-Identifier: MIT

//! Suspend's Suspended answer meets no unchanged kernel: the thread is not left Inactive.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/thread.rs	suspend	Suspended
//! refused: unchanged: CapKernel::suspend_answered(pre, post, c, root, i, ret)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::thread::SuspendStep;

impl super::SuspendSuspended for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, root: usize, i: usize, ret: SuspendStep) {}
}

} // verus!
