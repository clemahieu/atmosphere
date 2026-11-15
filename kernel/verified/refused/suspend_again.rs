// SPDX-License-Identifier: MIT

//! Suspend's Again answer meets no unchanged kernel: no stop is pending and no stop IPI was sent.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/thread.rs	suspend	Again
//! refused: unchanged: CapKernel::suspend_answered(pre, post, c, root, i, ret)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::thread::SuspendStep;

impl super::SuspendAgain for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, root: usize, i: usize, ret: SuspendStep) {}
}

} // verus!
