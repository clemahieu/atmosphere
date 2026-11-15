// SPDX-License-Identifier: MIT

//! check_current's Kept where the thread need not leave, claimed as MovedOff. The kernel is unchanged,
//! which is Kept's own post, so the thread was not moved off and the answer is not the state's.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/thread.rs	check_current	Kept
//! refused: wrong: ret is MovedOff == pre.must_leave(c as int)
//! refused: wrong: ret is Kept == !pre.must_leave(c as int)

use vstd::prelude::*;

verus! {

use crate::arch::{FrameKind, Registers};
use crate::capability::kernel::CapKernel;
use crate::capability::thread::CurrentStep;

impl super::CheckCurrentKept for () {
    proof fn wrong(pre: CapKernel, post: CapKernel, c: usize, frame: Registers, saved: FrameKind, ret: CurrentStep) {}
}

} // verus!
