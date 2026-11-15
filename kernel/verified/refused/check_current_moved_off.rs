// SPDX-License-Identifier: MIT

//! check_current's MovedOff at an unchanged kernel whose current thread must leave. The thread is
//! still current, so it is not live to return and it was not moved off.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/thread.rs	check_current	MovedOff
//! refused: unchanged: post.current_live(c as int)
//! refused: unchanged: ret is MovedOff ==> CapKernel::moved_off(pre, post, c as int, frame, saved)

use vstd::prelude::*;

verus! {

use crate::arch::{FrameKind, Registers};
use crate::capability::kernel::CapKernel;
use crate::capability::thread::CurrentStep;

impl super::CheckCurrentMovedOff for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, frame: Registers, saved: FrameKind, ret: CurrentStep) {}
}

} // verus!
