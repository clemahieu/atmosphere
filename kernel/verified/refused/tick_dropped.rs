// SPDX-License-Identifier: MIT

//! tick's Dropped at an unchanged idle core. A selected thread that preempts and cannot run would
//! leave its queue, and its record is still the runnable one, so ticked's drop did not happen.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/switch.rs	tick	Dropped
//! refused: unchanged: !pre.must_leave(c as int) ==> CapKernel::ticked(pre, post, c as int, frame, ret)

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;
use crate::capability::switch::TickStep;

impl super::TickDropped for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, frame: Registers, kernel_root: usize, ret: TickStep) {}
}

} // verus!
