// SPDX-License-Identifier: MIT

//! tick's Switched at an unchanged idle core. A selected thread that can run and preempt would take
//! the core, and the core still runs nothing, so ticked's switch did not happen.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/switch.rs	tick	Switched
//! refused: unchanged: !pre.must_leave(c as int) ==> CapKernel::ticked(pre, post, c as int, frame, ret)

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;
use crate::capability::switch::TickStep;

impl super::TickSwitched for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, frame: Registers, kernel_root: usize, ret: TickStep) {}
}

} // verus!
