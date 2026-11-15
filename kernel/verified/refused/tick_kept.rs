// SPDX-License-Identifier: MIT

//! tick's Kept where no selected thread preempts, claimed at another result. The kernel is unchanged,
//! which is Kept's own post, and ticked says Kept is exactly that state.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/switch.rs	tick	Kept
//! refused: wrong: !pre.must_leave(c as int) ==> CapKernel::ticked(pre, post, c as int, frame, ret)

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;
use crate::capability::switch::TickStep;

impl super::TickKept for () {
    proof fn wrong(pre: CapKernel, post: CapKernel, c: usize, frame: Registers, kernel_root: usize, ret: TickStep) {}
}

} // verus!
