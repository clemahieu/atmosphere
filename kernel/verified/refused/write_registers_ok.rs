// SPDX-License-Identifier: MIT

//! Writing the saved frame meets no unchanged kernel: the call is allowed and the frame was not written.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/thread.rs	write_registers	true
//! refused: unchanged: ret ==> CapKernel::write_registers_done(pre, post, root, i, frame)

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;

impl super::WriteRegistersOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, frame: Registers, ret: bool) {}
}

} // verus!
