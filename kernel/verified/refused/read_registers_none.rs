// SPDX-License-Identifier: MIT

//! Reading the saved frame is not None when the slot holds the thread. The query's other result.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/thread.rs	read_registers	Some
//! refused: wrong: kernel.read_registers_answered(root, i, ret)

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;

impl super::ReadRegistersNone for () {
    proof fn wrong(kernel: CapKernel, root: usize, i: usize, ret: Option<Registers>) {}
}

} // verus!
