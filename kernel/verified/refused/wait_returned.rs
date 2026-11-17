// SPDX-License-Identifier: MIT

//! wait's Returned meets no unchanged kernel: the word has a signalled bit, and the kernel did
//! not clear it. design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/notification.rs	wait	Returned
//! refused: unchanged: ret is Returned ==> CapKernel::waited(pre, post, root, i, ret->Returned_0)

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;
use crate::capability::notification::WaitStep;

impl super::WaitReturned for () {
    proof fn unchanged(
        pre: CapKernel,
        post: CapKernel,
        c: usize,
        root: usize,
        i: usize,
        frame: Registers,
        ret: WaitStep,
    ) {}
}

} // verus!
