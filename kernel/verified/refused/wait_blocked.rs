// SPDX-License-Identifier: MIT

//! wait's Blocked meets no unchanged kernel: the notification's word has no signalled bit, and the
//! kernel kept the caller on its core instead of blocking it on the notification's queue.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/notification.rs	wait	Blocked
//! refused: unchanged: ret is Blocked ==> CapKernel::wait_blocked(pre, post, c as int, root, i, frame)

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;
use crate::capability::notification::WaitStep;

impl super::WaitBlocked for () {
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
