// SPDX-License-Identifier: MIT

//! wait's Some meets no unchanged kernel: the word has a signalled bit, and it was not cleared.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/notification.rs	wait	Some
//! refused: unchanged: ret is Some ==> CapKernel::waited(pre, post, root, i, ret->0)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::WaitSome for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, ret: Option<u64>) {}
}

} // verus!
