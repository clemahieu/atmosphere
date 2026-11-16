// SPDX-License-Identifier: MIT

//! retype_reply's success meets no unchanged kernel: the free page is still free, so it is not a live reply.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/reply.rs	retype_reply	true
//! refused: unchanged: ret ==> reply_retyped(pre, post, root, from, to, base)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::RetypeReplyOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: usize, base: usize, ret: bool) {}
}

} // verus!
