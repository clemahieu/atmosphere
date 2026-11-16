// SPDX-License-Identifier: MIT

//! retype_thread's success meets no unchanged kernel: the call is allowed, and the free block is not a thread.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/thread.rs	retype_thread	true
//! refused: unchanged: ret ==> CapKernel::thread_retype_done(pre, post, root, from, to, base, j)
//! refused: unchanged: ret ==> CapKernel::thread_retyped(pre, post, root, from, to, base, j)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::RetypeThreadDone for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: usize, base: usize, j: usize, ret: bool) {}
}

} // verus!
