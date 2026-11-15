// SPDX-License-Identifier: MIT

//! Start's success meets no unchanged kernel: the call is allowed and nothing changed, and the thread is not made runnable.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/thread.rs	start	true
//! refused: unchanged: ret ==> CapKernel::start_done(pre, post, root, i)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::StartOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, ret: bool) {}
}

} // verus!
