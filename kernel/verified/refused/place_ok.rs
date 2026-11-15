// SPDX-License-Identifier: MIT

//! Place's success meets no unchanged kernel: the call is allowed and nothing changed, and the thread is not placed.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/thread.rs	place	true
//! refused: unchanged: ret ==> CapKernel::place_done(pre, post, root, i, j, priority)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::PlaceOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, j: usize, priority: usize, ret: bool) {}
}

} // verus!
