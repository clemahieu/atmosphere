// SPDX-License-Identifier: MIT

//! Destroy's success meets no unchanged kernel: the call is allowed and nothing changed, and destroy_done does not hold.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/destroy.rs	destroy	true
//! refused: unchanged: ret ==> CapKernel::destroy_done(pre, post, c, root, i)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::DestroyOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, root: usize, i: usize, ret: bool) {}
}

} // verus!
