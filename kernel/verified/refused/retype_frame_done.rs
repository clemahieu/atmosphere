// SPDX-License-Identifier: MIT

//! retype_frame's success meets no unchanged kernel: the call is allowed, and the free page is not a frame.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/retype.rs	retype_frame	true
//! refused: unchanged: ret ==> CapKernel::frame_retyped(pre, post, root, from, to, base)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::RetypeFrameDone for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: usize, base: usize, ret: bool) {}
}

} // verus!
