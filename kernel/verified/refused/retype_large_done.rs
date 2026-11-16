// SPDX-License-Identifier: MIT

//! retype_large_frame's Done meets no unchanged kernel: the call is allowed, and the block is not a large frame.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/retype.rs	retype_large_frame	Done
//! refused: unchanged: CapKernel::large_retype_cursor(pre, post, base, ret is Refused)
//! refused: unchanged: ret is Done ==> CapKernel::large_frame_retyped(pre, post, root, from, to, base, order)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::retype::RetypeStep;

impl super::RetypeLargeDone for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: usize, base: usize, order: u8, ret: RetypeStep) {}
}

} // verus!
