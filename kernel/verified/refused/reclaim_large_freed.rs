// SPDX-License-Identifier: MIT

//! reclaim_large_frame's Freed meets no unchanged kernel: the dead large frame every core has acknowledged is still typed.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/reclaim.rs	reclaim_large_frame	Freed
//! refused: unchanged: ret is Freed ==> pre.large_frame_freed(post, c, root, from, base, order)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::reclaim::FrameReclaimStep;

impl super::ReclaimLargeFreed for () {
    proof fn unchanged(
        pre: CapKernel,
        post: CapKernel,
        c: usize,
        root: usize,
        from: usize,
        base: usize,
        pre_steps: nat,
        post_steps: nat,
        order: u8,
        ret: FrameReclaimStep,
    ) {
    }
}

} // verus!
