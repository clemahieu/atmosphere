// SPDX-License-Identifier: MIT

//! reclaim_frame's Freed meets no unchanged kernel: the dead frame every core has acknowledged is still that frame.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/reclaim.rs	reclaim_frame	Freed
//! refused: unchanged: ret is Freed ==> pre.frame_freed(post, c, root, from, base)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::reclaim::FrameReclaimStep;

impl super::ReclaimFrameFreed for () {
    proof fn unchanged(
        pre: CapKernel,
        post: CapKernel,
        c: usize,
        root: usize,
        from: usize,
        base: usize,
        pre_steps: nat,
        post_steps: nat,
        ret: FrameReclaimStep,
    ) {
    }
}

} // verus!
