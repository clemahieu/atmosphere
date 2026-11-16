// SPDX-License-Identifier: MIT

//! reclaim's Freed meets no unchanged kernel: a dead queue the untyped covers is still that queue.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/reclaim.rs	reclaim	Freed
//! refused: unchanged: pre.can_retype_under(root, from, base, 0) && pre.queue_is_dead(base / PAGE_SZ) ==> ret is Freed && pre.queue_freed(post, c, root, from, base)
//! refused: unchanged: ret is Freed ==> pre.frame_freed(post, c, root, from, base) || pre.large_frame_freed(post, c, root, from, base, 9) || pre.large_frame_freed(post, c, root, from, base, 18) || pre.leaf_freed(post, c, root, from, base) || pre.table_freed(post, c, root, from, base) || pre.space_freed(post, c, root, from, base) || pre.thread_freed(post, c, root, from, base) || pre.process_freed(post, c, root, from, base) || pre.queue_freed(post, c, root, from, base) || pre.reply_freed(post, c, root, from, base)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::reclaim::ReclaimStep;

impl super::ReclaimFreed for () {
    proof fn unchanged(
        pre: CapKernel,
        post: CapKernel,
        c: usize,
        root: usize,
        from: usize,
        base: usize,
        pre_steps: nat,
        post_steps: nat,
        ret: ReclaimStep,
    ) {
    }
}

} // verus!
