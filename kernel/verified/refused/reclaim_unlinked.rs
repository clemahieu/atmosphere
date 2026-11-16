// SPDX-License-Identifier: MIT

//! reclaim's Unlinked meets no unchanged kernel: the leaf's hidden node is still live.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/reclaim.rs	reclaim	Unlinked
//! refused: unchanged: pre.can_unlink_leaf(root, from, base) ==> ret is Unlinked && pre.leaf_unlinked(post, root, from, base)
//! refused: unchanged: ret is Unlinked ==> pre.leaf_unlinked(post, root, from, base) || pre.table_page_unlinked(post, root, from, base)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::reclaim::ReclaimStep;

impl super::ReclaimUnlinked for () {
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
