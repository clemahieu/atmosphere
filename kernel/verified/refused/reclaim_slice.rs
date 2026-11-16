// SPDX-License-Identifier: MIT

//! reclaim's Slice meets no unchanged kernel: the leaf's list is not shorter.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/reclaim.rs	reclaim	Slice
//! refused: unchanged: pre.can_slice_leaf(root, from, base) ==> ret is Slice && pre.leaf_sliced(post, root, from, base)
//! refused: unchanged: ret is Slice ==> pre.leaf_sliced(post, root, from, base) || pre.table_sliced(post, root, from, base) || pre.space_children_cut(post, root, from, base) || pre.thread_unbound(post, root, from, base) || pre.process_retired(post, base) || pre.process_space_cut(post, root, from, base)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::reclaim::ReclaimStep;

impl super::ReclaimSlice for () {
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
