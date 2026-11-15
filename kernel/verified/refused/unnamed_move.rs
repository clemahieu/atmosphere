// SPDX-License-Identifier: MIT

//! Move names the source slot and the destination slot. Another slot does not change in presence or in kind, base, order or rights; a child may name a new parent.
//! design/refused-claim-per-way/.
//!
//! refused: claim: unnamed_move::unnamed(pre, post, root, frame)

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;
use crate::capability::operation::Outcome;
use crate::capability::position::spec_position;

pub open spec fn slot_changed(pre: CapKernel, post: CapKernel, t: usize, j: usize) -> bool {
    ||| post.table_view(t).contains_key(j) != pre.table_view(t).contains_key(j)
    ||| pre.table_view(t).contains_key(j) && post.table_view(t)[j] != pre.table_view(t)[j]
}

pub open spec fn presence_or_fields(pre: CapKernel, post: CapKernel, t: usize, j: usize) -> bool {
    ||| post.table_view(t).contains_key(j) != pre.table_view(t).contains_key(j)
    ||| pre.table_view(t).contains_key(j) && post.table_view(t).contains_key(j) && {
        ||| post.table_view(t)[j].kind != pre.table_view(t)[j].kind
        ||| post.table_view(t)[j].base != pre.table_view(t)[j].base
        ||| post.table_view(t)[j].order != pre.table_view(t)[j].order
        ||| post.table_view(t)[j].rights != pre.table_view(t)[j].rights
    }
}

pub open spec fn unnamed(pre: CapKernel, post: CapKernel, root: usize, frame: Registers) -> bool {
    match (spec_position(frame.spec_slot()), spec_position(frame.spec_argument(1))) {
        (Some(f), Some(d)) => match (pre.view_table_at(root, f.through), pre.view_table_at(root, d.through)) {
            (Some(src), Some(dst)) => exists|t: usize, j: usize|
                !(t == src && j == f.index) && !(t == dst && j == d.index)
                    && #[trigger] slot_changed(pre, post, t, j)
                    && presence_or_fields(pre, post, t, j),
            _ => false,
        },
        _ => false,
    }
}

impl super::UnnamedMove for () {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome) {
        CapKernel::lemma_move_contract(pre, post, root, frame, out);
    }
}

} // verus!
