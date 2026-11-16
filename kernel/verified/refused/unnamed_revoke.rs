// SPDX-License-Identifier: MIT

//! Revoke names a slot's capability in the run when it leaves and its leaf in the run when it
//! stops being live. A slot whose capability is not in c's run does not leave, and a slot whose
//! leaf is not in c's run does not change.
//! design/refused-claim-per-way/.
//!
//! refused: claim: unnamed_revoke::unnamed(pre, post, root, frame)

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;
use crate::capability::operation::Outcome;
use crate::capability::position::spec_position;
use crate::capability::table::index_entry;

pub open spec fn slot_changed(pre: CapKernel, post: CapKernel, c: usize, t: usize, j: usize) -> bool {
    ||| post.table_view(t).contains_key(j) != pre.table_view(t).contains_key(j)
        && !pre.list.in_run(c, pre.tables.node_of(t, j))
    ||| pre.table_view(t).contains_key(j) && post.table_view(t).contains_key(j)
        && post.table_view(t)[j] != pre.table_view(t)[j]
        && !pre.list.in_run(c, pre.tables.leaf(t, index_entry(j)))
}

pub open spec fn unnamed(pre: CapKernel, post: CapKernel, root: usize, frame: Registers) -> bool {
    match spec_position(frame.spec_slot()) {
        Some(at) => match pre.view_table_at(root, at.through) {
            Some(table) => exists|t: usize, j: usize|
                #[trigger] slot_changed(pre, post, pre.tables.node_of(table, at.index), t, j),
            None => false,
        },
        None => false,
    }
}

impl super::UnnamedRevoke for () {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome) {
        CapKernel::lemma_revoke_contract(pre, post, root, frame, out);
    }
}

} // verus!
