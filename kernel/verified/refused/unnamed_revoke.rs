// SPDX-License-Identifier: MIT

//! Revoke names the slots of the capability's run. A slot revokes_slot does not name does not change.
//! design/refused-claim-per-way/.
//!
//! refused: claim: unnamed_revoke::unnamed(pre, post, root, frame)

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

pub open spec fn unnamed(pre: CapKernel, post: CapKernel, root: usize, frame: Registers) -> bool {
    match spec_position(frame.spec_slot()) {
        Some(at) => match pre.view_table_at(root, at.through) {
            Some(table) => exists|t: usize, j: usize|
                !pre.revokes_slot(pre.tables.node_of(table, at.index), t, j) && #[trigger] slot_changed(pre, post, t, j),
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
