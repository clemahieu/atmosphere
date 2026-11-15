// SPDX-License-Identifier: MIT

//! Derive names the destination slot. A slot the contract does not name does not change.
//! design/refused-claim-per-way/.
//!
//! refused: claim: unnamed_derive::unnamed(pre, post, root, frame)

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
    match spec_position(frame.spec_argument(1)) {
        Some(to) => match pre.view_table_at(root, to.through) {
            Some(table) => exists|t: usize, j: usize|
                !(t == table && j == to.index) && #[trigger] slot_changed(pre, post, t, j),
            None => false,
        },
        None => false,
    }
}

impl super::UnnamedDerive for () {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome) {
        CapKernel::lemma_derive_contract(pre, post, root, frame, out);
    }
}

} // verus!
