// SPDX-License-Identifier: MIT

//! Map names no slot it changes. No slot's view changes.
//! design/refused-claim-per-way/.
//!
//! refused: claim: unnamed_map::unnamed(pre, post)

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;
use crate::capability::operation::Outcome;


pub open spec fn slot_changed(pre: CapKernel, post: CapKernel, t: usize, j: usize) -> bool {
    ||| post.table_view(t).contains_key(j) != pre.table_view(t).contains_key(j)
    ||| pre.table_view(t).contains_key(j) && post.table_view(t)[j] != pre.table_view(t)[j]
}

pub open spec fn unnamed(pre: CapKernel, post: CapKernel) -> bool {
    exists|t: usize, j: usize| #[trigger] slot_changed(pre, post, t, j)
}

impl super::UnnamedMap for () {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome) {
        CapKernel::lemma_map_contract(pre, post, root, frame, out);
    }
}

} // verus!
