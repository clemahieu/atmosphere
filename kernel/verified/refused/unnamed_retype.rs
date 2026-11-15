// SPDX-License-Identifier: MIT

//! Retype names the destination slot in argument 3. A slot other than that one does not change.
//! design/refused-claim-per-way/.
//!
//! refused: claim: unnamed_retype::unnamed(pre, post, root, frame)

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;
use crate::capability::operation::Outcome;


pub open spec fn slot_changed(pre: CapKernel, post: CapKernel, t: usize, j: usize) -> bool {
    ||| post.table_view(t).contains_key(j) != pre.table_view(t).contains_key(j)
    ||| pre.table_view(t).contains_key(j) && post.table_view(t)[j] != pre.table_view(t)[j]
}

pub open spec fn unnamed(pre: CapKernel, post: CapKernel, root: usize, frame: Registers) -> bool {
    exists|t: usize, j: usize|
        !(t == root && j == frame.spec_argument(3) as usize) && #[trigger] slot_changed(pre, post, t, j)
}

impl super::UnnamedRetype for () {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome) {
        CapKernel::lemma_retype_contract(pre, post, root, frame, out);
    }
}

} // verus!
