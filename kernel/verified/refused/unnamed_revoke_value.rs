// SPDX-License-Identifier: MIT

//! Revoke takes slots out of the run. It does not change what a slot that remains says: no slot's view is replaced.
//! design/refused-claim-per-way/.
//!
//! refused: claim: unnamed_revoke_value::unnamed(pre, post)

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;
use crate::capability::operation::Outcome;


pub open spec fn unnamed(pre: CapKernel, post: CapKernel) -> bool {
    exists|t: usize, j: usize|
        #[trigger] post.table_view(t).contains_key(j) && post.table_view(t)[j] != pre.table_view(t)[j]
}

impl super::UnnamedRevokeValue for () {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome) {
        CapKernel::lemma_revoke_contract(pre, post, root, frame, out);
    }
}

} // verus!
