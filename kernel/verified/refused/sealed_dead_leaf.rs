// SPDX-License-Identifier: MIT

//! A process whose table is at root is not sealed while another table holds, in a leaf whose
//! hidden node is dead, a process capability naming root.
//! design/refused-claim-per-way/.
//!
//! refused: wrong: k.sealed(root)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::SealedDeadLeaf for () {
    proof fn wrong(k: CapKernel, root: usize, other: usize, j: usize) {
        k.lemma_table_view(other, j);
    }
}

} // verus!
