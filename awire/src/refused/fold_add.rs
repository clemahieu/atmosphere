// SPDX-License-Identifier: MIT

//! `fold_add` at a sum that is not `spec_fold_add`. The ensures is `r == spec_fold_add(a, b)`;
//! this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/checksum.rs	fold_add	returns
//! refused: wrong: r != spec_fold_add(a, b)

use crate::*;

verus! {

impl super::FoldAddReturns for () {
    proof fn wrong(a: u16, b: u16, r: u16) {}
}

} // verus!
