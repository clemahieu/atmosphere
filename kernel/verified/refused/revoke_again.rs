// SPDX-License-Identifier: MIT

//! Revoke's again arm meets no unchanged post. The arm says the run shrank by the budget and a node of it remains, so the same revoke is the one a caller repeats.
//! design/refused-claim-per-way/.
//!
//! refused: unchanged: CapKernel::revoke_contract(pre, post, root, at, status_only(STATUS_AGAIN))

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;

impl super::RevokeAgain for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Option<Position>) {}
}

} // verus!
