// SPDX-License-Identifier: MIT

//! Revoke's ok arm meets no unchanged post: the call is allowed and the kernel is the one it was, and the arm's contract fails. The arm says the capability is left childless.
//! design/refused-claim-per-way/.
//!
//! refused: unchanged: CapKernel::revoke_contract(pre, post, root, at, status_only(STATUS_OK))

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;

impl super::RevokeOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Option<Position>) {}
}

} // verus!
