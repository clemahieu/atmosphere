// SPDX-License-Identifier: MIT

//! Delete's ok arm meets no unchanged post: the call is allowed and the kernel is the one it was, and the arm's contract fails.
//! design/refused-claim-per-way/.
//!
//! refused: unchanged: CapKernel::delete_contract(pre, post, root, at, status_only(STATUS_OK))

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;

impl super::DeleteOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Option<Position>) {}
}

} // verus!
