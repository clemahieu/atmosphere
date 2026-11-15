// SPDX-License-Identifier: MIT

//! Move's ok arm meets no unchanged post: the call is allowed and the kernel is the one it was, and the arm's contract fails.
//! design/refused-claim-per-way/.
//!
//! refused: unchanged: CapKernel::move_contract(pre, post, root, from, to, status_only(STATUS_OK))

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;

impl super::MoveOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: Option<Position>, to: Option<Position>) {}
}

} // verus!
