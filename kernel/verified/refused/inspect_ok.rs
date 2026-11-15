// SPDX-License-Identifier: MIT

//! Inspect's ok arm meets no unchanged post that returns an empty result: the call is allowed and the kernel is the one it was, and the arm's contract, which returns the slot's view, fails.
//! design/refused-claim-per-way/.
//!
//! refused: unchanged: CapKernel::inspect_contract(pre, post, root, at, status_only(STATUS_OK))

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;

impl super::InspectOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Option<Position>) {}
}

} // verus!
