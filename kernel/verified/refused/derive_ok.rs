// SPDX-License-Identifier: MIT

//! Derive's ok arm meets no unchanged post: the call is allowed and the kernel is the one it was, and the arm's contract fails.
//! design/refused-claim-per-way/.
//!
//! refused: unchanged: CapKernel::derive_contract(pre, post, root, from, to, rights, base, order, badge, status_only(STATUS_OK))

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;

impl super::DeriveOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: Option<Position>, to: Option<Position>, rights: u64, base: usize, order: u64, badge: u64) {}
}

} // verus!
