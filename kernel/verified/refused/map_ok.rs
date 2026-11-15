// SPDX-License-Identifier: MIT

//! Map's ok arm meets no unchanged post: the call is allowed and the kernel is the one it was, and the arm's contract fails.
//! design/refused-claim-per-way/.
//!
//! refused: unchanged: CapKernel::map_contract(pre, post, root, slot, va, level, from, page, status_only(STATUS_OK))

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::MapOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, slot: usize, va: u64, level: u64, from: usize, page: usize) {}
}

} // verus!
