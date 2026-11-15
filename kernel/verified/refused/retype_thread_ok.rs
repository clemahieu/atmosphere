// SPDX-License-Identifier: MIT

//! Retype's thread ok arm meets no unchanged post: the call is allowed and the kernel is the one it was, and the arm's contract fails.
//! design/refused-claim-per-way/.
//!
//! refused: unchanged: CapKernel::retype_contract(pre, post, root, RETYPE_THREAD, from, base, word, level, status_only(STATUS_OK))

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::RetypeThreadOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, base: usize, word: u64, level: usize) {}
}

} // verus!
