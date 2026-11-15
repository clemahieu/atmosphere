// SPDX-License-Identifier: MIT

//! Retype's 2M-frame again arm meets no unchanged post. The arm says the block is being zeroed, the cursor moved when it already was, and the same retype stays allowed.
//! design/refused-claim-per-way/.
//!
//! refused: unchanged: CapKernel::retype_contract(pre, post, root, RETYPE_LARGE_FRAME, from, base, word, level, status_only(STATUS_AGAIN))

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::RetypeLargeAgain for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, base: usize, word: u64, level: usize) {}
}

} // verus!
