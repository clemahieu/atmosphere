// SPDX-License-Identifier: MIT

//! Retype's free-kind ok arm meets no unchanged post: the call is allowed and the kernel is the one it was, and the arm's contract fails. The free-kind again arm is not a claim: spec_retyped's arm for that status is `post == pre` while the frame is not yet acknowledged (capability/operation.rs), so an unchanged post meets it.
//! design/refused-claim-per-way/.
//!
//! refused: unchanged: CapKernel::retype_contract(pre, post, root, RETYPE_FREE, from, base, word, level, status_only(STATUS_OK))

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::RetypeFreeOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, base: usize, word: u64, level: usize) {}
}

} // verus!
