// SPDX-License-Identifier: MIT

//! revoke's Again meets no unchanged kernel whose slot holds a capability that has children: the run
//! did not shrink by the budget. design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/revoke.rs	revoke	Again
//! refused: unchanged: ret is Again ==> pre.list.seq@.len() - post.list.seq@.len() == REVOKE_BUDGET

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;
use crate::capability::revoke::RevokeStep;

impl super::RevokeBudget for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Position, ret: RevokeStep) {}
}

} // verus!
