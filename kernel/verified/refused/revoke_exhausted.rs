// SPDX-License-Identifier: MIT

//! revoke's Exhausted meets no unchanged kernel whose slot holds a capability and whose epoch is below
//! the limit: the flush epoch is not at its limit. design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/revoke.rs	revoke	Exhausted
//! refused: unchanged: ret is Exhausted ==> post.flush_epoch == usize::MAX

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;
use crate::capability::revoke::RevokeStep;

impl super::RevokeExhausted for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Position, ret: RevokeStep) {}
}

} // verus!
