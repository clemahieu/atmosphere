// SPDX-License-Identifier: MIT

//! revoke's Done meets no unchanged kernel whose slot holds a capability that has children: the
//! capability is not left childless. design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/revoke.rs	revoke	Done
//! refused: unchanged: !(ret is Refused) ==> (ret is Done == post.list.childless(pre.cap_at(root, at)->0))

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;
use crate::capability::revoke::RevokeStep;

impl super::RevokeDone for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Position, ret: RevokeStep) {}
}

} // verus!
