// SPDX-License-Identifier: MIT

//! revoke's Done meets no unchanged kernel: the run was not taken, and the capability is not left childless.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/revoke.rs	revoke	Done
//! refused: unchanged: CapKernel::revoke_answered(pre, post, root, at, ret)
//! refused: unchanged: !(ret is Refused) ==> CapKernel::cap_revoking_at(pre, post, root, at)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;
use crate::capability::revoke::RevokeStep;

impl super::RevokeDone for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Position, ret: RevokeStep) {}
}

} // verus!
