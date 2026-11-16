// SPDX-License-Identifier: MIT

//! revoke through a process capability pc that depth and block containment say may be in c's run
//! (R3) does not answer Done, Again, or Exhausted:
//! revoke_answered and spec_revoked must refuse.
//! design/refused-claim-per-way/.
//!
//! refused: wrong: CapKernel::revoke_answered(pre, post, root, at, ret)
//! refused: wrong: CapKernel::spec_revoked(pre, post, root, frame, out)

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;
use crate::capability::operation::Outcome;
use crate::capability::position::Position;
use crate::capability::revoke::RevokeStep;

impl super::RevokeThroughRun for () {
    proof fn wrong(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, at: Position, out: Outcome, ret: RevokeStep) {}
}

} // verus!
