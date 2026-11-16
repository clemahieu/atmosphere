// SPDX-License-Identifier: MIT

//! move_cap's success meets no unchanged kernel: the call is allowed, and the capability is still in the source slot.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/moving.rs	move_cap	true
//! refused: unchanged: ret ==> CapKernel::cap_moved_at(pre, post, root, from, to)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;

impl super::MoveCapOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: Position, to: Position, ret: bool) {}
}

} // verus!
