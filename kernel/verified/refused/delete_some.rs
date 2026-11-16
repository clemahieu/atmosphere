// SPDX-License-Identifier: MIT

//! delete's Some meets no unchanged kernel: the call is allowed and the payload is the slot's, and the capability is still there.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/delete.rs	delete	Some
//! refused: unchanged: ret is Some ==> CapKernel::cap_deleted_at(pre, post, root, at)
//! refused: unchanged: ret is Some ==> CapKernel::object_dropped(pre, post, pre.cap_at(root, at)->0)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;
use crate::capability::table::Payload;

impl super::DeleteSome for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Position, ret: Option<Payload>) {}
}

} // verus!
