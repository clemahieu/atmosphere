// SPDX-License-Identifier: MIT

//! inspect's Some of a payload other than the one the slot holds. The kernel is unchanged, which is
//! inspect's own post, and the slot does hold a capability.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/inspect.rs	inspect	Some
//! refused: wrong: kernel.inspect_reads(root, at, ret)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;
use crate::capability::table::Payload;

impl super::InspectOther for () {
    proof fn wrong(kernel: CapKernel, root: usize, at: Position, ret: Option<(Payload, u64)>) {}
}

} // verus!
