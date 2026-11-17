// SPDX-License-Identifier: MIT

//! presence's Some is not None, and not the masks with a bit flipped, when the read is allowed: the
//! read's other answer, and a wrong one.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/presence.rs	presence	Some
//! refused: wrong: kernel.presence_read(root, slot, va, level, count, ret)
//! refused: flipped: kernel.presence_read(root, slot, va, level, count, ret)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::presence::Presence;

impl super::PresenceNone for () {
    proof fn wrong(kernel: CapKernel, root: usize, slot: usize, va: u64, level: u64, count: u64, ret: Option<Presence>) {}

    proof fn flipped(kernel: CapKernel, root: usize, slot: usize, va: u64, level: u64, count: u64, ret: Option<Presence>) {}
}

} // verus!
