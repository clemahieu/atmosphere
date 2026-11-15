// SPDX-License-Identifier: MIT

//! probe_at's Some meets no unchanged kernel. The view stays and the level 1 table's words are part
//! of the kernel, so they stay too: the probed prefix, which clears accessed and dirty bits, does not
//! hold.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/probe.rs	probe_at	Some
//! refused: unchanged: ret is Some ==> CapKernel::probe_done(pre, post, root, slot, va, count, ret->0)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::probe::Probed;

impl super::ProbeAtSome for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, slot: usize, va: u64, count: u64, ret: Option<Probed>) {}
}

} // verus!
