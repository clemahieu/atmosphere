// SPDX-License-Identifier: MIT

//! map_nested's success meets no unchanged kernel: the call is allowed and nothing was written, so
//! neither a page nor a large page was mapped into the nested table.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/guest_space.rs	map_nested	true
//! refused: unchanged: ret && r.large() ==> CapKernel::map_large_done(pre, post, root, slot, r.path(), from, page)
//! refused: unchanged: ret && !r.large() ==> CapKernel::map_done(pre, post, root, slot, r.path(), from, page)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::guest_space::GuestPhysRange;

impl super::MapNestedOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, slot: usize, r: GuestPhysRange, from: usize, page: usize, ret: bool) {}
}

} // verus!
