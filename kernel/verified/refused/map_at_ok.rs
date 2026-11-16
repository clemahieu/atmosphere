// SPDX-License-Identifier: MIT

//! map_at's success meets no unchanged kernel: the call is allowed, and the page is not mapped at the entry.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/map.rs	map_at	true
//! refused: unchanged: ret ==> CapKernel::page_mapped(pre, post, root, slot, va, level, from, page)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::MapAtOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, slot: usize, va: u64, level: u64, from: usize, page: usize, ret: bool) {}
}

} // verus!
