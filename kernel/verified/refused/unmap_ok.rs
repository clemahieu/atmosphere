// SPDX-License-Identifier: MIT

//! Unmap's success meets no unchanged kernel: the entry is still mapped.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/unmap.rs	unmap_at	Some
//! refused: unchanged: ret is Some ==> CapKernel::page_unmapped(pre, post, root, slot, va, level, ret->0)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::unmap::Unmapped;

impl super::UnmapOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, slot: usize, va: u64, level: u64, ret: Option<Unmapped>) {}
}

} // verus!
