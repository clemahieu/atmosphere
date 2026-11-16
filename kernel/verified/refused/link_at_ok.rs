// SPDX-License-Identifier: MIT

//! link_at's success meets no unchanged kernel: the call is allowed, and the table page is not linked at the entry.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/map.rs	link_at	true
//! refused: unchanged: ret ==> CapKernel::table_linked(pre, post, root, slot, va, level, from, child)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::LinkAtOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, slot: usize, va: u64, level: u64, from: usize, child: usize, ret: bool) {}
}

} // verus!
