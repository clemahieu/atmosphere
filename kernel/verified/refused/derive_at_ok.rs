// SPDX-License-Identifier: MIT

//! derive's success meets no unchanged kernel: the call is allowed, and no child is linked under the parent.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/derive.rs	derive	true
//! refused: unchanged: ret ==> CapKernel::derive_step(pre, post, pre.tables.node_of(pre.table_at(root, to.through)->0, to.index))
//! refused: unchanged: ret ==> CapKernel::cap_derived_at(pre, post, root, from, to, rights, base, order, badge)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;

impl super::DeriveAtOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: Position, rights: u32, base: usize, order: u8, badge: usize, ret: bool) {}
}

} // verus!
