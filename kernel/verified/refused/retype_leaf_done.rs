// SPDX-License-Identifier: MIT

//! retype_leaf's success meets no unchanged kernel: the call is allowed, and the free pages are not a table leaf.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/retype.rs	retype_leaf	true
//! refused: unchanged: ret ==> CapKernel::leaf_retyped(pre, post, root, from, at, base)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::position::Position;

impl super::RetypeLeafDone for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, at: Position, base: usize, ret: bool) {}
}

} // verus!
