// SPDX-License-Identifier: MIT

//! switch_space meets no unchanged kernel. The core's record does not name the space, and its base
//! register does not hold the root.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/mapping.rs	switch_space	returns
//! refused: unchanged: post.cores@[c as int].space == space
//! refused: unchanged: post.spaces.registers@[c as int].root() == root

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::SwitchSpaceReturns for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, space: Option<usize>, root: usize, tag: usize) {}
}

} // verus!
