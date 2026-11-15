// SPDX-License-Identifier: MIT

//! load_space meets no unchanged kernel. The core is not listed on the space, and the space's
//! retire is as it was.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/mapping.rs	load_space	returns
//! refused: unchanged: post.loaded(c as int, s)
//! refused: unchanged: post.spaces.loaded@[s].value().retired == 0

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::LoadSpaceReturns for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, s: usize, pcid: usize) {}
}

} // verus!
