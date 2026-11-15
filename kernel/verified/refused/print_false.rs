// SPDX-License-Identifier: MIT

//! print's true at a slot that holds the console, claimed at the other bool. The kernel is unchanged,
//! which is print's own post.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/console.rs	print	true
//! refused: wrong: ret == pre.holds_console(root, i)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::PrintFalse for () {
    proof fn wrong(pre: CapKernel, post: CapKernel, root: usize, i: usize, ret: bool) {}
}

} // verus!
