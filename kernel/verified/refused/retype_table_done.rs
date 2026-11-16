// SPDX-License-Identifier: MIT

//! retype_table_page's success meets no unchanged kernel: the call is allowed, and the free block is not a table page.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/space.rs	retype_table_page	true
//! refused: unchanged: ret ==> CapKernel::table_page_retype_done(pre, post, root, from, base, level)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::RetypeTableDone for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, base: usize, level: usize, ret: bool) {}
}

} // verus!
