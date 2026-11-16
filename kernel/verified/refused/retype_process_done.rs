// SPDX-License-Identifier: MIT

//! retype_process's success meets no unchanged kernel: the call is allowed, and the free block is not a process.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/process.rs	retype_process	true
//! refused: unchanged: ret ==> CapKernel::process_retype_done(pre, post, root, from, to, base)
//! refused: unchanged: ret ==> CapKernel::process_retyped(pre, post, root, from, to, base)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::RetypeProcessDone for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: usize, base: usize, ret: bool) {}
}

} // verus!
