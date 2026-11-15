// SPDX-License-Identifier: MIT

//! enter_boot_thread at an unchanged kernel. The boot thread stays inactive, and the core stays idle.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/thread.rs	enter_boot_thread	returns
//! refused: unchanged: post.cores@[c as int].current_thread == Some(t)
//! refused: unchanged: post.threads.records@[t].value().state == (ThreadState::Running { core: c })

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::EnterBootThreadReturns for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, t: usize) {}
}

} // verus!
