// SPDX-License-Identifier: MIT

//! enter_flush meets no unchanged kernel whose core is behind the epoch. The requires are the
//! operation's plus that unchanged kernel; nothing says the core is already caught up, which is the
//! state an unchanged kernel would already satisfy.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/operation.rs	enter_flush	returns
//! refused: unchanged: post.acked(c as int) == post.flush_epoch

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::EnterFlushReturns for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize) {}
}

} // verus!
