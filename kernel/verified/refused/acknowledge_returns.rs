// SPDX-License-Identifier: MIT

//! acknowledge meets no unchanged kernel. The core has not acknowledged the epoch, and its TLB
//! entries are not empty.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/kernel.rs	acknowledge	returns
//! refused: unchanged: post.acked(c as int) == pre.flush_epoch
//! refused: unchanged: post.tlb@[c as int] == Set::<TlbEntry>::empty()

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::AcknowledgeReturns for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize) {}
}

} // verus!
