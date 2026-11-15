// SPDX-License-Identifier: MIT

//! charge meets no unchanged kernel once the counter has moved: the entry notes the reading it was
//! given, and this core's since is not that reading.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/charge.rs	charge	returns
//! refused: unchanged: CapKernel::charged_entry(pre, post, c as int, now)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::ChargeReturns for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, now: u64) {}
}

} // verus!
