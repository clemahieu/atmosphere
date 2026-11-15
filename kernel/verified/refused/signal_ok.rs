// SPDX-License-Identifier: MIT

//! signal's success meets no unchanged kernel: the call is allowed, the badge sets a bit the word
//! does not hold, and the word was not written.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/notification.rs	signal	true
//! refused: unchanged: ret ==> CapKernel::signalled(pre, post, root, i)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::SignalOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, ret: bool) {}
}

} // verus!
