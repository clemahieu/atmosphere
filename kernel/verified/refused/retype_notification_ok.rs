// SPDX-License-Identifier: MIT

//! retype_notification's success meets no unchanged kernel: the free page is still free, so it is not a live notification.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/endpoint.rs	retype_notification	true
//! refused: unchanged: ret ==> CapKernel::queue_retyped(pre, post, root, from, to, base, CapKind::Notification)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::RetypeNotificationOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: usize, base: usize, ret: bool) {}
}

} // verus!
