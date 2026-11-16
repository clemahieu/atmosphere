// SPDX-License-Identifier: MIT

//! retype_endpoint's success meets no unchanged kernel: the free page is still free, so it is not a live endpoint.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/endpoint.rs	retype_endpoint	true
//! refused: unchanged: ret ==> CapKernel::queue_retyped(pre, post, root, from, to, base, CapKind::Endpoint)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::RetypeEndpointOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: usize, base: usize, ret: bool) {}
}

} // verus!
