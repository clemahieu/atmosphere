// SPDX-License-Identifier: MIT

//! bind_device's success meets no unchanged kernel. The call is allowed and nothing was written, so
//! the binding node did not become a child of the space and the view's binds did not gain the device.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/device.rs	bind_device	true
//! refused: unchanged: ret ==> CapKernel::device_bound(pre, post, pre.tables.node_of(root, j), device_of(pre.payload_of(pre.tables.node_of(root, i)).base))
//! refused: unchanged: ret ==> post.view().binds == pre.view().binds.insert(pre.payload_of(pre.tables.node_of(root, i)).base, pre.payload_of(pre.tables.node_of(root, j)).base)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::BindDeviceOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, j: usize, ret: bool) {}
}

} // verus!
