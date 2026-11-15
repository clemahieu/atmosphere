// SPDX-License-Identifier: MIT

//! unbind_device_at's success meets no unchanged kernel. The call is allowed and nothing was written,
//! so the flush epoch did not advance and the view's binds still name the device.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/device.rs	unbind_device_at	true
//! refused: unchanged: ret ==> CapKernel::device_unbound(pre, post, binding_node(&pre.devices, device_of(pre.payload_of(pre.tables.node_of(root, i)).base)))
//! refused: unchanged: ret ==> post.view().binds == pre.view().binds.remove(pre.payload_of(pre.tables.node_of(root, i)).base)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::UnbindDeviceOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, pre_steps: nat, post_steps: nat, ret: bool) {}
}

} // verus!
