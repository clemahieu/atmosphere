// SPDX-License-Identifier: MIT

//! add_devices's success meets no unchanged kernel. The call is allowed, the device table was empty,
//! boot gave at least one device, and nothing was written, so the count is not that number and the
//! records are not the devices boot gave.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/device.rs	add_devices	true
//! refused: unchanged: ret ==> post.devices.count == count
//! refused: unchanged: ret ==> forall|k: int| 0 <= k < count ==> #[trigger] post.devices.records@[k] == unbound_record(devices@[k])

use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::capability::device::{DeviceInfo, MAX_DEVICES};
use crate::capability::kernel::CapKernel;

impl super::AddDevicesOk for () {
    proof fn unchanged(
        pre: CapKernel,
        post: CapKernel,
        first: usize,
        root: usize,
        slot: usize,
        devices: &Array<DeviceInfo, MAX_DEVICES>,
        count: usize,
        pre_steps: nat,
        post_steps: nat,
        ret: bool,
    ) {
    }
}

} // verus!
