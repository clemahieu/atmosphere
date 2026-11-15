// SPDX-License-Identifier: MIT

//! map_device's success meets no unchanged kernel. The call is allowed and nothing was written, so
//! neither a page nor a large page was mapped into the device space.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/device_space.rs	map_device	true
//! refused: unchanged: ret && r.large() ==> CapKernel::map_large_done(pre, post, root, slot, r.path(), from, page)
//! refused: unchanged: ret && !r.large() ==> CapKernel::map_done(pre, post, root, slot, r.path(), from, page)

use vstd::prelude::*;

verus! {

use crate::capability::device_space::DeviceRange;
use crate::capability::kernel::CapKernel;

impl super::MapDeviceOk for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, slot: usize, r: DeviceRange, from: usize, page: usize, ret: bool) {}
}

} // verus!
