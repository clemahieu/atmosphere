// SPDX-License-Identifier: MIT

//! flush_iommu meets no unchanged kernel. The IOMMU has not acknowledged the epoch and its model
//! of the IOTLB is not empty.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/kernel.rs	flush_iommu	returns
//! refused: unchanged: post.iommu_acked(i as int) == pre.flush_epoch
//! refused: unchanged: post.iommus.tlb@[i as int] == Set::<TlbEntry>::empty()

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::FlushIommuReturns for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, i: usize) {}
}

} // verus!
