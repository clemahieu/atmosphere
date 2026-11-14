// SPDX-License-Identifier: MIT

//! The throwaway of `witness_kernel_init`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::capability::block::*;
use crate::capability::boot::*;
use crate::capability::boot_image::*;
use crate::capability::boot_kernel::*;
use crate::capability::boot_memory::*;
use crate::capability::boot_table::*;
use crate::capability::cpu::*;
use crate::capability::decompose::*;
use crate::capability::delete::*;
use crate::capability::derive::*;
use crate::capability::destroy::*;
use crate::capability::endpoint::*;
use crate::capability::device_space::{device_path, device_range_bytes, DeviceRange};
use crate::capability::guest_space::{guest_path, guest_range_bytes, GuestPhysRange};
use crate::capability::device::{
    binding_device, binding_node, bound_record, device_of, device_payload, lemma_device_object, devices_wf, DeviceInfo, IOMMU_DEVICES, MAX_DEVICES,
};
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::map::*;
use crate::capability::mapping::*;
use crate::capability::operation::Outcome;
use crate::capability::position::*;
use crate::capability::process::*;
use crate::capability::reach::*;
use crate::capability::reclaim::*;
use crate::capability::reclaim_process::*;
use crate::capability::reclaim_thread::*;
use crate::capability::refs::*;
use crate::capability::reply::*;
use crate::capability::retype::*;
use crate::capability::revoke::*;
use crate::capability::schedule::*;
use crate::capability::space::*;
use crate::capability::steps::*;
use crate::capability::switch::*;
use crate::arch::{partial_frame, saved_frame, user_frame, user_rip, FrameKind, Registers};
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::define::*;
use crate::capability::witness::*;

impl CapKernel {
    pub fn throwaway_kernel_init(
        &mut self,
        pages: Tracked<Map<usize, PagePerm4k>>,
        registers: Tracked<Map<int, crate::arch::BaseRegister>>,
        tlb: Tracked<crate::arch::TlbModel>,
        iotlb: Tracked<crate::arch::IotlbModel>,
    )
        requires
            forall|i: usize| 2 <= i <= 17 ==> #[trigger] holds(pages@, i),
            boot_registers(registers@, PAGE_SZ),
            boot_tlb(tlb@),
            boot_iotlb(iotlb@),
        ensures
            false,
    {
        self.witness_kernel_init(pages, registers, tlb, iotlb);
    }
}

} // verus!
