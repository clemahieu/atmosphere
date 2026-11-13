// SPDX-License-Identifier: MIT

//! The throwaway of `witness_root_prints`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::boot::*;
use crate::capability::boot_image::*;
use crate::capability::boot_kernel::*;
use crate::capability::boot_memory::*;
use crate::capability::boot_table::*;
use crate::capability::decompose::*;
use crate::capability::delete::*;
use crate::capability::derive::*;
use crate::capability::destroy::*;
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
use crate::capability::position::*;
use crate::capability::process::*;
use crate::capability::reach::*;
use crate::capability::reclaim::*;
use crate::capability::reclaim_process::*;
use crate::capability::reclaim_thread::*;
use crate::capability::refs::*;
use crate::capability::retype::*;
use crate::capability::revoke::*;
use crate::capability::space::*;
use crate::capability::steps::*;
use crate::capability::switch::*;
use crate::arch::{user_frame, user_rip, Registers};
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::define::*;
use crate::capability::witness::*;

impl CapKernel {
    pub fn throwaway_root_prints(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        kernel_root: Ghost<usize>,
        a: u64,
        b: u64,
        c: u64,
        d: u64,
        e: u64,
    )
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@, kernel_root@),
        ensures
            false,
    {
        self.witness_root_prints(root, process, leaf, frames, t, free, image, untyped, frame, present, kernel_root, a, b, c, d, e);
    }
}

} // verus!
