// SPDX-License-Identifier: MIT

//! The throwaway of `witness_root_reads_presence_down_its_path`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

use crate::capability::boot::*;
use crate::capability::boot_image::*;
use crate::capability::boot_memory::*;
use crate::capability::boot_table::*;
use crate::capability::decompose::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::map::*;
use crate::capability::mapping::*;
use crate::capability::presence::*;
use crate::capability::probe::mask_bit;
use crate::capability::space::*;
use crate::capability::steps::*;
use crate::capability::table::*;
use crate::capability::witness::*;
use crate::define::*;
use crate::capability::presence_witness::*;

impl CapKernel {
    pub fn throwaway_root_reads_presence_down_its_path(
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
        base: usize,
        l4: usize,
    )
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@, kernel_root@),
            image_tables_bound(image@) + 4 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
            KERNEL_MEM_END_L4INDEX <= l4 < ENTRIES / 2,
            !image_l4(image@, l4),
        ensures
            false,
    {
        self.witness_root_reads_presence_down_its_path(root, process, leaf, frames, t, free, image, untyped, frame, present, kernel_root, base, l4);
    }
}

} // verus!
