// SPDX-License-Identifier: MIT

//! The throwaway of `witness_slab_pair`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::layout::*;
use vstd::raw_ptr::*;
use crate::arch::*;
use crate::buddy::*;
use crate::class::*;
use crate::large::*;
use crate::heap::{Heap, class_for, part_refused, run_order};
use crate::page::*;
use crate::record::{RecordStore, back_refused, gave_back, page_refused, record_page, took_page};
use crate::slab::*;
use crate::small::*;
use crate::source::*;

verus! {

use crate::witness::*;

pub fn throwaway_slab_pair(
    first: *mut u8,
    first_run: Tracked<PointsToRaw>,
    second: *mut u8,
    second_run: Tracked<PointsToRaw>,
)
    requires
        first@.addr % PAGE_BYTES == 0,
        second@.addr % PAGE_BYTES == 0,
        first@.addr + PAGE_BYTES <= second@.addr,
        second@.addr + PAGE_BYTES <= usize::MAX,
        first_run@.is_range(first@.addr as int, PAGE_BYTES as int),
        first_run@.provenance() == first@.provenance,
        second_run@.is_range(second@.addr as int, PAGE_BYTES as int),
        second_run@.provenance() == second@.provenance,
    ensures
        false,
{
    witness_slab_pair(first, first_run, second, second_run);
}

} // verus!
