// SPDX-License-Identifier: MIT

//! The throwaway of `witness_new`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_basic};
use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;
use acall::step::{caller_alone, Caller};
use aheap::arch::*;
use aheap::source::*;
use verified::capability::operation::STATUS_REFUSED;
use verified::capability::table::TABLE_INDICES;
use crate::eager::*;
use crate::exercise::*;
use crate::glue::{
    AcallStep, acall_ok, acall_steps, flush_room, lemma_acall_ok_append, lemma_acall_refused_after_ok,
    lemma_acall_steps_append, lemma_caller_alone_split, lemma_source_ready_premises,
    names_own_space, own_process, source_ready,
};
use crate::{Eager, MAX_PAGES, REGION_BYTES, TABLE_PAGES, WINDOW_BLOCKS};

verus! {

use crate::witness::*;

pub fn throwaway_new(space: u64, untyped: u64, window: *mut u8)
    requires
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
    ensures
        false,
{
    witness_new(space, untyped, window);
}

} // verus!
