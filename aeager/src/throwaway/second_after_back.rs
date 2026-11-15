// SPDX-License-Identifier: MIT

//! The throwaway of `witness_second_after_back`: its parameters, its requires, one call of it and the
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
use crate::allocator::*;
use crate::apart::{lemma_other_source_ready, lemma_other_window_unclaimed, process_ready, sources_apart};
use crate::eager::*;
use crate::exercise::*;
use crate::glue::{
    AcallStep, acall_ok, acall_steps, flush_room, lemma_acall_ok_append, lemma_acall_refused_after_ok,
    lemma_acall_steps_append, lemma_acall_steps_claimed, lemma_caller_alone_split, lemma_source_ready_premises,
    lemma_window_still_unclaimed, lemma_window_unclaimed, names_own_space, own_process, source_ready, window_tokens_clear,
};
use crate::{Eager, MAX_PAGES, REGION_BYTES, TABLE_PAGES, WINDOW_BLOCKS};

verus! {

use crate::witness::*;

pub fn throwaway_second_after_back(
    space: u64,
    untyped: u64,
    memory: u64,
    slots: u64,
    window: *mut u8,
    second_untyped: u64,
    second_memory: u64,
    second_slots: u64,
    second_window: *mut u8,
    token: &mut Tracked<Caller>,
)
    requires
        old(token)@.pages_wf(),
        old(token)@.kernel() == old(token)@.start(),
        window_tokens_clear(old(token)@, window@.addr),
        window_tokens_clear(old(token)@, second_window@.addr),
        source_ready(old(token)@, space, untyped, memory, ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as usize, slots, window@.addr),
        source_ready(
            old(token)@,
            space,
            second_untyped,
            second_memory,
            ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as usize,
            second_slots,
            second_window@.addr,
        ),
        sources_apart(
            memory,
            ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as usize,
            slots,
            window@.addr,
            second_memory,
            ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as usize,
            second_slots,
            second_window@.addr,
        ),
    ensures
        false,
{
    witness_second_after_back(space, untyped, memory, slots, window, second_untyped, second_memory, second_slots, second_window, token);
}

} // verus!
