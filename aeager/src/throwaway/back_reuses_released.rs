// SPDX-License-Identifier: MIT

//! The throwaway of `witness_back_reuses_released`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_basic};
use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;
use acall::step::{caller_alone, slot_names_own_space, Caller};
use aheap::allocator::Allocator;
use aheap::arch::*;
use aheap::heap::{class_for, small_layout};
use aheap::source::*;
use verified::capability::block::Large;
use verified::capability::kernel::CapKernel;
use verified::capability::operation::{
    status_only, Outcome, RETYPE_FRAME, RETYPE_LARGE_FRAME, STATUS_AGAIN, STATUS_OK, STATUS_REFUSED,
};
use verified::capability::inspect::CAP_KIND_FRAME;
use verified::capability::position::{lemma_position_own, spec_position};
use verified::capability::retype::FRAME_RIGHTS;
use verified::capability::table::TABLE_INDICES;
use verified::capability::zero::level_pages;
use verified::define::{PAGES_PER_2M, PAGE_SZ};
use crate::allocator::*;
use crate::apart::{
    lemma_kernel_source_ready_parts, lemma_other_source_ready, lemma_other_window_unclaimed,
    lemma_steps_keep_retype_frame_allowed, lemma_steps_keep_slot_names_own_space, process_ready,
    sources_apart,
};
use crate::eager::*;
use crate::bootcheck::*;
use crate::glue::{
    AcallStep, acall_ok, acall_steps, flush_room, lemma_acall_ok_append, lemma_acall_refused_after_ok,
    lemma_acall_steps_append, lemma_acall_steps_claimed, lemma_caller_alone_split, lemma_source_ready_premises,
    lemma_window_still_unclaimed, lemma_window_unclaimed, names_own_space, own_process, source_ready, window_tokens_clear,
};
use crate::invoke::{call_keeps_slot_space, call_keeps_source, is_source_slot, GuardedCall, invoke};
use crate::{Eager, MAX_PAGES, REGION_BYTES, TABLE_PAGES, WINDOW_BLOCKS};

verus! {

use crate::witness::*;

pub fn throwaway_back_reuses_released(
    space: u64,
    untyped: u64,
    memory: u64,
    slots: u64,
    window: *mut u8,
    token: &mut Tracked<Caller>,
)
    requires
        old(token)@.pages_wf(),
        old(token)@.history().len() > 0,
        old(token)@.kernel() == old(token)@.start(),
        window_tokens_clear(old(token)@, window@.addr),
        source_ready(old(token)@, space, untyped, memory, (3 * TABLE_PAGES + 1) as usize, slots, window@.addr),
    ensures
        false,
{
    witness_back_reuses_released(space, untyped, memory, slots, window, token);
}

} // verus!
