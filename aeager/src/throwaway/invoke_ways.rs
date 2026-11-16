// SPDX-License-Identifier: MIT

//! The throwaway of `witness_invoke_ways`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_basic};
use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;
use acall::step::{caller_alone, Caller};
use aheap::allocator::Allocator;
use aheap::arch::*;
use aheap::heap::{class_for, small_layout};
use aheap::source::*;
use verified::capability::block::Large;
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
use crate::apart::{lemma_other_source_ready, lemma_other_window_unclaimed, process_ready, sources_apart};
use crate::eager::*;
use crate::exercise::*;
use crate::glue::{
    AcallStep, acall_ok, acall_steps, flush_room, lemma_acall_ok_append, lemma_acall_refused_after_ok,
    lemma_acall_steps_append, lemma_acall_steps_claimed, lemma_caller_alone_split, lemma_source_ready_premises,
    lemma_window_still_unclaimed, lemma_window_unclaimed, names_own_space, own_process, source_ready, window_tokens_clear,
};
use crate::invoke::{GuardedCall, invoke};
use crate::{Eager, MAX_PAGES, REGION_BYTES, TABLE_PAGES, WINDOW_BLOCKS};

verus! {

use crate::witness::*;

pub fn throwaway_invoke_ways(
    space: u64,
    untyped: u64,
    window: *mut u8,
    other_untyped: u64,
    big_base: u64,
    big_slot: u64,
    frame_base: u64,
    slot: u64,
    token: Tracked<Caller>,
)
    requires
        space < TABLE_INDICES,
        token@.pages_wf(),
        token@.kernel() == token@.start(),
        window_tokens_clear(token@, window@.addr),
        source_ready(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr),
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
        other_untyped < TABLE_INDICES,
        other_untyped != untyped,
        big_slot < TABLE_INDICES,
        big_slot != space,
        big_slot != untyped,
        big_slot as int > frame_slot(1, (MAX_PAGES - 1) as int),
        slot < TABLE_INDICES,
        slot != space,
        slot != untyped,
        slot != big_slot,
        slot as int > frame_slot(1, (MAX_PAGES - 1) as int),
        token@.kernel().retype_allowed(token@.root(), RETYPE_LARGE_FRAME, other_untyped as usize, big_base as usize, big_slot, 0),
        !token@.kernel().zeroing.active(Large::Two, big_base as usize / PAGE_SZ / level_pages(Large::Two)),
        token@.kernel().retype_allowed(token@.root(), RETYPE_FRAME, other_untyped as usize, frame_base as usize, slot, 0),
        frame_base as usize / PAGE_SZ / PAGES_PER_2M != big_base as usize / PAGE_SZ / PAGES_PER_2M,
        frame_base <= usize::MAX as u64,
    ensures
        false,
{
    witness_invoke_ways(space, untyped, window, other_untyped, big_base, big_slot, frame_base, slot, token);
}

} // verus!
