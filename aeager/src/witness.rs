// SPDX-License-Identifier: MIT

//! The witnesses: verified sequences of operations, built into no image, that reach the uses the
//! eager span source exists for.
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
use crate::exercise::*;
use crate::glue::{
    AcallStep, acall_ok, acall_steps, flush_room, lemma_acall_ok_append, lemma_acall_refused_after_ok,
    lemma_acall_steps_append, lemma_acall_steps_claimed, lemma_caller_alone_split, lemma_source_ready_premises,
    lemma_window_still_unclaimed, lemma_window_unclaimed, names_own_space, own_process, source_ready, window_tokens_clear,
};
use crate::invoke::{call_keeps_slot_space, call_keeps_source, is_source_slot, GuardedCall, invoke};
use crate::{Eager, MAX_PAGES, REGION_BYTES, TABLE_PAGES, WINDOW_BLOCKS};

verus! {

/// Constructs an eager source of `MAX_PAGES` pages over a region-aligned window.
pub fn witness_new(space: u64, untyped: u64, window: *mut u8, token: &mut Tracked<Caller>) -> (r: Option<Eager>)
    requires
        old(token)@.pages_wf(),
        old(token)@.kernel() == old(token)@.start(),
        window_tokens_clear(old(token)@, window@.addr),
        source_ready(old(token)@, space, untyped, 0, MAX_PAGES, 1, window@.addr),
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
    ensures
        r is Some,
{
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
        lemma_window_unclaimed(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr);
    }
    Eager::new(token, space, untyped, 0, MAX_PAGES, 1, window)
}

/// Constructs an eager source of `MAX_PAGES` pages over a region-aligned window in the caller's own
/// space and bundles it into an `Allocator<Eager>`.
pub fn witness_new_allocator(space: u64, untyped: u64, window: *mut u8, token: Tracked<Caller>) -> (r: AllocatorInit)
    requires
        token@.pages_wf(),
        token@.kernel() == token@.start(),
        window_tokens_clear(token@, window@.addr),
        source_ready(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr),
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
    ensures
        r is Ready,
{
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
        lemma_source_ready_premises(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr);
        lemma_window_unclaimed(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr);
    }
    new_allocator(token, 0, space, untyped, 0, MAX_PAGES, 1, window)
}

/// Constructs an eager source of `MAX_PAGES` pages over a region-aligned window in the caller's own
/// space and exercises it, as dom0 does at boot.
pub fn witness_exercise(space: u64, untyped: u64, window: *mut u8, token: &mut Tracked<Caller>) -> (seen: Exercised)
    requires
        old(token)@.pages_wf(),
        old(token)@.kernel() == old(token)@.start(),
        window_tokens_clear(old(token)@, window@.addr),
        source_ready(old(token)@, space, untyped, 0, MAX_PAGES, 1, window@.addr),
        old(token)@.wf(),
        own_process(old(token)@),
        names_own_space(old(token)@, space),
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
    ensures
        final(token)@.wf(),
{
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
        lemma_window_unclaimed(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr);
    }
    let mut source = Eager::new(token, space, untyped, 0, MAX_PAGES, 1, window).unwrap();
    let seen = exercise(&mut source, token);
    seen
}

/// Builds and exercises an eager source of `MAX_PAGES` pages over a region-aligned window in the
/// caller's own space in one call, as dom0 does at boot.
pub fn witness_exercise_eager(space: u64, untyped: u64, window: *mut u8, token: &mut Tracked<Caller>) -> (seen: Option<Exercised>)
    requires
        old(token)@.pages_wf(),
        old(token)@.kernel() == old(token)@.start(),
        window_tokens_clear(old(token)@, window@.addr),
        source_ready(old(token)@, space, untyped, 0, MAX_PAGES, 1, window@.addr),
        old(token)@.wf(),
        own_process(old(token)@),
        names_own_space(old(token)@, space),
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
    ensures
        seen is Some,
        final(token)@.wf(),
        final(token)@.pages_wf(),
        own_process(final(token)@),
{
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
        lemma_window_unclaimed(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr);
    }
    exercise_eager(token, space, untyped, 0, MAX_PAGES, 1, window)
}

/// Reserves a one-block span from a fresh eager source over a region-aligned window.
pub fn witness_reserve(space: u64, untyped: u64, window: *mut u8, token: &mut Tracked<Caller>) -> (r: Option<*mut u8>)
    requires
        old(token)@.pages_wf(),
        old(token)@.kernel() == old(token)@.start(),
        window_tokens_clear(old(token)@, window@.addr),
        source_ready(old(token)@, space, untyped, 0, MAX_PAGES, 1, window@.addr),
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
        old(token)@.wf(),
        own_process(old(token)@),
        names_own_space(old(token)@, space),
    ensures
        r is Some,
{
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
        lemma_window_unclaimed(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr);
    }
    let mut src: Eager = Eager::new(token, space, untyped, 0, MAX_PAGES, 1, window).unwrap();
    src.reserve(token, 1)
}

/// Reserves a one-block span from a fresh eager source over a region-aligned window, releases it and
/// reserves again: the second reservation is granted at the base the first was, which the released
/// span held.
pub fn witness_release_span(space: u64, untyped: u64, window: *mut u8, token: &mut Tracked<Caller>) -> (r: (*mut u8, Option<*mut u8>))
    requires
        old(token)@.pages_wf(),
        old(token)@.kernel() == old(token)@.start(),
        window_tokens_clear(old(token)@, window@.addr),
        source_ready(old(token)@, space, untyped, 0, MAX_PAGES, 1, window@.addr),
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
        old(token)@.wf(),
        own_process(old(token)@),
        names_own_space(old(token)@, space),
    ensures
        r.1 is Some,
        r.1->0@.addr == r.0@.addr,
{
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
        lemma_window_unclaimed(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr);
    }
    let mut src: Eager = Eager::new(token, space, untyped, 0, MAX_PAGES, 1, window).unwrap();
    proof {
        assert(src.window_fits(0, 1));
    }
    let first = src.reserve(token, 1).unwrap();
    src.release_span(token, first.addr());
    proof {
        assert(src@.spans =~= Map::<int, Span>::empty());
        assert(src.window_fits(0, 1));
    }
    let again = src.reserve(token, 1);
    (first, again)
}

/// Reserves a one-block span from a fresh eager source over an unmapped level-4 window and backs its
/// first page: every `acall` step stays within the source's window, slots and untyped, a refusal comes
/// only from `acall` refusing the final non-`Inspect` step, and when no other caller steps between the
/// calls `back` makes, the back is granted.
#[verifier::spinoff_prover]
pub fn witness_back(
    space: u64,
    untyped: u64,
    memory: u64,
    slots: u64,
    window: *mut u8,
    token: &mut Tracked<Caller>,
) -> (r: (Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>))
    requires
        old(token)@.pages_wf(),
        old(token)@.kernel() == old(token)@.start(),
        window_tokens_clear(old(token)@, window@.addr),
        source_ready(old(token)@, space, untyped, memory, ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as usize, slots, window@.addr),
    ensures
        final(token)@.wf(),
        acall_steps(old(token)@, final(token)@, r.1@),
        forall|k: int| 0 <= k < r.1@.len() ==> acall_call_in_window(
            #[trigger] r.1@[k],
            space,
            untyped,
            memory,
            ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as usize,
            slots,
            window@.addr,
            window@.addr as int,
            1,
        ),
        r.0 is None ==> {
            &&& r.1@.len() > 0
            &&& acall_ok(r.1@.drop_last())
            &&& r.1@.last().out.status == STATUS_REFUSED
        },
        caller_alone(old(token)@, final(token)@) ==> r.0 is Some,
{
    let pages: usize = (2 + WINDOW_BLOCKS) * TABLE_PAGES + 1;
    let ghost tok0 = token@;
    proof {
        lemma_source_ready_premises(token@, space, untyped, memory, pages, slots, window@.addr);
        lemma_window_unclaimed(token@, space, untyped, memory, pages, slots, window@.addr);
        assert(pages <= MAX_PAGES) by (compute);
        assert(pages as int - (2 + WINDOW_BLOCKS as int) * TABLE_PAGES as int >= 1) by (compute);
    }
    let mut src: Eager = Eager::new(token, space, untyped, memory, pages, slots, window).unwrap();
    let ghost made = token@;
    proof {
        assert(src.window_fits(0, 1));
    }
    let span = src.reserve(token, 1).unwrap();
    let addr = span.addr();
    proof {
        assert(addr == window@.addr);
        let q = addr as int / BLOCK_BYTES as int;
        lemma_fundamental_div_mod(addr as int, BLOCK_BYTES as int);
        assert(addr as int == (q * BLOCK_PAGES as int) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                addr as int == BLOCK_BYTES as int * q,
                BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
        ;
        lemma_mod_multiples_basic(q * BLOCK_PAGES as int, PAGE_BYTES as int);
        assert(1 * PAGE_BYTES <= span_bytes(1)) by (compute);
        assert(src@.runs_in(addr as int, addr as int, 1));
        assert(src@.unbacked(addr as int, addr as int, 1));
        assert(src.acall_trace() == Seq::<AcallStep>::empty());
    }
    let got = src.back(token, Ghost(addr as int), addr, 1);
    let ghost steps = src.acall_trace();
    proof {
        assert(src.acall_trace().skip(0) =~= steps);
        lemma_acall_steps_claimed(tok0, made, token@, steps);
    }
    (got, Ghost(steps))
}

/// Reserves a one-block span from a fresh eager source over an unmapped level-4 window, backs its first
/// page, releases it and backs it again: the release parks the page with no system call, so when no
/// other caller steps between the calls of the first back, `release` runs and the second back is granted
/// the same page with no system call.
#[verifier::spinoff_prover]
pub fn witness_release(
    space: u64,
    untyped: u64,
    memory: u64,
    slots: u64,
    window: *mut u8,
    token: &mut Tracked<Caller>,
) -> (r: (Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>))
    requires
        old(token)@.pages_wf(),
        old(token)@.kernel() == old(token)@.start(),
        window_tokens_clear(old(token)@, window@.addr),
        source_ready(old(token)@, space, untyped, memory, ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as usize, slots, window@.addr),
    ensures
        final(token)@.wf(),
        acall_steps(old(token)@, final(token)@, r.1@),
        caller_alone(old(token)@, final(token)@) ==> r.0 is Some,
        r.0 is Some ==> r.0->0@.is_range(window@.addr as int, PAGE_BYTES as int),
{
    let pages: usize = (2 + WINDOW_BLOCKS) * TABLE_PAGES + 1;
    let ghost tok0 = token@;
    proof {
        lemma_source_ready_premises(token@, space, untyped, memory, pages, slots, window@.addr);
        lemma_window_unclaimed(token@, space, untyped, memory, pages, slots, window@.addr);
        assert(pages <= MAX_PAGES) by (compute);
        assert(pages as int - (2 + WINDOW_BLOCKS as int) * TABLE_PAGES as int >= 1) by (compute);
    }
    let mut src: Eager = Eager::new(token, space, untyped, memory, pages, slots, window).unwrap();
    let ghost made = token@;
    proof {
        assert(src.window_fits(0, 1));
    }
    let span = src.reserve(token, 1).unwrap();
    let addr = span.addr();
    proof {
        assert(addr == window@.addr);
        let q = addr as int / BLOCK_BYTES as int;
        lemma_fundamental_div_mod(addr as int, BLOCK_BYTES as int);
        assert(addr as int == (q * BLOCK_PAGES as int) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                addr as int == BLOCK_BYTES as int * q,
                BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
        ;
        lemma_mod_multiples_basic(q * BLOCK_PAGES as int, PAGE_BYTES as int);
        assert(1 * PAGE_BYTES <= span_bytes(1)) by (compute);
        assert(src@.runs_in(addr as int, addr as int, 1));
        assert(src@.unbacked(addr as int, addr as int, 1));
        assert(src.acall_trace() == Seq::<AcallStep>::empty());
    }
    let ghost reserved = src@;
    let got = src.back(token, Ghost(addr as int), addr, 1);
    let ghost steps = src.acall_trace();
    proof {
        assert(src.acall_trace().skip(0) =~= steps);
        lemma_acall_steps_claimed(tok0, made, token@, steps);
    }
    if got.is_none() {
        return (got, Ghost(steps));
    }
    let perm = got.unwrap();
    src.release(token, Ghost(addr as int), addr, 1, perm);
    proof {
        assert(src@.spans[addr as int].backed =~= reserved.spans[addr as int].backed);
        assert(src@.spans =~= reserved.spans);
    }
    let again = src.back(token, Ghost(addr as int), addr, 1);
    (again, Ghost(steps))
}

/// Constructs an eager source of `3 * TABLE_PAGES + 1` pages (below `free_capacity`), reserves a
/// one-block span, backs its first page, checks that backing its second page is refused while no frame
/// remains, releases the first page, and backs the second page: when no other caller steps between, the
/// released frame is unmapped and mapped at the second address.
#[verifier::spinoff_prover]
pub fn witness_back_reuses_released(
    space: u64,
    untyped: u64,
    memory: u64,
    slots: u64,
    window: *mut u8,
    token: &mut Tracked<Caller>,
) -> (r: (Option<Tracked<PointsToRaw>>, Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>))
    requires
        old(token)@.pages_wf(),
        old(token)@.kernel() == old(token)@.start(),
        window_tokens_clear(old(token)@, window@.addr),
        source_ready(old(token)@, space, untyped, memory, (3 * TABLE_PAGES + 1) as usize, slots, window@.addr),
    ensures
        final(token)@.wf(),
        acall_steps(old(token)@, final(token)@, r.2@),
        forall|k: int| 0 <= k < r.2@.len() ==> acall_call_in_window(
            #[trigger] r.2@[k],
            space,
            untyped,
            memory,
            (3 * TABLE_PAGES + 1) as usize,
            slots,
            window@.addr,
            window@.addr as int,
            2,
        ),
        r.0 is None,
        r.1 is None ==> {
            &&& r.2@.len() > 0
            &&& acall_ok(r.2@.drop_last())
            &&& r.2@.last().out.status == STATUS_REFUSED
        },
        caller_alone(old(token)@, final(token)@) ==> r.1 is Some,
{
    let pages: usize = 3 * TABLE_PAGES + 1;
    let ghost tok0 = token@;
    proof {
        lemma_source_ready_premises(token@, space, untyped, memory, pages, slots, window@.addr);
        lemma_window_unclaimed(token@, space, untyped, memory, pages, slots, window@.addr);
        assert(pages <= MAX_PAGES) by (compute);
        assert((3 * TABLE_PAGES + 1) / TABLE_PAGES as int == 3) by (compute);
        assert(2 * PAGE_BYTES <= BLOCK_BYTES) by (compute);
    }
    let mut src: Eager = Eager::new(token, space, untyped, memory, pages, slots, window).unwrap();
    let ghost made = token@;
    proof {
        assert(src.window_fits(0, 1));
    }
    let span = src.reserve(token, 1).unwrap();
    let addr = span.addr();
    let next = addr + PAGE_BYTES;
    proof {
        assert(addr == window@.addr);
        let q = addr as int / BLOCK_BYTES as int;
        lemma_fundamental_div_mod(addr as int, BLOCK_BYTES as int);
        assert(addr as int == (q * BLOCK_PAGES as int) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                addr as int == BLOCK_BYTES as int * q,
                BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
        ;
        lemma_mod_multiples_basic(q * BLOCK_PAGES as int, PAGE_BYTES as int);
        assert((next as int) == (q * BLOCK_PAGES as int + 1) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                addr as int == (q * BLOCK_PAGES as int) * PAGE_BYTES as int,
                next == addr + PAGE_BYTES,
        ;
        lemma_mod_multiples_basic(q * BLOCK_PAGES as int + 1, PAGE_BYTES as int);
        assert(2 * PAGE_BYTES <= span_bytes(1)) by (compute);
        assert(src@.runs_in(addr as int, addr as int, 1));
        assert(src@.unbacked(addr as int, addr as int, 1));
        assert(src.acall_trace() == Seq::<AcallStep>::empty());
        assert(run_touches_block(addr, addr as int, 1, 0));
        assert(!run_touches_block(addr, addr as int, 1, 1));
        assert(!run_touches_block(addr, addr as int, 1, 2));
        assert(!run_touches_block(addr, addr as int, 1, 3));
        assert(src.unlinked_tables_on(addr as int, 1) == 3);
        assert(!src.parks(addr as int));
        assert(src.parked_pages(addr as int, 0) == 0);
        assert(src.parked_pages(addr as int, 1) == 0);
        assert(src.unparked_pages(addr as int, 0) == 0);
        assert(src.unparked_pages(addr as int, 1) == 1);
        assert(src.can_back(addr as int, 1));
    }
    let ghost reserved = src@;
    let got = src.back(token, Ghost(addr as int), addr, 1);
    let ghost steps1 = src.acall_trace();
    proof {
        assert(src.acall_trace().skip(0) =~= steps1);
        lemma_acall_steps_claimed(tok0, made, token@, steps1);
        assert forall|va: int| #[trigger] run_pages(addr as int, 1).contains(va)
            implies run_pages(addr as int, 2).contains(va) by {};
        assert forall|k: int| 0 <= k < steps1.len() implies acall_call_in_window(
            #[trigger] steps1[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window@.addr,
            window@.addr as int,
            2,
        ) by {
            assert(acall_call_in_window(steps1[k], space, untyped, memory, pages, slots, addr, addr as int, 1));
            reveal(acall_call_in_window);
        }
    }
    if got.is_none() {
        return (None, got, Ghost(steps1));
    }
    let perm = got.unwrap();
    let ghost tok1 = token@;
    proof {
        assert(src@.runs_in(addr as int, next as int, 1));
        assert(!reserved.spans[addr as int].backed.contains(next as int));
        assert(!run_pages(addr as int, 1).contains(next as int));
        assert(src@.unbacked(addr as int, next as int, 1));
        assert(run_touches_block(addr, next as int, 1, 0));
        assert(!run_touches_block(addr, next as int, 1, 1));
        assert(!run_touches_block(addr, next as int, 1, 2));
        assert(!run_touches_block(addr, next as int, 1, 3));
        assert(src.block_tabled(0));
        assert(src.unlinked_tables_on(next as int, 1) == 0);
        assert(src.free_frames() == 0);
    }
    let short = src.back(token, Ghost(addr as int), next, 1);
    proof {
        if caller_alone(tok0, tok1) {
            assert(src.ready(tok1));
        }
        let n1 = steps1.len() as int;
        assert(src.acall_trace().take(n1) == steps1);
        assert(src.acall_trace().skip(n1) == Seq::<AcallStep>::empty());
        assert(src.acall_trace() =~= steps1);
        assert(src.block_tabled(0));
        assert(!src.parks(next as int));
        assert(src@.runs_in(addr as int, addr as int, 1));
        assert(src@.backed(addr as int, addr as int, 1));
    }
    src.release(token, Ghost(addr as int), addr, 1, perm);
    proof {
        assert(src@.spans[addr as int].backed =~= reserved.spans[addr as int].backed);
        assert(src@.spans =~= reserved.spans);
        assert(src@.runs_in(addr as int, next as int, 1));
        assert(src@.unbacked(addr as int, next as int, 1));
        assert(!run_pages(addr as int, 1).contains(next as int));
        assert(!src.parks(next as int));
        assert(src.block_tabled(0));
        assert(src.unlinked_tables_on(next as int, 1) == 0);
        assert(src.parked_pages(next as int, 0) == 0);
        assert(src.parked_pages(next as int, 1) == 0);
        assert(src.unparked_pages(next as int, 0) == 0);
        assert(src.unparked_pages(next as int, 1) == 1);
        assert(src.free_frames() == 1);
        assert(src.can_back(next as int, 1));
        if caller_alone(tok0, tok1) {
            assert(src.ready(tok1));
            assert(flush_room(tok1, 1));
        }
    }
    let reused = src.back(token, Ghost(addr as int), next, 1);
    let ghost steps = src.acall_trace();
    proof {
        let n1 = steps1.len() as int;
        let steps2 = steps.skip(n1);
        assert(steps.take(n1) == steps1);
        assert(steps =~= steps1 + steps2);
        lemma_acall_steps_append(tok0, tok1, token@, steps1, steps2);
        lemma_acall_ok_append(steps1, steps2);
        if caller_alone(tok0, token@) {
            lemma_caller_alone_split(tok0, tok1, token@, steps1, steps2);
        }
        if reused.is_none() {
            lemma_acall_refused_after_ok(steps1, steps2);
        }
        assert forall|va: int| #[trigger] run_pages(next as int, 1).contains(va)
            implies run_pages(addr as int, 2).contains(va) by {};
        assert forall|k: int| 0 <= k < steps.len() implies acall_call_in_window(
            #[trigger] steps[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window@.addr,
            window@.addr as int,
            2,
        ) by {
            if k < n1 {
                assert(steps[k] == steps1[k]);
            } else {
                assert(steps[k] == steps2[k - n1]);
                assert(acall_call_in_window(steps2[k - n1], space, untyped, memory, pages, slots, addr, next as int, 1));
                reveal(acall_call_in_window);
            }
        }
    }
    (short, reused, Ghost(steps))
}

/// Constructs an eager source of `3 * TABLE_PAGES + 1` pages (below `free_capacity`), reserves a
/// one-block span, backs its first page, releases that page, gives up the span with `release_span`,
/// reserves a one-block span again, and backs its second page: `release_span` keeps the token, the
/// configuration, the linked tables, the parked and free frames and the `acall` trace, so when no other
/// caller steps between, the final back is granted.
#[verifier::spinoff_prover]
pub fn witness_back_after_release_span(
    space: u64,
    untyped: u64,
    memory: u64,
    slots: u64,
    window: *mut u8,
    token: &mut Tracked<Caller>,
) -> (r: (Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>))
    requires
        old(token)@.pages_wf(),
        old(token)@.kernel() == old(token)@.start(),
        window_tokens_clear(old(token)@, window@.addr),
        source_ready(old(token)@, space, untyped, memory, (3 * TABLE_PAGES + 1) as usize, slots, window@.addr),
    ensures
        final(token)@.wf(),
        acall_steps(old(token)@, final(token)@, r.1@),
        forall|k: int| 0 <= k < r.1@.len() ==> acall_call_in_window(
            #[trigger] r.1@[k],
            space,
            untyped,
            memory,
            (3 * TABLE_PAGES + 1) as usize,
            slots,
            window@.addr,
            window@.addr as int,
            2,
        ),
        r.0 is None ==> {
            &&& r.1@.len() > 0
            &&& acall_ok(r.1@.drop_last())
            &&& r.1@.last().out.status == STATUS_REFUSED
        },
        caller_alone(old(token)@, final(token)@) ==> r.0 is Some,
        r.0 is Some ==> r.0->0@.is_range((window@.addr + PAGE_BYTES) as int, PAGE_BYTES as int),
{
    let pages: usize = 3 * TABLE_PAGES + 1;
    let ghost tok0 = token@;
    proof {
        lemma_source_ready_premises(token@, space, untyped, memory, pages, slots, window@.addr);
        lemma_window_unclaimed(token@, space, untyped, memory, pages, slots, window@.addr);
        assert(pages <= MAX_PAGES) by (compute);
        assert((3 * TABLE_PAGES + 1) / TABLE_PAGES as int == 3) by (compute);
        assert(2 * PAGE_BYTES <= BLOCK_BYTES) by (compute);
    }
    let mut src: Eager = Eager::new(token, space, untyped, memory, pages, slots, window).unwrap();
    let ghost made = token@;
    proof {
        assert(src.window_fits(0, 1));
    }
    let first = src.reserve(token, 1).unwrap();
    let addr = first.addr();
    proof {
        assert(addr == window@.addr);
        let q = addr as int / BLOCK_BYTES as int;
        lemma_fundamental_div_mod(addr as int, BLOCK_BYTES as int);
        assert(addr as int == (q * BLOCK_PAGES as int) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                addr as int == BLOCK_BYTES as int * q,
                BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
        ;
        lemma_mod_multiples_basic(q * BLOCK_PAGES as int, PAGE_BYTES as int);
        assert(2 * PAGE_BYTES <= span_bytes(1)) by (compute);
        assert(src@.runs_in(addr as int, addr as int, 1));
        assert(src@.unbacked(addr as int, addr as int, 1));
        assert(src.acall_trace() == Seq::<AcallStep>::empty());
        assert(run_touches_block(addr, addr as int, 1, 0));
        assert(!run_touches_block(addr, addr as int, 1, 1));
        assert(!run_touches_block(addr, addr as int, 1, 2));
        assert(!run_touches_block(addr, addr as int, 1, 3));
        assert(src.unlinked_tables_on(addr as int, 1) == 3);
        assert(!src.parks(addr as int));
        assert(src.parked_pages(addr as int, 0) == 0);
        assert(src.parked_pages(addr as int, 1) == 0);
        assert(src.unparked_pages(addr as int, 0) == 0);
        assert(src.unparked_pages(addr as int, 1) == 1);
        assert(src.can_back(addr as int, 1));
    }
    let ghost reserved = src@;
    let got = src.back(token, Ghost(addr as int), addr, 1);
    let ghost steps1 = src.acall_trace();
    proof {
        assert(src.acall_trace().skip(0) =~= steps1);
        lemma_acall_steps_claimed(tok0, made, token@, steps1);
        assert forall|va: int| #[trigger] run_pages(addr as int, 1).contains(va)
            implies run_pages(addr as int, 2).contains(va) by {};
        assert forall|k: int| 0 <= k < steps1.len() implies acall_call_in_window(
            #[trigger] steps1[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window@.addr,
            window@.addr as int,
            2,
        ) by {
            assert(acall_call_in_window(steps1[k], space, untyped, memory, pages, slots, addr, addr as int, 1));
            reveal(acall_call_in_window);
        }
    }
    if got.is_none() {
        return (got, Ghost(steps1));
    }
    let perm = got.unwrap();
    let ghost tok1 = token@;
    proof {
        assert(src@.runs_in(addr as int, addr as int, 1));
        assert(src@.backed(addr as int, addr as int, 1));
    }
    src.release(token, Ghost(addr as int), addr, 1, perm);
    proof {
        assert(src@.spans[addr as int].backed =~= reserved.spans[addr as int].backed);
        assert(src@.spans =~= reserved.spans);
    }
    src.release_span(token, addr);
    proof {
        assert(src@.spans =~= Map::<int, Span>::empty());
        assert(src.window_fits(0, 1));
    }
    let second = src.reserve(token, 1).unwrap();
    let addr2 = second.addr();
    let next = addr2 + PAGE_BYTES;
    proof {
        assert(addr2 == addr);
        let q = addr as int / BLOCK_BYTES as int;
        lemma_fundamental_div_mod(addr as int, BLOCK_BYTES as int);
        assert(addr as int == (q * BLOCK_PAGES as int) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                addr as int == BLOCK_BYTES as int * q,
                BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
        ;
        assert((next as int) == (q * BLOCK_PAGES as int + 1) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                addr as int == (q * BLOCK_PAGES as int) * PAGE_BYTES as int,
                next == addr2 + PAGE_BYTES,
                addr2 == addr,
        ;
        lemma_mod_multiples_basic(q * BLOCK_PAGES as int + 1, PAGE_BYTES as int);
        assert(2 * PAGE_BYTES <= span_bytes(1)) by (compute);
        assert(src@.runs_in(addr2 as int, next as int, 1));
        assert(src@.unbacked(addr2 as int, next as int, 1));
        assert(!run_pages(addr as int, 1).contains(next as int));
        assert(!src.parks(next as int));
        assert(run_touches_block(addr2, next as int, 1, 0));
        assert(!run_touches_block(addr2, next as int, 1, 1));
        assert(!run_touches_block(addr2, next as int, 1, 2));
        assert(!run_touches_block(addr2, next as int, 1, 3));
        assert(src.block_tabled(0));
        assert(src.unlinked_tables_on(next as int, 1) == 0);
        assert(src.parked_pages(next as int, 0) == 0);
        assert(src.parked_pages(next as int, 1) == 0);
        assert(src.unparked_pages(next as int, 0) == 0);
        assert(src.unparked_pages(next as int, 1) == 1);
        assert(src.free_frames() == 1);
        assert(src.can_back(next as int, 1));
        if caller_alone(tok0, tok1) {
            assert(src.ready(tok1));
            assert(flush_room(tok1, 1));
        }
    }
    let again = src.back(token, Ghost(addr2 as int), next, 1);
    let ghost steps = src.acall_trace();
    proof {
        let n1 = steps1.len() as int;
        let steps2 = steps.skip(n1);
        assert(steps.take(n1) == steps1);
        assert(steps =~= steps1 + steps2);
        lemma_acall_steps_append(tok0, tok1, token@, steps1, steps2);
        lemma_acall_ok_append(steps1, steps2);
        if caller_alone(tok0, token@) {
            lemma_caller_alone_split(tok0, tok1, token@, steps1, steps2);
        }
        if again.is_none() {
            lemma_acall_refused_after_ok(steps1, steps2);
        }
        assert forall|va: int| #[trigger] run_pages(next as int, 1).contains(va)
            implies run_pages(addr as int, 2).contains(va) by {};
        assert forall|k: int| 0 <= k < steps.len() implies acall_call_in_window(
            #[trigger] steps[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window@.addr,
            window@.addr as int,
            2,
        ) by {
            if k < n1 {
                assert(steps[k] == steps1[k]);
            } else {
                assert(steps[k] == steps2[k - n1]);
                assert(acall_call_in_window(steps2[k - n1], space, untyped, memory, pages, slots, addr2, next as int, 1));
                reveal(acall_call_in_window);
            }
        }
    }
    (again, Ghost(steps))
}

/// Constructs an eager source of `5 * TABLE_PAGES` pages (below `free_capacity`), reserves a
/// two-block span and backs the first page of each block. The first back links the window's path
/// and the first block's table and breaks at most one more free block for its frame, so a free block
/// remains for the second block's table and enough frames beyond it: when no other caller steps
/// between, both backs are granted.
#[verifier::spinoff_prover]
pub fn witness_back_second_block(
    space: u64,
    untyped: u64,
    memory: u64,
    slots: u64,
    window: *mut u8,
    token: &mut Tracked<Caller>,
) -> (r: (Option<Tracked<PointsToRaw>>, Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>))
    requires
        old(token)@.pages_wf(),
        old(token)@.kernel() == old(token)@.start(),
        window_tokens_clear(old(token)@, window@.addr),
        source_ready(old(token)@, space, untyped, memory, (5 * TABLE_PAGES) as usize, slots, window@.addr),
    ensures
        final(token)@.wf(),
        acall_steps(old(token)@, final(token)@, r.2@),
        forall|k: int| 0 <= k < r.2@.len() ==> acall_call_in_window(
            #[trigger] r.2@[k],
            space,
            untyped,
            memory,
            (5 * TABLE_PAGES) as usize,
            slots,
            window@.addr,
            window@.addr as int,
            (BLOCK_PAGES + 1) as nat,
        ),
        r.0 is None ==> r.1 is None,
        r.1 is None ==> {
            &&& r.2@.len() > 0
            &&& acall_ok(r.2@.drop_last())
            &&& r.2@.last().out.status == STATUS_REFUSED
        },
        caller_alone(old(token)@, final(token)@) ==> r.0 is Some,
        caller_alone(old(token)@, final(token)@) ==> r.1 is Some,
{
    let pages: usize = 5 * TABLE_PAGES;
    let ghost tok0 = token@;
    proof {
        lemma_source_ready_premises(token@, space, untyped, memory, pages, slots, window@.addr);
        lemma_window_unclaimed(token@, space, untyped, memory, pages, slots, window@.addr);
        assert(pages <= MAX_PAGES) by (compute);
        assert((5 * TABLE_PAGES) / TABLE_PAGES as int == 5) by (compute);
        assert(BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES);
        assert(PAGE_BYTES < BLOCK_BYTES) by (compute);
        assert(WINDOW_BYTES == 4 * BLOCK_BYTES) by (compute);
    }
    let mut src: Eager = Eager::new(token, space, untyped, memory, pages, slots, window).unwrap();
    let ghost made = token@;
    proof {
        assert(src.window_fits(0, 2));
    }
    let span = src.reserve(token, 2).unwrap();
    let addr = span.addr();
    let next = addr + BLOCK_BYTES;
    proof {
        assert(addr == window@.addr);
        let q = addr as int / BLOCK_BYTES as int;
        lemma_fundamental_div_mod(addr as int, BLOCK_BYTES as int);
        assert(addr as int == (q * BLOCK_PAGES as int) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                addr as int == BLOCK_BYTES as int * q,
                BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
        ;
        lemma_mod_multiples_basic(q * BLOCK_PAGES as int, PAGE_BYTES as int);
        assert((next as int) == (q * BLOCK_PAGES as int + BLOCK_PAGES as int) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                addr as int == (q * BLOCK_PAGES as int) * PAGE_BYTES as int,
                next == addr + BLOCK_BYTES,
                BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
        ;
        lemma_mod_multiples_basic(q * BLOCK_PAGES as int + BLOCK_PAGES as int, PAGE_BYTES as int);
        assert(span_bytes(2) == 2 * BLOCK_BYTES as int);
        assert(src@.runs_in(addr as int, addr as int, 1));
        assert(src@.unbacked(addr as int, addr as int, 1));
        assert(src.acall_trace() == Seq::<AcallStep>::empty());
        assert(run_touches_block(addr, addr as int, 1, 0));
        assert(!run_touches_block(addr, addr as int, 1, 1));
        assert(!run_touches_block(addr, addr as int, 1, 2));
        assert(!run_touches_block(addr, addr as int, 1, 3));
        assert(src.unlinked_tables_on(addr as int, 1) == 3);
        assert(!src.parks(addr as int));
        assert(src.parked_pages(addr as int, 0) == 0);
        assert(src.parked_pages(addr as int, 1) == 0);
        assert(src.unparked_pages(addr as int, 0) == 0);
        assert(src.unparked_pages(addr as int, 1) == 1);
        assert(src.can_back(addr as int, 1));
    }
    let ghost reserved = src@;
    let first = src.back(token, Ghost(addr as int), addr, 1);
    let ghost steps1 = src.acall_trace();
    proof {
        assert(src.acall_trace().skip(0) =~= steps1);
        lemma_acall_steps_claimed(tok0, made, token@, steps1);
        assert forall|va: int| #[trigger] run_pages(addr as int, 1).contains(va)
            implies run_pages(addr as int, (BLOCK_PAGES + 1) as nat).contains(va) by {};
        assert forall|k: int| 0 <= k < steps1.len() implies acall_call_in_window(
            #[trigger] steps1[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window@.addr,
            window@.addr as int,
            (BLOCK_PAGES + 1) as nat,
        ) by {
            assert(acall_call_in_window(steps1[k], space, untyped, memory, pages, slots, addr, addr as int, 1));
            reveal(acall_call_in_window);
        }
    }
    if first.is_none() {
        return (None, None, Ghost(steps1));
    }
    let ghost tok1 = token@;
    proof {
        assert(src@.runs_in(addr as int, next as int, 1));
        assert(!reserved.spans[addr as int].backed.contains(next as int));
        assert(!run_pages(addr as int, 1).contains(next as int));
        assert(src@.unbacked(addr as int, next as int, 1));
        assert(!run_touches_block(addr, next as int, 1, 0));
        assert(run_touches_block(addr, next as int, 1, 1));
        assert(!run_touches_block(addr, next as int, 1, 2));
        assert(!run_touches_block(addr, next as int, 1, 3));
        assert(src.top_linked());
        assert(src.middle_linked());
        assert(!src.block_tabled(1));
        assert(src.unlinked_tables_on(next as int, 1) == 1);
        assert(src.free_table_blocks() >= 1);
        assert(src.free_frames() == 5 * TABLE_PAGES - 3 * TABLE_PAGES - 1);
        assert(!src.parks(next as int));
        assert(src.parked_pages(next as int, 0) == 0);
        assert(src.parked_pages(next as int, 1) == 0);
        assert(src.unparked_pages(next as int, 0) == 0);
        assert(src.unparked_pages(next as int, 1) == 1);
        assert(src.can_back(next as int, 1));
        if caller_alone(tok0, tok1) {
            assert(src.ready(tok1));
            assert(flush_room(tok1, 1));
        }
    }
    let second = src.back(token, Ghost(addr as int), next, 1);
    let ghost steps = src.acall_trace();
    proof {
        let n1 = steps1.len() as int;
        let steps2 = steps.skip(n1);
        assert(steps.take(n1) == steps1);
        assert(steps =~= steps1 + steps2);
        lemma_acall_steps_append(tok0, tok1, token@, steps1, steps2);
        lemma_acall_ok_append(steps1, steps2);
        if caller_alone(tok0, token@) {
            lemma_caller_alone_split(tok0, tok1, token@, steps1, steps2);
        }
        if second.is_none() {
            lemma_acall_refused_after_ok(steps1, steps2);
        }
        assert forall|va: int| #[trigger] run_pages(next as int, 1).contains(va)
            implies run_pages(addr as int, (BLOCK_PAGES + 1) as nat).contains(va) by {
            assert((BLOCK_PAGES + 1) as int * PAGE_BYTES as int == BLOCK_BYTES as int + PAGE_BYTES as int) by (compute);
        };
        assert forall|k: int| 0 <= k < steps.len() implies acall_call_in_window(
            #[trigger] steps[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window@.addr,
            window@.addr as int,
            (BLOCK_PAGES + 1) as nat,
        ) by {
            if k < n1 {
                assert(steps[k] == steps1[k]);
            } else {
                assert(steps[k] == steps2[k - n1]);
                assert(acall_call_in_window(steps2[k - n1], space, untyped, memory, pages, slots, addr, next as int, 1));
                reveal(acall_call_in_window);
            }
        }
    }
    (first, second, Ghost(steps))
}

/// Makes the two sources of `witness_two_sources`, both before any back, and reserves a one-block span at
/// the base of each window: making the second claims page tokens for its own window's paths alone, so
/// that window is unclaimed still after the first is made, and the first still serves the caller and
/// is ready after the second is made, which took no step.
fn two_sources_reserved(
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
) -> (r: (Eager, Eager))
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
        window@.addr != second_window@.addr,
    ensures
        final(token)@.kernel() == old(token)@.kernel(),
        final(token)@.root() == old(token)@.root(),
        final(token)@.history() == old(token)@.history(),
        r.0.serves(final(token)@),
        r.1.serves(final(token)@),
        r.0.space() == space,
        r.1.space() == space,
        r.0@.wf(),
        r.1@.wf(),
        r.0.ready(final(token)@),
        forall|a: int| !#[trigger] r.0.parks(a),
        r.0.fresh(),
        r.1.fresh(),
        r.0.untyped() == untyped,
        r.0.memory() == memory,
        r.0.pages() == ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as usize,
        r.0.slots() == slots,
        r.0.window() == window@.addr,
        r.1.untyped() == second_untyped,
        r.1.memory() == second_memory,
        r.1.pages() == ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as usize,
        r.1.slots() == second_slots,
        r.1.window() == second_window@.addr,
        r.0.free_capacity() >= 1,
        r.1.free_capacity() >= 1,
        r.0.acall_trace() == Seq::<AcallStep>::empty(),
        r.1.acall_trace() == Seq::<AcallStep>::empty(),
        window@.addr as int % PAGE_BYTES as int == 0,
        second_window@.addr as int % PAGE_BYTES as int == 0,
        r.0@.runs_in(window@.addr as int, window@.addr as int, 1),
        r.0@.unbacked(window@.addr as int, window@.addr as int, 1),
        r.1@.runs_in(second_window@.addr as int, second_window@.addr as int, 1),
        r.1@.unbacked(second_window@.addr as int, second_window@.addr as int, 1),
{
    let pages: usize = (2 + WINDOW_BLOCKS) * TABLE_PAGES + 1;
    let ghost tok0 = token@;
    proof {
        lemma_source_ready_premises(token@, space, untyped, memory, pages, slots, window@.addr);
        lemma_source_ready_premises(token@, space, second_untyped, second_memory, pages, second_slots, second_window@.addr);
        lemma_window_unclaimed(token@, space, untyped, memory, pages, slots, window@.addr);
        lemma_window_unclaimed(token@, space, second_untyped, second_memory, pages, second_slots, second_window@.addr);
        assert(pages <= MAX_PAGES) by (compute);
        assert(pages as int - (2 + WINDOW_BLOCKS as int) * TABLE_PAGES as int >= 1) by (compute);
    }
    let mut first: Eager = Eager::new(token, space, untyped, memory, pages, slots, window).unwrap();
    let ghost made_first = token@;
    proof {
        lemma_window_still_unclaimed(tok0, made_first, window@.addr, second_window@.addr);
    }
    let mut second: Eager = Eager::new(token, space, second_untyped, second_memory, pages, second_slots, second_window).unwrap();
    let ghost made = token@;
    proof {
        first.lemma_holds_claimed(made_first, made);
        assert(source_ready(made, space, untyped, memory, pages, slots, window@.addr));
        assert(first.window_fits(0, 1));
        assert(second.window_fits(0, 1));
    }
    let span = first.reserve(token, 1).unwrap();
    let second_span = second.reserve(token, 1).unwrap();
    let addr = span.addr();
    let second_addr = second_span.addr();
    proof {
        assert(addr == window@.addr);
        assert(second_addr == second_window@.addr);
        let q = addr as int / BLOCK_BYTES as int;
        lemma_fundamental_div_mod(addr as int, BLOCK_BYTES as int);
        assert(addr as int == (q * BLOCK_PAGES as int) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                addr as int == BLOCK_BYTES as int * q,
                BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
        ;
        lemma_mod_multiples_basic(q * BLOCK_PAGES as int, PAGE_BYTES as int);
        let q2 = second_addr as int / BLOCK_BYTES as int;
        lemma_fundamental_div_mod(second_addr as int, BLOCK_BYTES as int);
        assert(second_addr as int == (q2 * BLOCK_PAGES as int) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                second_addr as int == BLOCK_BYTES as int * q2,
                BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
        ;
        lemma_mod_multiples_basic(q2 * BLOCK_PAGES as int, PAGE_BYTES as int);
        assert(1 * PAGE_BYTES <= span_bytes(1)) by (compute);
        assert(first@.runs_in(addr as int, addr as int, 1));
        assert(first@.unbacked(addr as int, addr as int, 1));
        assert(second@.runs_in(second_addr as int, second_addr as int, 1));
        assert(second@.unbacked(second_addr as int, second_addr as int, 1));
    }
    (first, second)
}

/// Constructs two eager sources over windows at two level-4 entries, both before any back, reserves a
/// one-block span from each and backs its first page: making the second source claims page tokens for
/// its own window's paths alone, so that window is unclaimed still after the first is made, and the
/// first source still serves the caller and is ready after the second is made. When no other caller
/// steps between the backs' calls, both are granted: the first back's steps, in its own window, untyped
/// run and frame slots, leave the second source ready. Each back is refused only when `acall` refuses
/// its last step.
#[verifier::spinoff_prover]
pub fn witness_two_sources(
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
) -> (r: (Option<Tracked<PointsToRaw>>, Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>, Ghost<Seq<AcallStep>>))
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
        window@.addr != second_window@.addr,
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
        final(token)@.wf(),
        acall_steps(old(token)@, final(token)@, r.2@ + r.3@),
        r.0 is None ==> {
            &&& r.2@.len() > 0
            &&& acall_ok(r.2@.drop_last())
            &&& r.2@.last().out.status == STATUS_REFUSED
        },
        r.1 is None ==> {
            &&& r.3@.len() > 0
            &&& acall_ok(r.3@.drop_last())
            &&& r.3@.last().out.status == STATUS_REFUSED
        },
        caller_alone(old(token)@, final(token)@) ==> r.0 is Some && r.1 is Some,
        r.0 is Some ==> r.0->0@.is_range(window@.addr as int, PAGE_BYTES as int),
        r.1 is Some ==> r.1->0@.is_range(second_window@.addr as int, PAGE_BYTES as int),
{
    let ghost tok0 = token@;
    let ghost pages = ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as usize;
    let (mut first, mut second) = two_sources_reserved(
        space,
        untyped,
        memory,
        slots,
        window,
        second_untyped,
        second_memory,
        second_slots,
        second_window,
        token,
    );
    let ghost made = token@;
    let addr = window.addr();
    let second_addr = second_window.addr();
    let got = first.back(token, Ghost(addr as int), addr, 1);
    let ghost steps = first.acall_trace();
    let ghost backed = token@;
    proof {
        assert(first.acall_trace().skip(0) =~= steps);
        lemma_acall_steps_claimed(tok0, made, backed, steps);
        second.lemma_fresh_held(&first, made, backed);
    }
    let second_got = second.back(token, Ghost(second_addr as int), second_addr, 1);
    let ghost second_steps = second.acall_trace();
    proof {
        assert(second.acall_trace().skip(0) =~= second_steps);
        lemma_acall_steps_append(tok0, backed, token@, steps, second_steps);
        if caller_alone(tok0, token@) {
            lemma_caller_alone_split(tok0, backed, token@, steps, second_steps);
            assert(caller_alone(made, backed));
            assert(first.ready(backed));
            first.lemma_ready_process(backed);
            assert(process_ready(backed.kernel(), tok0.root()));
            lemma_other_source_ready(
                tok0, backed, steps, space, untyped, memory, pages, slots, window@.addr, addr as int, 1,
                second_untyped, second_memory, pages, second_slots, second_window@.addr,
            );
        }
    }
    (got, second_got, Ghost(steps), Ghost(second_steps))
}

/// Constructs an eager source over a window at one level-4 entry, reserves a one-block span and backs its
/// first page, then constructs a second source over a window at another level-4 entry, from another
/// untyped run into other frame slots, reserves a one-block span from it and backs its first page: the
/// first back's steps, whoever stepped between them, add to the caller's space only at the first
/// window's level-4 entry, so the second window is unclaimed still and the second source can be made
/// after the first backed. When no other caller steps between the backs' calls, both are granted; each
/// back is refused only when `acall` refuses its last step.
#[verifier::spinoff_prover]
pub fn witness_second_after_back(
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
) -> (r: (Option<Tracked<PointsToRaw>>, Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>, Ghost<Seq<AcallStep>>))
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
        final(token)@.wf(),
        acall_steps(old(token)@, final(token)@, r.2@ + r.3@),
        r.0 is None ==> {
            &&& r.2@.len() > 0
            &&& acall_ok(r.2@.drop_last())
            &&& r.2@.last().out.status == STATUS_REFUSED
        },
        r.1 is None ==> {
            &&& r.3@.len() > 0
            &&& acall_ok(r.3@.drop_last())
            &&& r.3@.last().out.status == STATUS_REFUSED
        },
        caller_alone(old(token)@, final(token)@) ==> r.0 is Some && r.1 is Some,
        r.0 is Some ==> r.0->0@.is_range(window@.addr as int, PAGE_BYTES as int),
        r.1 is Some ==> r.1->0@.is_range(second_window@.addr as int, PAGE_BYTES as int),
{
    let pages: usize = (2 + WINDOW_BLOCKS) * TABLE_PAGES + 1;
    let ghost tok0 = token@;
    proof {
        lemma_source_ready_premises(token@, space, untyped, memory, pages, slots, window@.addr);
        lemma_source_ready_premises(token@, space, second_untyped, second_memory, pages, second_slots, second_window@.addr);
        lemma_window_unclaimed(token@, space, untyped, memory, pages, slots, window@.addr);
        lemma_window_unclaimed(token@, space, second_untyped, second_memory, pages, second_slots, second_window@.addr);
        assert(pages <= MAX_PAGES) by (compute);
        assert(pages as int - (2 + WINDOW_BLOCKS as int) * TABLE_PAGES as int >= 1) by (compute);
    }
    let mut first: Eager = Eager::new(token, space, untyped, memory, pages, slots, window).unwrap();
    let ghost made = token@;
    proof {
        lemma_window_still_unclaimed(tok0, made, window@.addr, second_window@.addr);
        assert(source_ready(made, space, untyped, memory, pages, slots, window@.addr));
        assert(first.window_fits(0, 1));
    }
    let span = first.reserve(token, 1).unwrap();
    let addr = span.addr();
    proof {
        assert(addr == window@.addr);
        let q = addr as int / BLOCK_BYTES as int;
        lemma_fundamental_div_mod(addr as int, BLOCK_BYTES as int);
        assert(addr as int == (q * BLOCK_PAGES as int) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                addr as int == BLOCK_BYTES as int * q,
                BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
        ;
        lemma_mod_multiples_basic(q * BLOCK_PAGES as int, PAGE_BYTES as int);
        assert(1 * PAGE_BYTES <= span_bytes(1)) by (compute);
        assert(first@.runs_in(addr as int, addr as int, 1));
        assert(first@.unbacked(addr as int, addr as int, 1));
        assert(first.acall_trace() == Seq::<AcallStep>::empty());
        assert(PAGE_BYTES <= WINDOW_BYTES) by (compute);
    }
    let got = first.back(token, Ghost(addr as int), addr, 1);
    let ghost steps = first.acall_trace();
    let ghost backed = token@;
    proof {
        assert(first.acall_trace().skip(0) =~= steps);
        lemma_acall_steps_claimed(tok0, made, backed, steps);
        lemma_other_window_unclaimed(
            made, backed, steps, space, untyped, memory, pages, slots, window@.addr, addr as int, 1,
            second_window@.addr,
        );
        first.lemma_holds_pages_wf(backed);
    }
    let mut second: Eager = Eager::new(token, space, second_untyped, second_memory, pages, second_slots, second_window).unwrap();
    proof {
        assert(second.window_fits(0, 1));
    }
    let second_span = second.reserve(token, 1).unwrap();
    let second_addr = second_span.addr();
    let ghost reserved = token@;
    proof {
        assert(second_addr == second_window@.addr);
        let q2 = second_addr as int / BLOCK_BYTES as int;
        lemma_fundamental_div_mod(second_addr as int, BLOCK_BYTES as int);
        assert(second_addr as int == (q2 * BLOCK_PAGES as int) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                second_addr as int == BLOCK_BYTES as int * q2,
                BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
        ;
        lemma_mod_multiples_basic(q2 * BLOCK_PAGES as int, PAGE_BYTES as int);
        assert(1 * PAGE_BYTES <= span_bytes(1)) by (compute);
        assert(second@.runs_in(second_addr as int, second_addr as int, 1));
        assert(second@.unbacked(second_addr as int, second_addr as int, 1));
        assert(second.acall_trace() == Seq::<AcallStep>::empty());
    }
    let second_got = second.back(token, Ghost(second_addr as int), second_addr, 1);
    let ghost second_steps = second.acall_trace();
    proof {
        assert(second.acall_trace().skip(0) =~= second_steps);
        lemma_acall_steps_claimed(backed, reserved, token@, second_steps);
        lemma_acall_steps_append(tok0, backed, token@, steps, second_steps);
        if caller_alone(tok0, token@) {
            lemma_caller_alone_split(tok0, backed, token@, steps, second_steps);
            assert(caller_alone(made, backed));
            assert(first.ready(backed));
            first.lemma_ready_process(backed);
            assert(process_ready(backed.kernel(), tok0.root()));
            lemma_other_source_ready(
                tok0, backed, steps, space, untyped, memory, pages, slots, window@.addr, addr as int, 1,
                second_untyped, second_memory, pages, second_slots, second_window@.addr,
            );
            assert(caller_alone(reserved, token@));
            assert(source_ready(reserved, space, second_untyped, second_memory, pages, second_slots, second_window@.addr));
        }
    }
    (got, second_got, Ghost(steps), Ghost(second_steps))
}

/// Bundles an eager source into an `Allocator<Eager>`, runs an allowed inspection and a guarded
/// source-slot deletion through `invoke`, and then allocates from the heap, proving `serves` holds
/// across both.
pub fn witness_invoke(space: u64, untyped: u64, window: *mut u8, token: Tracked<Caller>) -> (r: (
    Allocator<Eager>,
    Outcome,
    Outcome,
    bool,
    Ghost<Caller>,
))
    requires
        space < TABLE_INDICES,
        token@.pages_wf(),
        token@.kernel() == token@.start(),
        window_tokens_clear(token@, window@.addr),
        source_ready(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr),
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
    ensures
        r.0.held(),
        caller_alone(token@, r.4@) ==> r.1.status == STATUS_OK,
        caller_alone(token@, r.4@) ==> r.1.result_2 == token@.root() as u64,
        r.2 == status_only(STATUS_REFUSED),
{
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
        lemma_source_ready_premises(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr);
        lemma_window_unclaimed(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr);
    }
    let AllocatorInit::Ready(mut alloc) = new_allocator(token, 0, space, untyped, 0, MAX_PAGES, 1, window) else {
        unreached()
    };
    let ok = invoke(&mut alloc, GuardedCall::Inspect { at: space });
    let ghost after_ok = alloc.token()->0;
    proof {
        assert(TABLE_INDICES <= verified::capability::position::POSITION_INDEX_MASK + 1) by (compute);
        verified::capability::position::lemma_position_own(space);
        if caller_alone(token@, after_ok) {
            let n = token@.history().len() as int;
            let added = after_ok.history().skip(n);
            assert(after_ok.history().take(n) == token@.history());
            assert(added =~= seq![(after_ok.entry(), after_ok.kernel())]);
            assert(added.len() == 1);
            assert(added[0] == (after_ok.entry(), after_ok.kernel()));
            assert(after_ok.entry() == token@.kernel());
        }
    }
    let refused = invoke(&mut alloc, GuardedCall::Delete { at: space });
    proof {
        alloc.lemma_wf();
        assert(small_layout(8, 8)) by (compute);
        assert(class_for(8, 8) == 0) by (compute);
    }
    let allocated = alloc.alloc(8, 8).is_some();
    (alloc, ok, refused, allocated, Ghost(after_ok))
}

/// Bundles an eager source into an `Allocator<Eager>`, begins zeroing a 2M frame from a second
/// untyped (`STATUS_AGAIN`), retypes a 4K frame from that untyped into a non-source slot
/// (`STATUS_OK`), and inspects the slot the retype filled (`STATUS_OK`), proving `invoke`
/// reaches both outcome ways and ties the token's kernel state to the `acall` contract across
/// successive calls.
pub fn witness_invoke_ways(
    space: u64,
    untyped: u64,
    window: *mut u8,
    other_untyped: u64,
    big_base: u64,
    big_slot: u64,
    frame_base: u64,
    slot: u64,
    token: Tracked<Caller>,
) -> (r: (
    Allocator<Eager>,
    Outcome,
    Outcome,
    Outcome,
))
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
        r.0.held(),
        r.0.token() is Some,
        caller_alone(token@, r.0.token()->0) ==> r.1.status == STATUS_AGAIN,
        caller_alone(token@, r.0.token()->0) ==> r.2.status == STATUS_OK,
        caller_alone(token@, r.0.token()->0) ==> r.3.status == STATUS_OK,
        caller_alone(token@, r.0.token()->0) ==> r.3.result_1 == CAP_KIND_FRAME,
        caller_alone(token@, r.0.token()->0) ==> r.3.result_2 == frame_base,
        caller_alone(token@, r.0.token()->0) ==> r.3.result_3 == 0,
        caller_alone(token@, r.0.token()->0) ==> r.3.result_4 == FRAME_RIGHTS as u64,
{
    let ghost tok0 = token@;
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
        lemma_source_ready_premises(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr);
        lemma_window_unclaimed(token@, space, untyped, 0, MAX_PAGES, 1, window@.addr);
    }
    let AllocatorInit::Ready(mut alloc) = new_allocator(token, 0, space, untyped, 0, MAX_PAGES, 1, window) else {
        unreached()
    };
    let ghost tok1 = alloc.token()->0;
    proof {
        assert forall|i: int| 0 <= i < MAX_PAGES implies frame_slot(1, i) < big_slot as int && frame_slot(1, i) < slot as int by {
            if i < MAX_PAGES - 1 {
                lemma_frame_slot(1, i, (MAX_PAGES - 1) as int);
            }
        };
    }
    let again = invoke(&mut alloc, GuardedCall::Retype { untyped: other_untyped, kind: RETYPE_LARGE_FRAME, base: big_base, word: big_slot, level: 0 });
    let ghost tok2 = alloc.token()->0;
    let retyped = invoke(&mut alloc, GuardedCall::Retype { untyped: other_untyped, kind: RETYPE_FRAME, base: frame_base, word: slot, level: 0 });
    let ghost tok3 = alloc.token()->0;
    proof {
        assert(TABLE_INDICES <= verified::capability::position::POSITION_INDEX_MASK + 1) by (compute);
        lemma_position_own(slot);
    }
    let inspected = invoke(&mut alloc, GuardedCall::Inspect { at: slot });
    let ghost tok4 = alloc.token()->0;
    proof {
        if caller_alone(tok0, tok4) {
            let n = tok0.history().len() as int;
            let added = tok4.history().skip(n);
            assert(tok4.history().take(n) == tok0.history());
            assert(added =~= seq![
                (tok2.entry(), tok2.kernel()),
                (tok3.entry(), tok3.kernel()),
                (tok4.entry(), tok4.kernel()),
            ]);
            assert(added.len() == 3);
            assert(added[0] == (tok2.entry(), tok2.kernel()));
            assert(added[1] == (tok3.entry(), tok3.kernel()));
            assert(added[2] == (tok4.entry(), tok4.kernel()));
            assert(tok2.entry() == tok0.kernel());
            assert(tok3.entry() == tok2.kernel());
            assert(tok4.entry() == tok3.kernel());
            let r_big = (big_base as usize) / PAGE_SZ / level_pages(Large::Two);
            let r_frame = (frame_base as usize) / PAGE_SZ / PAGES_PER_2M;
            assert(level_pages(Large::Two) == PAGES_PER_2M);
            assert(r_frame != r_big);
            assert(tok2.kernel().blocks.regions_2m@[r_frame as int] == tok0.kernel().blocks.regions_2m@[r_frame as int]);
            assert(tok2.kernel().retype_allowed(tok0.root(), RETYPE_FRAME, other_untyped as usize, frame_base as usize, slot, 0));
            assert(tok3.kernel().inspect_allowed(tok0.root(), spec_position(slot)));
        }
    }
    (alloc, again, retyped, inspected)
}

/// Constructs two eager sources over disjoint windows, untyped runs, frame slots and space slots,
/// backs one page of the second so it holds frames outside the first, bundles the first into an
/// `Allocator<Eager>` and runs an allowed `invoke` (`RETYPE_FRAME` into a slot outside both
/// sources): the post-state preserves `CapKernel::space_kept`, `CapKernel::count_kept`,
/// `slot_names_own_space` for slots the first source does not hold, and `second.serves` on the
/// returned token.
#[verifier::spinoff_prover]
pub fn witness_invoke_other_serves(
    space: u64,
    untyped: u64,
    memory: u64,
    slots: u64,
    window: *mut u8,
    second_space: u64,
    second_untyped: u64,
    second_memory: u64,
    second_slots: u64,
    second_window: *mut u8,
    other_untyped: u64,
    frame_base: u64,
    slot: u64,
    token: Tracked<Caller>,
) -> (r: (Allocator<Eager>, Eager, Option<Tracked<PointsToRaw>>, Outcome))
    requires
        space < TABLE_INDICES,
        second_space < TABLE_INDICES,
        second_space != space,
        second_space != untyped,
        forall|i: int| 0 <= i < ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as int
            ==> #[trigger] frame_slot(slots as int, i) != second_space as int,
        token@.pages_wf(),
        token@.kernel() == token@.start(),
        window_tokens_clear(token@, window@.addr),
        window_tokens_clear(token@, second_window@.addr),
        source_ready(token@, space, untyped, memory, ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as usize, slots, window@.addr),
        source_ready(
            token@,
            second_space,
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
        other_untyped < TABLE_INDICES,
        other_untyped != untyped,
        other_untyped != second_untyped,
        slot < TABLE_INDICES,
        slot != space,
        slot != second_space,
        slot != untyped,
        slot != second_untyped,
        forall|i: int| 0 <= i < ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as int
            ==> #[trigger] frame_slot(slots as int, i) != slot as int,
        forall|i: int| 0 <= i < ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as int
            ==> #[trigger] frame_slot(second_slots as int, i) != slot as int,
        (frame_base as int / PAGE_SZ as int) < second_memory as int / PAGE_SZ as int
            || (frame_base as int / PAGE_SZ as int)
                >= second_memory as int / PAGE_SZ as int + ((2 + WINDOW_BLOCKS) * TABLE_PAGES + 1) as int,
        token@.kernel().retype_allowed(token@.root(), RETYPE_FRAME, other_untyped as usize, frame_base as usize, slot, 0),
        frame_base <= usize::MAX as u64,
    ensures
        r.0.held(),
        r.0.token() is Some,
        r.1.serves(r.0.token()->0),
        CapKernel::space_kept(r.0.token()->0.entry(), r.0.token()->0.kernel(), r.0.token()->0.root()),
        CapKernel::count_kept(r.0.token()->0.entry(), r.0.token()->0.kernel(), r.0.token()->0.root()),
        forall|s: usize|
            !is_source_slot(&r.0.src(), s)
                && #[trigger] slot_names_own_space(token@.kernel(), token@.root(), s)
                ==> slot_names_own_space(r.0.token()->0.kernel(), r.0.token()->0.root(), s),
        caller_alone(token@, r.0.token()->0) ==> r.2 is Some && r.3.status == STATUS_OK,
{
    let pages: usize = (2 + WINDOW_BLOCKS) * TABLE_PAGES + 1;
    let mut token = token;
    let ghost tok0 = token@;
    proof {
        lemma_source_ready_premises(token@, space, untyped, memory, pages, slots, window@.addr);
        lemma_source_ready_premises(token@, second_space, second_untyped, second_memory, pages, second_slots, second_window@.addr);
        lemma_window_unclaimed(token@, space, untyped, memory, pages, slots, window@.addr);
        lemma_window_unclaimed(token@, second_space, second_untyped, second_memory, pages, second_slots, second_window@.addr);
        assert(pages <= MAX_PAGES) by (compute);
        assert(pages as int - (2 + WINDOW_BLOCKS as int) * TABLE_PAGES as int >= 1) by (compute);
    }
    let mut second: Eager = Eager::new(&mut token, second_space, second_untyped, second_memory, pages, second_slots, second_window).unwrap();
    let ghost made_second = token@;
    proof {
        lemma_window_still_unclaimed(tok0, made_second, second_window@.addr, window@.addr);
        assert(source_ready(made_second, second_space, second_untyped, second_memory, pages, second_slots, second_window@.addr));
        assert(second.window_fits(0, 1));
    }
    let second_span = second.reserve(&mut token, 1).unwrap();
    let second_addr = second_span.addr();
    let ghost reserved = token@;
    proof {
        assert(second_addr == second_window@.addr);
        let q = second_addr as int / BLOCK_BYTES as int;
        lemma_fundamental_div_mod(second_addr as int, BLOCK_BYTES as int);
        assert(second_addr as int == (q * BLOCK_PAGES as int) * PAGE_BYTES as int) by (nonlinear_arith)
            requires
                second_addr as int == BLOCK_BYTES as int * q,
                BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
        ;
        lemma_mod_multiples_basic(q * BLOCK_PAGES as int, PAGE_BYTES as int);
        assert(1 * PAGE_BYTES <= span_bytes(1)) by (compute);
        assert(second@.runs_in(second_addr as int, second_addr as int, 1));
        assert(second@.unbacked(second_addr as int, second_addr as int, 1));
        assert(second.acall_trace() == Seq::<AcallStep>::empty());
        assert(PAGE_BYTES <= WINDOW_BYTES) by (compute);
    }
    let second_got = second.back(&mut token, Ghost(second_addr as int), second_addr, 1);
    let ghost steps = second.acall_trace();
    let ghost backed = token@;
    proof {
        assert(second.acall_trace().skip(0) =~= steps);
        lemma_acall_steps_claimed(tok0, reserved, backed, steps);
        lemma_other_window_unclaimed(
            reserved, backed, steps, second_space, second_untyped, second_memory, pages, second_slots,
            second_window@.addr, second_addr as int, 1, window@.addr,
        );
        lemma_steps_keep_slot_names_own_space(
            tok0, backed, steps, second_space, second_untyped, second_memory, pages, second_slots,
            second_window@.addr, second_addr as int, 1,
        );
        assert(slot_names_own_space(tok0.kernel(), tok0.root(), space as usize));
        assert(slot_names_own_space(backed.kernel(), backed.root(), space as usize));
        assert(names_own_space(backed, space));
        second.lemma_holds_pages_wf(backed);
    }
    let AllocatorInit::Ready(mut alloc) = new_allocator(token, 0, space, untyped, memory, pages, slots, window) else {
        unreached()
    };
    let ghost made_alloc = alloc.token()->0;
    let call = GuardedCall::Retype {
        untyped: other_untyped,
        kind: RETYPE_FRAME,
        base: frame_base,
        word: slot,
        level: 0,
    };
    proof {
        second.lemma_holds_claimed(backed, made_alloc);
        assert(second.serves(made_alloc));
        assert(!is_source_slot(&alloc.src(), slot as usize));
        assert(!is_source_slot(&alloc.src(), second_space as usize));
        assert(!is_source_slot(&second, slot as usize));
        assert(call_keeps_source(&second, call));
    }
    let out = invoke(&mut alloc, call);
    let ghost post = alloc.token()->0;
    proof {
        alloc.lemma_wf();
        assert(slot_names_own_space(made_alloc.kernel(), made_alloc.root(), second_space as usize));
        assert(call_keeps_slot_space(made_alloc.kernel(), post.entry(), post.root(), call, second_space as usize));
        assert(slot_names_own_space(post.kernel(), post.root(), second_space as usize));
        second.lemma_invoke_serves(made_alloc, post, call, out);
        assert forall|s: usize|
            !is_source_slot(&alloc.src(), s)
                && #[trigger] slot_names_own_space(tok0.kernel(), tok0.root(), s)
            implies slot_names_own_space(post.kernel(), post.root(), s) by {
            assert(slot_names_own_space(backed.kernel(), backed.root(), s));
            assert(slot_names_own_space(made_alloc.kernel(), made_alloc.root(), s));
            assert(call_keeps_slot_space(made_alloc.kernel(), post.entry(), post.root(), call, s));
        };
        if caller_alone(tok0, post) {
            let n0 = tok0.history().len() as int;
            let n1 = backed.history().len() as int;
            let added = post.history().skip(n0);
            let b_added = backed.history().skip(n0);
            reveal(acall_steps);
            assert(n1 == n0 + steps.len());
            assert(post.history().len() == n1 + 1);
            assert(post.history().take(n1) == made_alloc.history());
            assert(made_alloc.history() == backed.history());
            assert(backed.history().take(n0) == tok0.history());
            assert(post.history().take(n0) == tok0.history());
            assert forall|k: int| 0 <= k < steps.len() implies
                b_added[k] == added[k]
                    && (#[trigger] b_added[k]).0 == (if k == 0 { tok0.kernel() } else { b_added[k - 1].1 }) by {
                assert(b_added[k] == backed.history()[n0 + k]);
                assert(added[k] == post.history()[n0 + k]);
                assert(post.history()[n0 + k] == post.history().take(n1)[n0 + k]);
            };
            assert(b_added.len() == steps.len());
            assert(caller_alone(tok0, backed));
            assert(post.entry() == added[steps.len() as int].0);
            if steps.len() == 0 {
                assert(backed.kernel() == tok0.kernel());
            } else {
                assert(b_added[steps.len() - 1] == added[steps.len() - 1]);
                assert(backed.kernel() == steps.last().post);
                assert(b_added[steps.len() - 1] == (steps.last().pre, steps.last().post));
            }
            assert(post.entry() == backed.kernel());
            lemma_kernel_source_ready_parts(
                tok0.kernel(), tok0.root(), second_space, second_untyped, second_memory, pages, second_slots, second_window@.addr,
            );
            lemma_steps_keep_retype_frame_allowed(
                tok0, backed, steps, second_space, second_untyped, second_memory, pages, second_slots,
                second_window@.addr, second_addr as int, 1, other_untyped, frame_base, slot,
            );
            assert(post.entry().retype_allowed(post.root(), RETYPE_FRAME, other_untyped as usize, frame_base as usize, slot, 0));
        }
    }
    (alloc, second, second_got, out)
}

} // verus!
