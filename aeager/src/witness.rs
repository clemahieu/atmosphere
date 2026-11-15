// SPDX-License-Identifier: MIT

//! The witnesses: verified sequences of operations, built into no image, that reach the uses the
//! eager span source exists for.
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
    lemma_acall_steps_append, lemma_acall_steps_claimed, lemma_caller_alone_split, lemma_source_ready_premises,
    lemma_window_still_unclaimed, lemma_window_unclaimed, names_own_space, own_process, source_ready, window_tokens_clear,
};
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
        r.1.fresh(),
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
/// steps between the first back's calls, it is granted; each back is refused only when `acall` refuses
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
        caller_alone(old(token)@, final(token)@) ==> r.0 is Some,
        r.0 is Some ==> r.0->0@.is_range(window@.addr as int, PAGE_BYTES as int),
        r.1 is Some ==> r.1->0@.is_range(second_window@.addr as int, PAGE_BYTES as int),
{
    let ghost tok0 = token@;
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
        }
    }
    (got, second_got, Ghost(steps), Ghost(second_steps))
}

} // verus!
