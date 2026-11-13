// SPDX-License-Identifier: MIT

//! The witnesses: verified sequences of operations, built into no image, that reach the uses the
//! eager span source exists for.
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_basic};
use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;
use acall::step::Caller;
use aheap::arch::*;
use aheap::source::*;
use verified::capability::operation::STATUS_REFUSED;
use verified::capability::table::TABLE_INDICES;

use crate::eager::*;
use crate::exercise::*;
use crate::glue::{
    AcallStep, acall_ok, acall_steps, lemma_acall_ok_append, lemma_acall_refused_after_ok,
    lemma_acall_steps_append, names_own_space, own_process,
};
use crate::{Eager, MAX_PAGES, REGION_BYTES, TABLE_PAGES, WINDOW_BLOCKS};

verus! {

/// Constructs an eager source of `MAX_PAGES` pages over a region-aligned window.
pub fn witness_new(space: u64, untyped: u64, window: *mut u8) -> (r: Option<Eager>)
    requires
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
    ensures
        r is Some,
{
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
    }
    Eager::new(space, untyped, 0, MAX_PAGES, 1, window)
}

/// Constructs an eager source of `MAX_PAGES` pages over a region-aligned window in the caller's own
/// space and exercises it, as dom0 does at boot.
pub fn witness_exercise(space: u64, untyped: u64, window: *mut u8, token: &mut Tracked<Caller>) -> (seen: Exercised)
    requires
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
    }
    let mut source = Eager::new(space, untyped, 0, MAX_PAGES, 1, window).unwrap();
    let seen = exercise(&mut source, token);
    seen
}

/// Reserves a one-block span from a fresh eager source over a region-aligned window.
pub fn witness_reserve(space: u64, untyped: u64, window: *mut u8, token: &mut Tracked<Caller>) -> (r: Option<*mut u8>)
    requires
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
    }
    let mut src: Eager = Eager::new(space, untyped, 0, MAX_PAGES, 1, window).unwrap();
    src.reserve(token, 1)
}

/// Reserves a one-block span from a fresh eager source over a region-aligned window, releases it and
/// reserves again: the second reservation is granted at the base the first was, which the released
/// span held.
pub fn witness_release_span(space: u64, untyped: u64, window: *mut u8, token: &mut Tracked<Caller>) -> (r: (*mut u8, Option<*mut u8>))
    requires
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
    }
    let mut src: Eager = Eager::new(space, untyped, 0, MAX_PAGES, 1, window).unwrap();
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

/// Reserves a one-block span from a fresh eager source over a region-aligned window and backs its
/// first page: every `acall` step stays within the source's window, slots and untyped, a refusal comes
/// only from `acall` refusing the final non-`Inspect` step, and when `acall` accepts every step the
/// back is granted.
pub fn witness_back(
    space: u64,
    untyped: u64,
    window: *mut u8,
    token: &mut Tracked<Caller>,
) -> (r: (Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>))
    requires
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
        old(token)@.wf(),
        own_process(old(token)@),
        names_own_space(old(token)@, space),
    ensures
        final(token)@.wf(),
        acall_steps(old(token)@, final(token)@, r.1@),
        forall|k: int| 0 <= k < r.1@.len() ==> acall_call_in_window(
            #[trigger] r.1@[k],
            space,
            untyped,
            0,
            MAX_PAGES,
            1,
            window@.addr,
            window@.addr as int,
            1,
        ),
        r.0 is None ==> {
            &&& r.1@.len() > 0
            &&& acall_ok(r.1@.drop_last())
            &&& r.1@.last().out.status == STATUS_REFUSED
        },
        acall_ok(r.1@) ==> r.0 is Some,
{
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
        assert(MAX_PAGES as int - (2 + WINDOW_BLOCKS as int) * TABLE_PAGES as int >= 1) by (compute);
    }
    let mut src: Eager = Eager::new(space, untyped, 0, MAX_PAGES, 1, window).unwrap();
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
    }
    (got, Ghost(steps))
}

/// Reserves a one-block span from a fresh eager source over a region-aligned window, backs its first
/// page, releases it and backs it again: the release parks the page with no system call, so when
/// `acall` accepts every step of the first back, the second is granted the same page with none.
pub fn witness_release(
    space: u64,
    untyped: u64,
    window: *mut u8,
    token: &mut Tracked<Caller>,
) -> (r: (Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>))
    requires
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
        old(token)@.wf(),
        own_process(old(token)@),
        names_own_space(old(token)@, space),
    ensures
        final(token)@.wf(),
        acall_steps(old(token)@, final(token)@, r.1@),
        acall_ok(r.1@) ==> r.0 is Some,
        r.0 is Some ==> r.0->0@.is_range(window@.addr as int, PAGE_BYTES as int),
{
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
        assert(MAX_PAGES as int - (2 + WINDOW_BLOCKS as int) * TABLE_PAGES as int >= 1) by (compute);
    }
    let mut src: Eager = Eager::new(space, untyped, 0, MAX_PAGES, 1, window).unwrap();
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
/// remains, releases the first page, and backs the second page: when `acall` accepts every step, the
/// released frame is unmapped and mapped at the second address.
pub fn witness_back_reuses_released(
    space: u64,
    untyped: u64,
    window: *mut u8,
    token: &mut Tracked<Caller>,
) -> (r: (Option<Tracked<PointsToRaw>>, Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>))
    requires
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
        old(token)@.wf(),
        own_process(old(token)@),
        names_own_space(old(token)@, space),
    ensures
        final(token)@.wf(),
        acall_steps(old(token)@, final(token)@, r.2@),
        forall|k: int| 0 <= k < r.2@.len() ==> acall_call_in_window(
            #[trigger] r.2@[k],
            space,
            untyped,
            0,
            (3 * TABLE_PAGES + 1) as usize,
            1,
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
        acall_ok(r.2@) ==> r.1 is Some,
{
    let pages: usize = 3 * TABLE_PAGES + 1;
    let ghost tok0 = token@;
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (3 * TABLE_PAGES) as int) < TABLE_INDICES) by (compute);
        assert((3 * TABLE_PAGES + 1) / TABLE_PAGES as int == 3) by (compute);
        assert(2 * PAGE_BYTES <= BLOCK_BYTES) by (compute);
    }
    let mut src: Eager = Eager::new(space, untyped, 0, pages, 1, window).unwrap();
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
        assert forall|va: int| #[trigger] run_pages(addr as int, 1).contains(va)
            implies run_pages(addr as int, 2).contains(va) by {};
        assert forall|k: int| 0 <= k < steps1.len() implies acall_call_in_window(
            #[trigger] steps1[k],
            space,
            untyped,
            0,
            pages,
            1,
            window@.addr,
            window@.addr as int,
            2,
        ) by {
            assert(acall_call_in_window(steps1[k], space, untyped, 0, pages, 1, addr, addr as int, 1));
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
        if reused.is_none() {
            lemma_acall_refused_after_ok(steps1, steps2);
        }
        assert forall|va: int| #[trigger] run_pages(next as int, 1).contains(va)
            implies run_pages(addr as int, 2).contains(va) by {};
        assert forall|k: int| 0 <= k < steps.len() implies acall_call_in_window(
            #[trigger] steps[k],
            space,
            untyped,
            0,
            pages,
            1,
            window@.addr,
            window@.addr as int,
            2,
        ) by {
            if k < n1 {
                assert(steps[k] == steps1[k]);
            } else {
                assert(steps[k] == steps2[k - n1]);
                assert(acall_call_in_window(steps2[k - n1], space, untyped, 0, pages, 1, addr, next as int, 1));
                reveal(acall_call_in_window);
            }
        }
    }
    (short, reused, Ghost(steps))
}

} // verus!
