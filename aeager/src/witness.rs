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
use crate::glue::{AcallStep, acall_ok, acall_steps, names_own_space, own_process};
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

} // verus!
