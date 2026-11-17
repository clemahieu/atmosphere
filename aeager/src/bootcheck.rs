// SPDX-License-Identifier: MIT

//! A verified use of the span source contract that runs, where the witness in aheap is built into no
//! image: from any well-formed source it reserves a span of one block; backs its first page, writes a
//! byte there and releases it, backs the second page and writes another byte, backs the first page
//! again and writes there, reads the second page's byte and releases both; backs the span's pages one
//! at a time until the source refuses or the block is full, writes a byte through the run's permission
//! and reads it back, releases the run, backs one page again and releases it, backs the page the
//! source refused, at an address it never backed, writes and reads a byte there and releases it, and
//! gives the span back, ending with the spans it started with; only the source's count of refusals
//! may have grown. The proof says the second page reads its own byte, since the two pages' permissions
//! are apart; on the machine it does only while no translation of the first page outlives its release,
//! so that is what the read checks. What it saw is the caller's to judge: dom0 prints it.
//! `exercise_eager` builds the eager source and exercises it in one verified call, so that the source
//! serving the caller and its view being well formed, which `exercise` requires, are `Eager::new`'s
//! ensures and no glue's word. This module is an in-image boot check, a verified script dom0 runs
//! and judges, and it holds no operation (design/witness-per-way-an-operation-succeeds/).
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::layout::*;
use vstd::pervasive::unreached;
use vstd::prelude::*;
use vstd::raw_ptr::*;

use acall::step::Caller;
use aheap::allocator::Allocator;
use aheap::arch::*;
use aheap::source::*;

#[cfg(verus_keep_ghost)]
use crate::apart::sources_apart;
#[cfg(verus_keep_ghost)]
use crate::glue::{names_own_space, own_process, window_unclaimed};
use crate::eager::Eager;
#[cfg(verus_keep_ghost)]
use crate::eager::WINDOW_BYTES;
#[cfg(verus_keep_ghost)]
use verified::capability::map::LOWER_HALF_END;
#[cfg(verus_keep_ghost)]
use verified::define::SIZE_512G;

verus! {

broadcast use group_raw_ptr_axioms;

/// What `exercise` saw.
pub struct Exercised {
    /// The pages the source backed before it refused or the block was full.
    pub backed: usize,
    /// Whether the source refused a page before the block was full.
    pub refused: bool,
    /// Whether a byte written through the run's permission was read back.
    pub read: bool,
    /// Whether the source backed a page again once the run was released.
    pub again: bool,
    /// Whether a page backed after another was released, and written before that other was backed and
    /// written again, read its own byte back.
    pub apart: bool,
    /// Whether, once the run was released after a refusal, the source backed the page it had refused,
    /// at an address it never backed before, and a byte written there read back.
    pub fresh: bool,
}

/// The byte at `p`, the first of the page whose bytes `perm` permits, holding `value`, and the
/// permission to the rest of the page.
fn put(p: *mut u8, perm: Tracked<PointsToRaw>, value: u8) -> (r: (Tracked<PointsTo<u8>>, Tracked<PointsToRaw>))
    requires
        p@.addr != 0,
        perm@.is_range(p@.addr as int, PAGE_BYTES as int),
        p@.provenance == perm@.provenance(),
    ensures
        r.0@.ptr() == p,
        r.0@.opt_value() == MemContents::Init(value),
        r.1@.dom() =~= Set::range(p@.addr + 1, p@.addr + PAGE_BYTES),
        r.1@.provenance() == perm@.provenance(),
{
    let tracked (one, rest) = perm.get().split(Set::range(p@.addr as int, p@.addr + 1));
    assert(size_of::<u8>() == 1 && align_of::<u8>() == 1) by {
        broadcast use layout_of_primitives, align_of_u8;
    }
    assert(one.is_range(p@.addr as int, size_of::<u8>() as int));
    let tracked mut byte = one.into_typed::<u8>(p@.addr);
    ptr_mut_write(p, Tracked(&mut byte), value);
    (Tracked(byte), Tracked(rest))
}

/// Reads the byte at `p` that `put` wrote, and joins its permission with the rest of the page's.
fn take(p: *mut u8, byte: Tracked<PointsTo<u8>>, rest: Tracked<PointsToRaw>) -> (r: (u8, Tracked<PointsToRaw>))
    requires
        byte@.ptr() == p,
        byte@.is_init(),
        rest@.dom() =~= Set::range(p@.addr + 1, p@.addr + PAGE_BYTES),
        rest@.provenance() == p@.provenance,
    ensures
        r.0 == byte@.value(),
        r.1@.is_range(p@.addr as int, PAGE_BYTES as int),
        r.1@.provenance() == p@.provenance,
{
    let tracked mut byte = byte.get();
    let value = ptr_mut_read(p, Tracked(&mut byte));
    assert(size_of::<u8>() == 1) by {
        broadcast use layout_of_primitives;
    }
    let tracked whole = byte.into_raw().join(rest.get());
    assert(whole.dom() =~= Set::range(p@.addr as int, p@.addr + PAGE_BYTES));
    (value, Tracked(whole))
}

/// Backs the first page of the span at `base`, which has one block and nothing backed, writes 1 there
/// and releases it; backs the second page and writes 2 there; backs the first page again and writes 3;
/// then reads the second page's byte and releases both pages. Whether every back was granted and the
/// second page read 2, which the proof says it does whenever it is read, and leaves the spans as they
/// were.
fn apart<S: SpanSource>(src: &mut S, token: &mut Tracked<S::Token>, base: *mut u8) -> (r: bool)
    requires
        old(src).serves(old(token)@),
        old(src)@.wf(),
        old(src)@.spans.contains_key(base@.addr as int),
        old(src)@.spans[base@.addr as int].blocks == 1,
        old(src)@.spans[base@.addr as int].backed =~= Set::empty(),
        base@.provenance == old(src)@.provenance,
        base@.addr as int % BLOCK_BYTES as int == 0,
        base@.addr + BLOCK_BYTES <= usize::MAX + 1,
    ensures
        final(src).serves(final(token)@),
        final(src)@.wf(),
        final(src)@.spans == old(src)@.spans,
        final(src)@.provenance == old(src)@.provenance,
{
    let ghost start = src@;
    let x = base.addr();
    let ghost span = x as int;
    proof {
        assert(BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES);
        assert(2 * PAGE_BYTES <= BLOCK_BYTES);
        lemma_page_aligned(x as int, 0);
        lemma_page_aligned(x as int, 1);
        lemma_run_grows(x as int, 0);
        lemma_run_grows(x as int, 1);
        assert(run_pages(x as int, 0) =~= Set::empty());
    }
    let y = x + PAGE_BYTES;
    let py = base.with_addr(y);
    assert(run_pages(x as int, 1) =~= set![x as int]);
    assert(run_pages(y as int, 1) =~= set![y as int]) by {
        assert(y as int % PAGE_BYTES as int == 0);
    }
    let first = match src.back(token, Ghost(span), x, 1) {
        None => return false,
        Some(perm) => perm,
    };
    let (byte, rest) = put(base, first, 1);
    let (_, first) = take(base, byte, rest);
    src.release(token, Ghost(span), x, 1, first);
    assert(src@.spans[span].backed =~= start.spans[span].backed);
    assert(src@.spans =~= start.spans);
    let second = match src.back(token, Ghost(span), y, 1) {
        None => return false,
        Some(perm) => perm,
    };
    let (yb, yrest) = put(py, second, 2);
    let first = match src.back(token, Ghost(span), x, 1) {
        None => {
            let (_, second) = take(py, yb, yrest);
            src.release(token, Ghost(span), y, 1, second);
            assert(src@.spans[span].backed =~= start.spans[span].backed);
            assert(src@.spans =~= start.spans);
            return false;
        },
        Some(perm) => perm,
    };
    let (xb, xrest) = put(base, first, 3);
    let (seen, second) = take(py, yb, yrest);
    let (_, first) = take(base, xb, xrest);
    src.release(token, Ghost(span), y, 1, second);
    src.release(token, Ghost(span), x, 1, first);
    assert(src@.spans[span].backed =~= start.spans[span].backed);
    assert(src@.spans =~= start.spans);
    seen == 2
}

/// A page run from a block's base is page-aligned.
proof fn lemma_page_aligned(base: int, k: int)
    requires
        base % BLOCK_BYTES as int == 0,
    ensures
        (base + k * PAGE_BYTES) % PAGE_BYTES as int == 0,
{
    let q = base / BLOCK_BYTES as int;
    lemma_fundamental_div_mod(base, BLOCK_BYTES as int);
    assert(BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES);
    assert(base + k * PAGE_BYTES == (q * BLOCK_PAGES + k) * PAGE_BYTES) by (nonlinear_arith)
        requires
            base == BLOCK_BYTES * q,
            BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
    ;
    lemma_mod_multiples_basic(q * BLOCK_PAGES + k, PAGE_BYTES as int);
}

/// The run of `k` pages and the page after it are disjoint and make the run of `k + 1` pages.
proof fn lemma_run_grows(start: int, k: nat)
    ensures
        run_pages(start, k).disjoint(run_pages(start + k * PAGE_BYTES, 1)),
        run_pages(start, k).union(run_pages(start + k * PAGE_BYTES, 1)) =~= run_pages(start, k + 1),
{
    assert((k + 1) * PAGE_BYTES == k * PAGE_BYTES + PAGE_BYTES) by (nonlinear_arith);
}

/// Exercises `src` from any well-formed view and leaves its spans as it found them.
pub fn exercise<S: SpanSource>(src: &mut S, token: &mut Tracked<S::Token>) -> (seen: Exercised)
    requires
        old(src).serves(old(token)@),
        old(src)@.wf(),
    ensures
        final(src).serves(final(token)@),
        final(src)@.spans == old(src)@.spans,
        final(src)@.provenance == old(src)@.provenance,
{
    let ghost start = src@;
    let nothing = Exercised { backed: 0, refused: false, read: false, again: false, apart: false, fresh: false };
    let base = match src.reserve(token, 1) {
        None => return nothing,
        Some(base) => base,
    };
    let addr = base.addr();
    let ghost reserved = src@;
    let ghost provenance = start.provenance;
    assert(!start.spans.contains_key(addr as int));
    proof {
        assert(BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES);
        assert(BLOCK_PAGES * PAGE_BYTES == BLOCK_BYTES) by (nonlinear_arith)
            requires
                BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES,
        ;
    }
    assert(run_pages(addr as int, 0) =~= Set::empty());
    let apart = apart(src, token, base);
    assert(src@.spans =~= reserved.spans.insert(addr as int, Span { blocks: 1, backed: run_pages(addr as int, 0) }));
    let tracked mut run = PointsToRaw::empty(provenance);
    let mut k: usize = 0;
    let mut limit = BLOCK_PAGES;
    while k < limit
        invariant
            src.serves(token@),
            k <= limit <= BLOCK_PAGES,
            BLOCK_PAGES * PAGE_BYTES == BLOCK_BYTES,
            addr == base@.addr,
            base@.provenance == provenance,
            addr as int % BLOCK_BYTES as int == 0,
            addr + BLOCK_BYTES <= usize::MAX + 1,
            !start.spans.contains_key(addr as int),
            reserved == start.reserved(addr as int, 1),
            src@.wf(),
            src@.provenance == provenance,
            src@.spans == reserved.spans.insert(addr as int, Span { blocks: 1, backed: run_pages(addr as int, k as nat) }),
            run.dom() =~= Set::range(addr as int, addr + k * PAGE_BYTES),
            run.provenance() == provenance,
        decreases limit - k,
    {
        proof {
            assert(k * PAGE_BYTES + PAGE_BYTES <= BLOCK_PAGES * PAGE_BYTES) by (nonlinear_arith)
                requires
                    k < BLOCK_PAGES,
            ;
            lemma_page_aligned(addr as int, k as int);
            lemma_run_grows(addr as int, k as nat);
        }
        let page = addr + k * PAGE_BYTES;
        match src.back(token, Ghost(addr as int), page, 1) {
            None => {
                limit = k;
            },
            Some(perm) => {
                proof {
                    run = run.join(perm.get());
                }
                k += 1;
                assert(run.dom() =~= Set::range(addr as int, addr + k * PAGE_BYTES));
                assert(src@.spans =~= reserved.spans.insert(addr as int, Span { blocks: 1, backed: run_pages(addr as int, k as nat) }));
            },
        }
    }
    let refused = k < BLOCK_PAGES;
    proof {
        assert(k * PAGE_BYTES <= BLOCK_PAGES * PAGE_BYTES) by (nonlinear_arith)
            requires
                k <= BLOCK_PAGES,
        ;
        lemma_page_aligned(addr as int, 0);
    }
    let mut read = false;
    if k > 0 {
        let ghost first = Set::range(addr as int, addr as int + 1);
        let tracked (one, rest) = run.split(first);
        assert(size_of::<u8>() == 1 && align_of::<u8>() == 1) by {
            broadcast use layout_of_primitives, align_of_u8;
        }
        assert(one.is_range(addr as int, size_of::<u8>() as int));
        let tracked mut byte = one.into_typed::<u8>(addr);
        ptr_mut_write(base, Tracked(&mut byte), 7u8);
        let value = ptr_mut_read(base, Tracked(&mut byte));
        read = value == 7u8;
        let tracked raw = byte.into_raw();
        let tracked whole = raw.join(rest);
        assert(whole.dom() =~= Set::range(addr as int, addr + k * PAGE_BYTES));
        src.release(token, Ghost(addr as int), addr, k, Tracked(whole));
    }
    assert(src@.spans[addr as int].backed =~= Set::empty());
    assert(src@.spans =~= reserved.spans);
    proof {
        lemma_page_aligned(addr as int, 0);
        lemma_run_grows(addr as int, 0);
    }
    let again = match src.back(token, Ghost(addr as int), addr, 1) {
        None => false,
        Some(perm) => {
            src.release(token, Ghost(addr as int), addr, 1, perm);
            true
        },
    };
    assert(src@.spans[addr as int].backed =~= Set::empty());
    assert(src@.spans =~= reserved.spans);
    let mut fresh = false;
    if refused {
        proof {
            assert(k * PAGE_BYTES + PAGE_BYTES <= BLOCK_PAGES * PAGE_BYTES) by (nonlinear_arith)
                requires
                    k < BLOCK_PAGES,
            ;
            lemma_page_aligned(addr as int, k as int);
            lemma_run_grows(addr as int, 0);
        }
        let page = addr + k * PAGE_BYTES;
        let p = base.with_addr(page);
        match src.back(token, Ghost(addr as int), page, 1) {
            None => {},
            Some(perm) => {
                let (byte, rest) = put(p, perm, 9);
                let (value, perm) = take(p, byte, rest);
                fresh = value == 9;
                src.release(token, Ghost(addr as int), page, 1, perm);
            },
        }
        assert(src@.spans[addr as int].backed =~= Set::empty());
        assert(src@.spans =~= reserved.spans);
    }
    src.release_span(token, addr);
    assert(src@.spans =~= start.spans);
    Exercised { backed: k, refused, read, again, apart, fresh }
}

/// Builds the eager source `Eager::new` builds from these arguments and exercises it, or returns
/// `None` when `new` refuses them. The source serves the caller between the two calls because nothing
/// else runs between them: `new` returns it holding every frame it holds, and the caller's own
/// process and its space slot are as they were.
pub fn exercise_eager(
    caller: &mut Tracked<Caller>,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: *mut u8,
) -> (seen: Option<Exercised>)
    requires
        old(caller)@.pages_wf(),
        window_unclaimed(old(caller)@, window@.addr),
        old(caller)@.wf(),
        own_process(old(caller)@),
        names_own_space(old(caller)@, space),
    ensures
        final(caller)@.wf(),
        final(caller)@.pages_wf(),
        own_process(final(caller)@),
        seen is Some <==> Eager::new_ok(memory, pages, slots, window),
{
    let mut source = match Eager::new(caller, space, untyped, memory, pages, slots, window) {
        None => return None,
        Some(source) => source,
    };
    let seen = exercise(&mut source, caller);
    proof {
        source.lemma_holds_pages_wf(caller@);
    }
    Some(seen)
}

enum BackedPage {
    Empty,
    Held(usize, Tracked<PointsToRaw>),
    CheckedOut,
}

struct PairedState {
    alloc: Option<Allocator<Eager>>,
    bench: Option<Eager>,
    span: Option<*mut u8>,
    backed: BackedPage,
}

/// Bundles the process's `Allocator<Eager>` with a second, disjoint `Eager` benchmark source
/// inside one invariant so benchmark operations (`bench_reserve`, `bench_back`, `bench_release`,
/// `bench_release_span`, `restore_into`) verify without per-call boundary obligations in
/// unverified callers.
pub struct PairedEager {
    state: PairedState,
}

#[inline(never)]
fn lend_caller_from(alloc_slot: &mut Option<Allocator<Eager>>) -> (r: (u64, Option<Tracked<Caller>>))
    ensures
        *old(alloc_slot) matches Some(old_a) ==> {
            &&& *final(alloc_slot) matches Some(new_a)
            &&& new_a.src() == old_a.src()
            &&& old_a.held() <==> r.1 is Some
            &&& r.1 matches Some(c) ==> {
                &&& c@ == old_a.token()->0
                &&& old_a.src().serves(c@)
                &&& c@.wf()
                &&& own_process(c@)
                &&& c@.pages_wf()
                &&& names_own_space(c@, r.0)
                &&& r.0 == new_a.src().space()
            }
        },
        *old(alloc_slot) is None ==> *final(alloc_slot) is None && r.1 is None,
    no_unwind
{
    let Some(mut alloc) = alloc_slot.take() else {
        return (0, None);
    };
    proof {
        alloc.lemma_wf();
    }
    let space = alloc.source().exec_space();
    let caller = alloc.lend();
    proof {
        match &caller {
            Some(c) => alloc.src().lemma_holds_pages_wf(c@),
            None => (),
        }
    }
    *alloc_slot = Some(alloc);
    (space, caller)
}

#[inline(never)]
fn give_back_to(alloc_slot: &mut Option<Allocator<Eager>>, caller: Tracked<Caller>)
    requires
        *old(alloc_slot) matches Some(old_a) && old_a.src().serves(caller@),
    ensures
        *final(alloc_slot) matches Some(new_a) && new_a.held() && new_a.token() == Some(caller@)
            && new_a.src() == old(alloc_slot)->0.src(),
    no_unwind
{
    let Some(mut alloc) = alloc_slot.take() else {
        unreached()
    };
    alloc.give_back(caller);
    *alloc_slot = Some(alloc);
}

#[inline(never)]
fn give_back_and_check_apart_opt(
    alloc_slot: &mut Option<Allocator<Eager>>,
    caller: Tracked<Caller>,
    bench_slot: &Option<Eager>,
) -> (r: bool)
    requires
        *old(alloc_slot) matches Some(old_a) && old_a.src().serves(caller@),
        *bench_slot is Some,
    ensures
        *final(alloc_slot) matches Some(new_a) && new_a.held() && new_a.token() == Some(caller@)
            && new_a.src() == old(alloc_slot)->0.src(),
        r ==> {
            let bench = (*bench_slot)->0;
            &&& bench.window() as int % SIZE_512G as int == 0
            &&& bench.window() + WINDOW_BYTES <= LOWER_HALF_END as usize
            &&& final(alloc_slot)->0.src().window() as int % SIZE_512G as int == 0
            &&& final(alloc_slot)->0.src().window() + WINDOW_BYTES <= LOWER_HALF_END as usize
            &&& sources_apart(
                bench.memory(),
                bench.pages(),
                bench.slots(),
                bench.window(),
                final(alloc_slot)->0.src().memory(),
                final(alloc_slot)->0.src().pages(),
                final(alloc_slot)->0.src().slots(),
                final(alloc_slot)->0.src().window(),
            )
        },
{
    let Some(bench) = bench_slot else {
        unreached()
    };
    let Some(mut alloc) = alloc_slot.take() else {
        unreached()
    };
    let apart = bench.exec_apart_from(alloc.source());
    alloc.give_back(caller);
    *alloc_slot = Some(alloc);
    apart
}

spec fn pair_compatible(bench: Eager, alloc: Allocator<Eager>) -> bool {
    &&& alloc.held()
    &&& bench@.wf()
    &&& bench.serves(alloc.token()->0)
    &&& bench.window() as int % SIZE_512G as int == 0
    &&& bench.window() + WINDOW_BYTES <= LOWER_HALF_END as usize
    &&& alloc.src().window() as int % SIZE_512G as int == 0
    &&& alloc.src().window() + WINDOW_BYTES <= LOWER_HALF_END as usize
    &&& sources_apart(
        bench.memory(),
        bench.pages(),
        bench.slots(),
        bench.window(),
        alloc.src().memory(),
        alloc.src().pages(),
        alloc.src().slots(),
        alloc.src().window(),
    )
}

#[inline(never)]
fn make_bench_in(
    bench_slot: &mut Option<Eager>,
    caller: &mut Tracked<Caller>,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: *mut u8,
) -> (r: bool)
    requires
        *old(bench_slot) is None,
        old(caller)@.wf(),
        own_process(old(caller)@),
        old(caller)@.pages_wf(),
        names_own_space(old(caller)@, space),
        window_unclaimed(old(caller)@, window@.addr),
    ensures
        final(caller)@.kernel() == old(caller)@.kernel(),
        final(caller)@.entry() == old(caller)@.entry(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.history() == old(caller)@.history(),
        final(caller)@.pages_id() == old(caller)@.pages_id(),
        final(caller)@.wf(),
        own_process(final(caller)@),
        final(caller)@.pages_wf(),
        names_own_space(final(caller)@, space),
        r <==> *final(bench_slot) is Some,
        r ==> {
            let b = (*final(bench_slot))->0;
            &&& b.serves(final(caller)@)
            &&& b.holds(final(caller)@)
            &&& b@.wf()
            &&& b.space() == space
            &&& b.untyped() == untyped
            &&& b.memory() == memory
            &&& b.pages() == pages
            &&& b.slots() == slots
            &&& b.window() == window@.addr
        },
{
    *bench_slot = Eager::new(caller, space, untyped, memory, pages, slots, window);
    bench_slot.is_some()
}

#[inline(never)]
fn prepare_bench_in(
    alloc_slot: &mut Option<Allocator<Eager>>,
    bench_slot: &mut Option<Eager>,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: *mut u8,
) -> (r: bool)
    requires
        *old(alloc_slot) matches Some(a) ==> (a.held() ==> window_unclaimed(a.token()->0, window@.addr)),
        *old(bench_slot) is None,
    ensures
        r ==> {
            &&& *final(alloc_slot) is Some
            &&& *final(bench_slot) is Some
            &&& pair_compatible((*final(bench_slot))->0, (*final(alloc_slot))->0)
        },
{
    let (space, caller_opt) = lend_caller_from(alloc_slot);
    let Some(mut caller) = caller_opt else {
        return false;
    };
    let ghost tok0 = caller@;
    let ok = make_bench_in(bench_slot, &mut caller, space, untyped, memory, pages, slots, window);
    let ghost tok1 = caller@;
    proof {
        let ghost a = (*alloc_slot)->0;
        a.src().lemma_holds_claimed(tok0, tok1);
        assert(a.src().serves(tok1));
    }
    if !ok {
        give_back_to(alloc_slot, caller);
        return false;
    }
    proof {
        assert((*bench_slot)->0.serves(tok1));
    }
    give_back_and_check_apart_opt(alloc_slot, caller, bench_slot)
}

#[inline(never)]
fn pack_alloc(src: &mut Option<Allocator<Eager>>, dst: &mut Option<Allocator<Eager>>)
    requires
        *old(dst) is None,
    ensures
        *final(src) is None,
        *final(dst) == *old(src),
    no_unwind
{
    core::mem::swap(src, dst);
}

#[inline(never)]
fn pack_bench(src: &mut Option<Eager>, dst: &mut Option<Eager>)
    requires
        *old(dst) is None,
    ensures
        *final(src) is None,
        *final(dst) == *old(src),
    no_unwind
{
    core::mem::swap(src, dst);
}

#[inline(never)]
fn clear_bench(dst: &mut Option<Eager>)
    ensures
        *final(dst) is None,
    no_unwind
{
    *dst = None;
}

proof fn lemma_opt_alloc_wf(tracked opt: &Option<Allocator<Eager>>)
    ensures
        opt matches Some(a) ==> {
            &&& a.src_view().wf()
            &&& a.held() <==> a.token() is Some
            &&& a.token() matches Some(t) ==> a.src_serves(t)
        },
{
    match opt {
        Some(a) => a.lemma_wf(),
        None => (),
    }
}

#[inline(never)]
fn reserve_from_opt(
    bench_slot: &mut Option<Eager>,
    caller: &mut Tracked<Caller>,
) -> (r: Option<*mut u8>)
    requires
        *old(bench_slot) is Some,
        old(bench_slot)->0@.wf(),
        old(bench_slot)->0.serves(old(caller)@),
    ensures
        *final(bench_slot) is Some,
        final(caller)@ == old(caller)@,
        ({
            let ob = (*old(bench_slot))->0;
            let fb = (*final(bench_slot))->0;
            &&& fb@.wf()
            &&& fb@.provenance == ob@.provenance
            &&& fb.serves(final(caller)@)
            &&& fb.space() == ob.space()
            &&& fb.untyped() == ob.untyped()
            &&& fb.memory() == ob.memory()
            &&& fb.pages() == ob.pages()
            &&& fb.slots() == ob.slots()
            &&& fb.window() == ob.window()
            &&& match r {
                Some(ptr) => {
                    let first = (ptr@.addr - ob.window()) / BLOCK_BYTES as int;
                    &&& fb@.spans.contains_key(ptr@.addr as int)
                    &&& fb@.spans[ptr@.addr as int].backed =~= Set::empty()
                    &&& ptr@.provenance == fb@.provenance
                    &&& ptr@.addr == ob.window() + first * BLOCK_BYTES
                    &&& 0 <= first
                    &&& first + 1 <= crate::WINDOW_BLOCKS
                    &&& ob.window_fits(first, 1nat)
                },
                None => fb@.spans == ob@.spans,
            }
        }),
    no_unwind
{
    let Some(mut bench) = bench_slot.take() else {
        unreached()
    };
    let got = bench.reserve(caller, 1);
    *bench_slot = Some(bench);
    got
}

#[inline(never)]
#[verifier::spinoff_prover]
fn back_from_opt(
    bench_slot: &mut Option<Eager>,
    alloc_ref: &Option<Allocator<Eager>>,
    caller: &mut Tracked<Caller>,
    ptr: *mut u8,
) -> (r: Option<Tracked<PointsToRaw>>)
    requires
        *old(bench_slot) is Some,
        *alloc_ref is Some,
        ({
            let ob = (*old(bench_slot))->0;
            let oa = (*alloc_ref)->0;
            let addr = ptr.addr();
            &&& ob@.wf()
            &&& ob.serves(old(caller)@)
            &&& oa.src().serves(old(caller)@)
            &&& oa.src()@.wf()
            &&& oa.src().window() as int % SIZE_512G as int == 0
            &&& oa.src().window() + WINDOW_BYTES <= LOWER_HALF_END as usize
            &&& ob.window() as int % SIZE_512G as int == 0
            &&& ob.window() + WINDOW_BYTES <= LOWER_HALF_END as usize
            &&& sources_apart(
                ob.memory(),
                ob.pages(),
                ob.slots(),
                ob.window(),
                oa.src().memory(),
                oa.src().pages(),
                oa.src().slots(),
                oa.src().window(),
            )
            &&& ptr@.provenance == ob@.provenance
            &&& ob.window() <= addr
            &&& addr + BLOCK_BYTES <= ob.window() + WINDOW_BYTES
            &&& ob@.spans.contains_key(addr as int)
            &&& ob@.spans[addr as int].backed =~= Set::empty()
        }),
    ensures
        *final(bench_slot) is Some,
        ({
            let ob = (*old(bench_slot))->0;
            let fb = (*final(bench_slot))->0;
            let oa = (*alloc_ref)->0;
            let addr = ptr.addr();
            &&& fb@.wf()
            &&& fb@.provenance == ob@.provenance
            &&& fb.serves(final(caller)@)
            &&& oa.src().serves(final(caller)@)
            &&& fb.space() == ob.space()
            &&& fb.untyped() == ob.untyped()
            &&& fb.memory() == ob.memory()
            &&& fb.pages() == ob.pages()
            &&& fb.slots() == ob.slots()
            &&& fb.window() == ob.window()
            &&& match r {
                Some(perm) => {
                    &&& fb@.spans.contains_key(addr as int)
                    &&& fb@.runs_in(addr as int, addr as int, 1nat)
                    &&& fb@.backed(addr as int, addr as int, 1nat)
                    &&& fb@.spans[addr as int].backed =~= run_pages(addr as int, 1nat)
                    &&& perm@.is_range(addr as int, PAGE_BYTES as int)
                    &&& perm@.provenance() == fb@.provenance
                },
                None => {
                    &&& fb@.spans == ob@.spans
                    &&& fb@.spans[addr as int].backed =~= Set::empty()
                },
            }
        }),
    no_unwind
{
    let Some(mut bench) = bench_slot.take() else {
        unreached()
    };
    let Some(alloc) = alloc_ref else {
        unreached()
    };
    let addr = ptr.addr();
    proof {
        bench.lemma_holds_pages_wf(caller@);
        assert(BLOCK_BYTES == PAGE_BYTES * BLOCK_PAGES);
        assert(PAGE_BYTES <= BLOCK_BYTES);
        lemma_page_aligned(addr as int, 0);
        lemma_run_grows(addr as int, 0);
        assert(run_pages(addr as int, 0) =~= Set::empty());
        assert(run_pages(addr as int, 1) =~= set![addr as int]);
        assert(bench@.runs_in(addr as int, addr as int, 1nat));
        assert(bench@.unbacked(addr as int, addr as int, 1nat));
    }
    let ghost tok0 = caller@;
    let ghost old_trace_len = bench.acall_trace().len() as int;
    let got = bench.back(caller, Ghost(addr as int), addr, 1);
    let other = alloc.source();
    proof {
        bench.lemma_holds_pages_wf(caller@);
        let steps = bench.acall_trace().skip(old_trace_len);
        bench.lemma_steps_keep_other_serves(
            other,
            tok0,
            caller@,
            steps,
            addr as int,
            1nat,
        );
    }
    *bench_slot = Some(bench);
    got
}

#[inline(never)]
fn release_from_opt(
    bench_slot: &mut Option<Eager>,
    caller: &mut Tracked<Caller>,
    sp_addr: usize,
    addr: usize,
    perm: Tracked<PointsToRaw>,
)
    requires
        *old(bench_slot) is Some,
        ({
            let ob = (*old(bench_slot))->0;
            &&& ob@.wf()
            &&& ob.serves(old(caller)@)
            &&& ob@.runs_in(sp_addr as int, addr as int, 1nat)
            &&& ob@.backed(sp_addr as int, addr as int, 1nat)
            &&& perm@.is_range(addr as int, PAGE_BYTES as int)
            &&& perm@.provenance() == ob@.provenance
        }),
    ensures
        *final(bench_slot) is Some,
        final(caller)@ == old(caller)@,
        ({
            let ob = (*old(bench_slot))->0;
            let fb = (*final(bench_slot))->0;
            &&& fb@.wf()
            &&& fb@.provenance == ob@.provenance
            &&& fb.serves(final(caller)@)
            &&& fb.space() == ob.space()
            &&& fb.untyped() == ob.untyped()
            &&& fb.memory() == ob.memory()
            &&& fb.pages() == ob.pages()
            &&& fb.slots() == ob.slots()
            &&& fb.window() == ob.window()
            &&& fb@.spans.contains_key(sp_addr as int)
            &&& fb@.spans[sp_addr as int].backed == ob@.spans[sp_addr as int].backed.difference(
                run_pages(addr as int, 1nat),
            )
        }),
    no_unwind
{
    let Some(mut bench) = bench_slot.take() else {
        unreached()
    };
    bench.release(caller, Ghost(sp_addr as int), addr, 1, perm);
    *bench_slot = Some(bench);
}

#[inline(never)]
fn release_span_from_opt(
    bench_slot: &mut Option<Eager>,
    caller: &mut Tracked<Caller>,
    sp_addr: usize,
)
    requires
        *old(bench_slot) is Some,
        ({
            let ob = (*old(bench_slot))->0;
            &&& ob@.wf()
            &&& ob.serves(old(caller)@)
            &&& ob@.spans.contains_key(sp_addr as int)
            &&& ob@.spans[sp_addr as int].backed =~= Set::empty()
        }),
    ensures
        *final(bench_slot) is Some,
        final(caller)@ == old(caller)@,
        ({
            let ob = (*old(bench_slot))->0;
            let fb = (*final(bench_slot))->0;
            &&& fb@.wf()
            &&& fb@.provenance == ob@.provenance
            &&& fb.serves(final(caller)@)
            &&& fb.space() == ob.space()
            &&& fb.untyped() == ob.untyped()
            &&& fb.memory() == ob.memory()
            &&& fb.pages() == ob.pages()
            &&& fb.slots() == ob.slots()
            &&& fb.window() == ob.window()
            &&& fb@.spans == ob@.spans.remove(sp_addr as int)
        }),
    no_unwind
{
    let Some(mut bench) = bench_slot.take() else {
        unreached()
    };
    bench.release_span(caller, sp_addr);
    *bench_slot = Some(bench);
}

impl PairedState {
    spec fn inv(self) -> bool {
        match (self.alloc, self.bench) {
            (None, None) => self.span is None && self.backed is Empty,
            (Some(alloc), Some(bench)) => {
                &&& pair_compatible(bench, alloc)
                &&& match self.span {
                    None => self.backed is Empty,
                    Some(sp) => {
                        let addr = sp@.addr;
                        &&& sp@.provenance == bench@.provenance
                        &&& bench.window() <= addr
                        &&& addr + BLOCK_BYTES <= bench.window() + WINDOW_BYTES
                        &&& bench@.spans.contains_key(addr as int)
                        &&& match self.backed {
                            BackedPage::Empty => bench@.spans[addr as int].backed =~= Set::empty(),
                            BackedPage::CheckedOut => {
                                &&& bench@.runs_in(addr as int, addr as int, 1nat)
                                &&& bench@.backed(addr as int, addr as int, 1nat)
                                &&& bench@.spans[addr as int].backed =~= run_pages(addr as int, 1nat)
                            },
                            BackedPage::Held(backed_addr, perm) => {
                                &&& backed_addr == addr
                                &&& bench@.runs_in(addr as int, backed_addr as int, 1nat)
                                &&& bench@.backed(addr as int, backed_addr as int, 1nat)
                                &&& bench@.spans[addr as int].backed =~= run_pages(addr as int, 1nat)
                                &&& perm@.is_range(backed_addr as int, PAGE_BYTES as int)
                                &&& perm@.provenance() == bench@.provenance
                            },
                        }
                    },
                }
            },
            _ => false,
        }
    }

    fn is_empty(&self) -> (r: bool)
        requires
            self.inv(),
        ensures
            r <==> (self.alloc is None && self.bench is None),
    {
        self.alloc.is_none()
    }

    #[inline(never)]
    fn pack_from(&mut self, alloc_slot: &mut Option<Allocator<Eager>>, bench_slot: &mut Option<Eager>)
        requires
            old(self).inv(),
            old(self).alloc is None,
            old(self).bench is None,
            *old(alloc_slot) is Some,
            *old(bench_slot) is Some,
            pair_compatible((*old(bench_slot))->0, (*old(alloc_slot))->0),
        ensures
            final(self).inv(),
            *final(alloc_slot) is None,
            *final(bench_slot) is None,
        no_unwind
    {
        pack_alloc(alloc_slot, &mut self.alloc);
        pack_bench(bench_slot, &mut self.bench);
    }

    #[inline(never)]
    fn restore_into(&mut self, alloc_slot: &mut Option<Allocator<Eager>>) -> (r: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
        no_unwind
    {
        if self.alloc.is_none() || self.bench.is_none() || alloc_slot.is_some() {
            return false;
        }
        self.span = None;
        self.backed = BackedPage::Empty;
        clear_bench(&mut self.bench);
        pack_alloc(&mut self.alloc, alloc_slot);
        true
    }

    fn bench_reserve(&mut self) -> (r: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
        no_unwind
    {
        proof {
            lemma_opt_alloc_wf(&self.alloc);
        }
        let is_empty_backed = match self.backed {
            BackedPage::Empty => true,
            _ => false,
        };
        if self.alloc.is_none() || self.bench.is_none() || self.span.is_some() || !is_empty_backed {
            return false;
        }
        let (_, caller_opt) = lend_caller_from(&mut self.alloc);
        let Some(mut caller) = caller_opt else {
            return false;
        };
        let got = reserve_from_opt(&mut self.bench, &mut caller);
        give_back_to(&mut self.alloc, caller);
        match got {
            None => false,
            Some(ptr) => {
                proof {
                    let b = self.bench->0;
                    assert(b@.spans.contains_key(ptr@.addr as int));
                    assert(b@.spans[ptr@.addr as int].backed =~= Set::empty());
                    let first = (ptr@.addr - b.window()) / BLOCK_BYTES as int;
                    assert(ptr@.addr == b.window() + first * BLOCK_BYTES);
                    assert(0 <= first && first + 1 <= crate::WINDOW_BLOCKS);
                    assert(BLOCK_BYTES * crate::WINDOW_BLOCKS == WINDOW_BYTES);
                    assert(first * BLOCK_BYTES >= 0 && first * BLOCK_BYTES + BLOCK_BYTES <= WINDOW_BYTES)
                        by (nonlinear_arith)
                        requires
                            0 <= first,
                            first + 1 <= crate::WINDOW_BLOCKS,
                            BLOCK_BYTES > 0,
                            BLOCK_BYTES * crate::WINDOW_BLOCKS == WINDOW_BYTES,
                    ;
                }
                self.span = Some(ptr);
                true
            },
        }
    }

    fn bench_back_start(&mut self) -> (r: Option<(*mut u8, Tracked<PointsToRaw>)>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            r matches Some((ptr, perm)) ==> {
                let addr = ptr@.addr;
                &&& ptr@.addr != 0
                &&& final(self).span == Some(ptr)
                &&& final(self).bench is Some
                &&& ptr@.provenance == final(self).bench->0@.provenance
                &&& final(self).backed is CheckedOut
                &&& perm@.is_range(addr as int, PAGE_BYTES as int)
                &&& perm@.provenance() == final(self).bench->0@.provenance
            },
        no_unwind
    {
        proof {
            lemma_opt_alloc_wf(&self.alloc);
        }
        let is_empty_backed = match self.backed {
            BackedPage::Empty => true,
            _ => false,
        };
        if self.alloc.is_none() || self.bench.is_none() || !is_empty_backed {
            return None;
        }
        let Some(ptr) = self.span else {
            return None;
        };
        let (_, caller_opt) = lend_caller_from(&mut self.alloc);
        let Some(mut caller) = caller_opt else {
            return None;
        };
        let got = back_from_opt(&mut self.bench, &self.alloc, &mut caller, ptr);
        give_back_to(&mut self.alloc, caller);
        let Some(perm) = got else {
            return None;
        };
        self.backed = BackedPage::CheckedOut;
        Some((ptr, perm))
    }

    fn bench_back_finish(&mut self, addr: usize, perm: Tracked<PointsToRaw>)
        requires
            old(self).inv(),
            old(self).bench is Some,
            old(self).span matches Some(sp) && sp@.addr == addr,
            old(self).backed is CheckedOut,
            perm@.is_range(addr as int, PAGE_BYTES as int),
            perm@.provenance() == old(self).bench->0@.provenance,
        ensures
            final(self).inv(),
        no_unwind
    {
        self.backed = BackedPage::Held(addr, perm);
    }

    fn bench_release(&mut self) -> (r: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
        no_unwind
    {
        proof {
            lemma_opt_alloc_wf(&self.alloc);
        }
        if self.alloc.is_none() || self.bench.is_none() {
            return false;
        }
        let Some(ptr) = self.span else {
            return false;
        };
        let mut backed = BackedPage::Empty;
        core::mem::swap(&mut self.backed, &mut backed);
        let BackedPage::Held(addr, perm) = backed else {
            core::mem::swap(&mut self.backed, &mut backed);
            return false;
        };
        let sp_addr = ptr.addr();
        let (_, caller_opt) = lend_caller_from(&mut self.alloc);
        let Some(mut caller) = caller_opt else {
            self.backed = BackedPage::Held(addr, perm);
            return false;
        };
        release_from_opt(&mut self.bench, &mut caller, sp_addr, addr, perm);
        give_back_to(&mut self.alloc, caller);
        proof {
            assert(run_pages(addr as int, 1nat).contains(addr as int));
            assert(self.bench->0@.spans[sp_addr as int].backed =~= Set::empty());
        }
        true
    }

    fn bench_release_span(&mut self) -> (r: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
        no_unwind
    {
        proof {
            lemma_opt_alloc_wf(&self.alloc);
        }
        let is_empty_backed = match self.backed {
            BackedPage::Empty => true,
            _ => false,
        };
        if self.alloc.is_none() || self.bench.is_none() || !is_empty_backed {
            return false;
        }
        let Some(ptr) = self.span.take() else {
            return false;
        };
        let sp_addr = ptr.addr();
        let (_, caller_opt) = lend_caller_from(&mut self.alloc);
        let Some(mut caller) = caller_opt else {
            self.span = Some(ptr);
            return false;
        };
        release_span_from_opt(&mut self.bench, &mut caller, sp_addr);
        give_back_to(&mut self.alloc, caller);
        true
    }
}

impl PairedEager {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.state.inv()
    }

    /// Returns an empty `PairedEager` holder ready for heap placement prior to `init_in`.
    #[inline(never)]
    pub fn empty() -> Self {
        PairedEager {
            state: PairedState { alloc: None, bench: None, span: None, backed: BackedPage::Empty },
        }
    }

    /// Moves an `Allocator<Eager>` out of `alloc_slot` and pairs it with a fresh `Eager` over
    /// `(untyped, memory, pages, slots, window)` inside `self` (using `bench_slot` as temporary
    /// storage), returning `false` and leaving `alloc_slot` untouched if any slot is invalid,
    /// `Eager::new` refuses, or the two sources are not apart over `SIZE_512G`-aligned lower-half
    /// windows.
    #[inline(never)]
    pub fn init_in(
        &mut self,
        alloc_slot: &mut Option<Allocator<Eager>>,
        bench_slot: &mut Option<Eager>,
        untyped: u64,
        memory: u64,
        pages: usize,
        slots: u64,
        window: *mut u8,
    ) -> (r: bool)
        requires
            *old(alloc_slot) matches Some(a) ==> (a.held() ==> window_unclaimed(a.token()->0, window@.addr)),
    {
        proof {
            use_type_invariant(&*self);
        }
        if !self.state.is_empty() || bench_slot.is_some() {
            return false;
        }
        if !prepare_bench_in(alloc_slot, bench_slot, untyped, memory, pages, slots, window) {
            return false;
        }
        self.state.pack_from(alloc_slot, bench_slot);
        true
    }

    /// Moves the paired global `Allocator<Eager>` from `self` back into `alloc_slot`.
    #[inline(never)]
    pub fn restore_into(&mut self, alloc_slot: &mut Option<Allocator<Eager>>) -> bool {
        proof {
            use_type_invariant(&*self);
        }
        self.state.restore_into(alloc_slot)
    }

    /// Reserves a 1-block span in `self.bench` when no span is currently held.
    pub fn bench_reserve(&mut self) -> bool {
        proof {
            use_type_invariant(&*self);
        }
        self.state.bench_reserve()
    }

    /// Backs the first page of the reserved span; when `verify_rw` is true, writes and reads back
    /// a sentinel byte through the returned permission.
    pub fn bench_back(&mut self, verify_rw: bool) -> bool {
        proof {
            use_type_invariant(&*self);
        }
        let Some((ptr, mut perm)) = self.state.bench_back_start() else {
            return false;
        };
        let addr = ptr.addr();
        let mut ok = true;
        if verify_rw {
            let (byte, rest) = put(ptr, perm, 0x5au8);
            let (value, restored) = take(ptr, byte, rest);
            perm = restored;
            ok = value == 0x5a;
        }
        self.state.bench_back_finish(addr, perm);
        ok
    }

    /// Releases the backed first page of the reserved span.
    pub fn bench_release(&mut self) -> bool {
        proof {
            use_type_invariant(&*self);
        }
        self.state.bench_release()
    }

    /// Releases the reserved span when no backed page remains inside it.
    pub fn bench_release_span(&mut self) -> bool {
        proof {
            use_type_invariant(&*self);
        }
        self.state.bench_release_span()
    }
}

} // verus!
