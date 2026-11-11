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
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::layout::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;

use aheap::arch::*;
use aheap::source::*;

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
fn apart<S: SpanSource>(src: &mut S, base: *mut u8) -> (r: bool)
    requires
        old(src)@.wf(),
        old(src)@.spans.contains_key(base@.addr as int),
        old(src)@.spans[base@.addr as int].blocks == 1,
        old(src)@.spans[base@.addr as int].backed =~= Set::empty(),
        base@.provenance == old(src)@.provenance,
        base@.addr as int % BLOCK_BYTES as int == 0,
        base@.addr + BLOCK_BYTES <= usize::MAX + 1,
    ensures
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
    let first = match src.back(Ghost(span), x, 1) {
        None => return false,
        Some(perm) => perm,
    };
    let (byte, rest) = put(base, first, 1);
    let (_, first) = take(base, byte, rest);
    src.release(Ghost(span), x, 1, first);
    assert(src@.spans[span].backed =~= start.spans[span].backed);
    assert(src@.spans =~= start.spans);
    let second = match src.back(Ghost(span), y, 1) {
        None => return false,
        Some(perm) => perm,
    };
    let (yb, yrest) = put(py, second, 2);
    let first = match src.back(Ghost(span), x, 1) {
        None => {
            let (_, second) = take(py, yb, yrest);
            src.release(Ghost(span), y, 1, second);
            assert(src@.spans[span].backed =~= start.spans[span].backed);
            assert(src@.spans =~= start.spans);
            return false;
        },
        Some(perm) => perm,
    };
    let (xb, xrest) = put(base, first, 3);
    let (seen, second) = take(py, yb, yrest);
    let (_, first) = take(base, xb, xrest);
    src.release(Ghost(span), y, 1, second);
    src.release(Ghost(span), x, 1, first);
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
pub fn exercise<S: SpanSource>(src: &mut S) -> (seen: Exercised)
    requires
        old(src)@.wf(),
    ensures
        final(src)@.spans == old(src)@.spans,
        final(src)@.provenance == old(src)@.provenance,
{
    let ghost start = src@;
    let nothing = Exercised { backed: 0, refused: false, read: false, again: false, apart: false, fresh: false };
    let base = match src.reserve(1) {
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
    let apart = apart(src, base);
    assert(src@.spans =~= reserved.spans.insert(addr as int, Span { blocks: 1, backed: run_pages(addr as int, 0) }));
    let tracked mut run = PointsToRaw::empty(provenance);
    let mut k: usize = 0;
    let mut limit = BLOCK_PAGES;
    while k < limit
        invariant
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
        match src.back(Ghost(addr as int), page, 1) {
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
        src.release(Ghost(addr as int), addr, k, Tracked(whole));
    }
    assert(src@.spans[addr as int].backed =~= Set::empty());
    assert(src@.spans =~= reserved.spans);
    proof {
        lemma_page_aligned(addr as int, 0);
        lemma_run_grows(addr as int, 0);
    }
    let again = match src.back(Ghost(addr as int), addr, 1) {
        None => false,
        Some(perm) => {
            src.release(Ghost(addr as int), addr, 1, perm);
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
        match src.back(Ghost(addr as int), page, 1) {
            None => {},
            Some(perm) => {
                let (byte, rest) = put(p, perm, 9);
                let (value, perm) = take(p, byte, rest);
                fresh = value == 9;
                src.release(Ghost(addr as int), page, 1, perm);
            },
        }
        assert(src@.spans[addr as int].backed =~= Set::empty());
        assert(src@.spans =~= reserved.spans);
    }
    src.release_span(addr);
    assert(src@.spans =~= start.spans);
    Exercised { backed: k, refused, read, again, apart, fresh }
}

} // verus!
