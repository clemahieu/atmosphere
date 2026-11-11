// SPDX-License-Identifier: MIT

//! A verified use of the span source contract that runs, where the witness in aheap is built into no
//! image: from any well-formed source it reserves a span of one block, backs its pages one at a time
//! until the source refuses or the block is full, writes a byte through the run's permission and reads
//! it back, releases the run, backs one page again and releases it, and gives the span back, ending
//! with the spans it started with; only the source's count of refusals may have grown. What it saw is
//! the caller's to judge: dom0 prints it.
use vstd::arithmetic::div_mod::*;
use vstd::layout::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::set::*;

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
    let nothing = Exercised { backed: 0, refused: false, read: false, again: false };
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
    src.release_span(addr);
    assert(src@.spans =~= start.spans);
    Exercised { backed: k, refused, read, again }
}

} // verus!
