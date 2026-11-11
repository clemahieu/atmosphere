// SPDX-License-Identifier: MIT

//! The witnesses: verified sequences of operations, built into no image, that reach the uses the
//! span source and the block buddy exist for.
//!
//! The span source's witness, from any well-formed source, reserves a span of one block, backs
//! its first page, writes a byte through the permission back returned and reads it again, releases
//! the page and the span, and ends with the view it started with. A source that refuses leaves the
//! view as it was with the refusal counted, and the sequence stops there.
//!
//! The page buddy's witness, over any well-formed source and with no spares, cuts a run of order 0
//! and one of order BLOCK_ORDER, frees both, and ends holding no span, with the source's view the one
//! it started with. A refusal stops the sequence after freeing what it cut, and the page buddy refuses
//! only when the source did, so a source that refused nothing during the sequence gave both runs. Its
//! second witness, with one spare, cuts a run, frees it so its span stays as the spare, and cuts
//! again, which is shown to succeed whatever the source does. Its third, with no spares, cuts MANY
//! whole blocks, each in a span of its own and all held at once, more spans than one page of block
//! buddy records would hold, until the source refuses; frees them all and ends with the source's view
//! the one it started with, so a source that refused nothing gave all MANY.
//!
//! The backed run's witness, over any well-formed source and with no spares, cuts a run of order 0,
//! backs it, writes a byte through the permission and reads it again, releases the run's page and
//! frees the run, ending as the page buddy's witness does: a source that refused nothing gave the
//! byte.
use vstd::prelude::*;
use vstd::layout::*;
use vstd::raw_ptr::*;

use crate::arch::*;
use crate::buddy::*;
use crate::page::*;
use crate::source::*;

verus! {

broadcast use group_raw_ptr_axioms;

/// Writes and reads one byte of a span `src` backs, and gives the span back. Returns whether the
/// byte was written: false when the source refused to reserve or to back, which it did once.
pub fn witness_one_page<S: SpanSource>(src: &mut S) -> (wrote: bool)
    requires
        old(src)@.wf(),
    ensures
        final(src)@ == if wrote {
            old(src)@
        } else {
            old(src)@.refused()
        },
{
    let ghost start = src@;
    let base = match src.reserve(1) {
        None => return false,
        Some(base) => base,
    };
    let addr = base.addr();
    let ghost reserved = src@;
    assert(!start.spans.contains_key(addr as int));
    let perm = match src.back(Ghost(addr as int), addr, 1) {
        None => {
            src.release_span(addr);
            assert(src@.spans =~= start.spans);
            assert(src@ == start.refused());
            return false;
        },
        Some(perm) => perm,
    };
    let tracked run = perm.get();
    let ghost page = Set::range(addr as int, addr as int + PAGE_BYTES as int);
    let ghost first = Set::range(addr as int, addr as int + 1);
    let tracked (one, rest) = run.split(first);
    assert(size_of::<u8>() == 1 && align_of::<u8>() == 1) by {
        broadcast use layout_of_primitives, align_of_u8;
    }
    assert(one.is_range(addr as int, size_of::<u8>() as int));
    let tracked mut byte = one.into_typed::<u8>(addr);
    ptr_mut_write(base, Tracked(&mut byte), 7u8);
    let v = ptr_mut_read(base, Tracked(&mut byte));
    assert(v == 7u8);
    let tracked raw = byte.into_raw();
    let tracked whole = raw.join(rest);
    assert(whole.dom() =~= page);
    src.release(Ghost(addr as int), addr, 1, Tracked(whole));
    assert(src@.spans[addr as int].backed =~= Set::empty());
    assert(src@.spans =~= reserved.spans);
    src.release_span(addr);
    assert(src@.spans =~= start.spans);
    true
}

} // verus!

verus! {

/// The block buddy's witness: from the initial value it cuts a run of order 0 and frees it, takes
/// the whole block, is refused a run of order 0 while the block is taken, frees the block, and ends
/// with the initial view.
pub fn witness_block_buddy() -> (b: BlockBuddy)
    ensures
        b.wf(),
        b.blocks() == initial(),
{
    let mut b = BlockBuddy::new();
    assert(b.blocks().contains_key(0) && b.blocks()[0].free);
    assert(b.used() =~= Map::<int, nat>::empty());
    let small = b.alloc(0);
    let p = small.unwrap();
    assert(b.used() =~= Map::<int, nat>::empty().insert(p as int, 0nat));
    b.free(p);
    assert(b.used().dom() =~= Set::<int>::empty());
    proof {
        b.lemma_idle();
        lemma_block_pages();
    }
    assert(b.blocks().contains_key(0) && b.blocks()[0].free);
    let whole = b.alloc(BLOCK_ORDER).unwrap();
    assert(whole == 0);
    assert(b.used().contains_key(0) && b.used()[0] == BLOCK_ORDER as nat);
    assert(b.blocks().contains_key(0) && !b.blocks()[0].free && b.blocks()[0].order
        == BLOCK_ORDER);
    proof {
        b.lemma_view();
    }
    assert(!b.fits(0)) by {
        if b.fits(0) {
            let h = choose|h: int|
                #[trigger] b.blocks().contains_key(h) && b.blocks()[h].free && b.blocks()[h].order
                    >= 0;
            lemma_pages(b.blocks()[h].order, BLOCK_ORDER as nat);
            assert(placed(h, b.blocks()[h]));
            assert(h != 0);
            assert(h + pages(b.blocks()[h].order) <= 0 || 0 + pages(b.blocks()[0].order) <= h);
        }
    }
    let refused = b.alloc(0);
    assert(refused is None);
    b.free(whole);
    assert(b.used().dom() =~= Set::<int>::empty());
    proof {
        b.lemma_idle();
    }
    let idle = b.is_idle();
    assert(idle);
    b
}

} // verus!

verus! {

/// Taking a run span and giving it back leaves the view as it was.
proof fn lemma_took_released(s: SourceView, b: int)
    requires
        !s.spans.contains_key(b),
    ensures
        s.reserved(b, SPAN_BLOCKS as nat).backed_run(b, meta_page(b), 1).released_span(b) == s,
        s.refused().reserved(b, SPAN_BLOCKS as nat).backed_run(b, meta_page(b), 1) == s.reserved(
            b,
            SPAN_BLOCKS as nat,
        ).backed_run(b, meta_page(b), 1).refused(),
{
    assert(s.reserved(b, SPAN_BLOCKS as nat).backed_run(b, meta_page(b), 1).released_span(b).spans =~= s.spans);
}

/// Freeing a run cut in a block that was held already gives back the runs from before the cut, and
/// the cut run is the one at its head with its order.
proof fn lemma_uncut(before: Map<int, Map<int, nat>>, after: Map<int, Map<int, nat>>, p: int, k: nat)
    requires
        cut(before, after, p, k),
        before.contains_key(span_of(p)),
    ensures
        after.contains_key(span_of(p)),
        after[span_of(p)].contains_key(page_of(p)),
        after[span_of(p)][page_of(p)] == k,
        !before[span_of(p)].contains_key(page_of(p)),
        after.insert(span_of(p), after[span_of(p)].remove(page_of(p))) == before,
{
    let b = span_of(p);
    let h = page_of(p);
    lemma_pages_pos(k);
    if before[b].contains_key(h) {
        lemma_pages_pos(before[b][h]);
    }
    assert(after[b].remove(h) =~= before[b]);
    assert(after.insert(b, after[b].remove(h)) =~= before);
}

/// A run of order BLOCK_ORDER is at page 0 of its block.
proof fn lemma_whole_at_0(h: int)
    requires
        placed(h, Block { order: BLOCK_ORDER as nat, free: false }),
    ensures
        h == 0,
        pages(BLOCK_ORDER as nat) == BLOCK_PAGES as int,
{
    lemma_block_pages();
}

/// Cuts a small run and a whole block from a page buddy over `src` keeping no spare, frees both, and
/// returns the page buddy, which then holds no span and has given every span back to the source, with
/// whether both runs were cut: they were exactly when the source refused nothing, and otherwise it
/// refused once.
pub fn witness_page_buddy<S: SpanSource>(src: S) -> (r: (PageBuddy<S>, bool))
    requires
        src@.wf(),
    ensures
        r.0.wf(),
        r.0.spans().dom() == Set::<int>::empty(),
        r.0.source() == if r.1 {
            src@
        } else {
            src@.refused()
        },
        r.1 == (r.0.source().refusals == src@.refusals),
{
    let mut pb = PageBuddy::new(src, 0);
    let ghost s0 = pb.source();
    assert(pb.spans().dom() =~= Set::<int>::empty());
    let small = match pb.alloc_run(0) {
        Err(_) => {
            return (pb, false);
        },
        Ok(p) => p,
    };
    let ghost b1 = span_of(small as int);
    let ghost m1 = meta_page(b1);
    let ghost h1 = page_of(small as int);
    let ghost fr1 = fresh(Map::<int, Map<int, nat>>::empty(), b1);
    let ghost u1 = pb.used();
    let ghost s1 = pb.source();
    let ghost spans1 = pb.spans();
    proof {
        lemma_uncut(fr1, u1, small as int, 0);
        lemma_took_released(s0, b1);
        assert(u1[b1].contains_key(h1));
        assert(u1[m1] == Map::<int, nat>::empty());
        assert(spans1.dom() =~= set![b1, m1]);
        pb.lemma_view();
        lemma_pages_pos(0);
    }
    let whole = match pb.alloc_run(BLOCK_ORDER) {
        Err(_) => {
            assert(pb.used() == u1);
            pb.free_run(small);
            proof {
                assert(fr1[b1].dom() =~= Set::<int>::empty());
                assert(pb.used().dom() =~= Set::<int>::empty());
                pb.lemma_view();
            }
            return (pb, false);
        },
        Ok(p) => p,
    };
    let ghost c2 = span_of(whole as int);
    let ghost h2 = page_of(whole as int);
    proof {
        lemma_whole_at_0(h2);
        if spans1.contains_key(c2) {
            // The only held blocks are the small run's, with no room for a whole block, and the
            // metadata page's, whose page 0 is allocated.
            if c2 == b1 {
                assert(h2 + pages(BLOCK_ORDER as nat) <= h1 || h1 + pages(u1[b1][h1]) <= h2);
            } else {
                assert(c2 == m1);
                assert(pb.metas().contains(m1));
            }
        }
    }
    let ghost b2 = c2;
    let ghost m2 = meta_page(b2);
    let ghost u2 = pb.used();
    let ghost s2 = pb.source();
    proof {
        assert(!spans1.contains_key(b2));
        assert(b2 != b1 && b2 != m1);
        lemma_uncut(fresh(u1, b2), u2, whole as int, BLOCK_ORDER as nat);
        lemma_took_released(s1, b2);
        assert(u2[b1] == u1[b1]);
        assert(u2[b2].remove(h2) =~= Map::<int, nat>::empty());
        assert(u2[m2] == Map::<int, nat>::empty());
        pb.lemma_view();
    }
    pb.free_run(whole);
    proof {
        assert(pb.used() =~= u1);
        assert(pb.source() == s1);
        assert(pb.span_base(span_of(small as int)) == b1);
    }
    pb.free_run(small);
    proof {
        assert(fr1[b1].dom() =~= Set::<int>::empty());
        assert(pb.used().dom() =~= Set::<int>::empty());
        pb.lemma_view();
    }
    (pb, true)
}

/// The whole blocks the many-spans witness cuts: more than one page of block buddy records would
/// hold, so no table of records in a page bounds the spans the page buddy holds.
pub const MANY: usize = PAGE_BYTES / BLOCK_PAGES + 1;

/// The source's view `s` is `start`, with one more refusal when `refused`, and with a span for each
/// first block `used` holds, every span of `start` as it was.
spec fn added(start: SourceView, s: SourceView, used: Map<int, Map<int, nat>>, metas: Set<int>, refused: bool) -> bool {
    &&& s.provenance == start.provenance
    &&& s.refusals == start.refusals + if refused { 1nat } else { 0nat }
    &&& forall|c: int|
        #![trigger s.spans.contains_key(c)]
        #![trigger start.spans.contains_key(c)]
        #![trigger used.contains_key(c)]
        s.spans.contains_key(c) <==> start.spans.contains_key(c) || (used.contains_key(c) && !metas.contains(c))
    &&& forall|c: int| #[trigger]
        start.spans.contains_key(c) ==> !(used.contains_key(c) && !metas.contains(c)) && s.spans[c] == start.spans[c]
}

/// Cuts runs of a whole block from a page buddy over `src` keeping no spare, each in a span of its
/// own and all held at once, until MANY are held or the source refuses; frees them and returns the
/// page buddy, which then holds no span and has given every span back to the source, with how many
/// it cut: MANY exactly when the source refused nothing, and otherwise fewer, the source having
/// refused once.
pub fn witness_page_buddy_many<S: SpanSource>(src: S) -> (r: (PageBuddy<S>, usize))
    requires
        src@.wf(),
    ensures
        r.0.wf(),
        r.0.spans().dom() == Set::<int>::empty(),
        r.1 <= MANY,
        r.0.source() == if r.1 == MANY {
            src@
        } else {
            src@.refused()
        },
{
    let ghost start = src@;
    let mut pb = PageBuddy::new(src, 0);
    let ghost whole = Map::<int, nat>::empty().insert(0, BLOCK_ORDER as nat);
    let mut runs = [0usize; MANY];
    let mut n: usize = 0;
    let mut go = true;
    proof {
        lemma_block_pages();
        assert(pb.used().dom() =~= Set::<int>::empty());
        assert(whole.remove(0) =~= Map::<int, nat>::empty());
    }
    while go && n < MANY
        invariant
            pb.wf(),
            pb.spares() == 0,
            n <= MANY,
            go || n < MANY,
            pages(BLOCK_ORDER as nat) == BLOCK_PAGES as int,
            whole == Map::<int, nat>::empty().insert(0, BLOCK_ORDER as nat),
            whole.remove(0) == Map::<int, nat>::empty(),
            added(start, pb.source(), pb.used(), pb.metas(), !go),
            forall|j: int|
                0 <= j < n ==> {
                    &&& (#[trigger] runs@[j]) as int % BLOCK_BYTES as int == 0
                    &&& pb.used().contains_key(runs@[j] as int)
                    &&& pb.used()[runs@[j] as int] == whole
                    &&& !pb.metas().contains(runs@[j] as int)
                    &&& pb.source().unbacked(runs@[j] as int, runs@[j] as int, BLOCK_PAGES as nat)
                },
            forall|i: int, j: int| 0 <= i < j < n ==> runs@[i] != runs@[j],
            forall|b: int|
                #[trigger] pb.used().contains_key(b) ==> pb.metas().contains(b) || exists|j: int|
                    0 <= j < n && runs@[j] as int == b,
            forall|m: int| #[trigger] pb.metas().contains(m) ==> pb.used()[m] == Map::<int, nat>::empty(),
        decreases MANY - n + if go { 1int } else { 0int },
    {
        let ghost u0 = pb.used();
        let ghost s0 = pb.source();
        let ghost metas0 = pb.metas();
        let ghost spans0 = pb.spans();
        proof {
            pb.lemma_view();
        }
        match pb.alloc_run(BLOCK_ORDER) {
            Err(e) => {
                assert(e is Source);
                go = false;
            },
            Ok(p) => {
                proof {
                    let c = span_of(p as int);
                    let h = page_of(p as int);
                    lemma_whole_at_0(h);
                    lemma_head(p as int);
                    if spans0.contains_key(c) {
                        // A held first block holds a whole run already, and a held second block's
                        // page 0 is its metadata page.
                        if metas0.contains(c) {
                            assert(spans0[c][0] == (Block { order: 0, free: false }));
                        } else {
                            let j = choose|j: int| 0 <= j < n && runs@[j] as int == c;
                            assert(u0[c] == whole);
                            assert(u0[c].contains_key(0));
                            assert(h + pages(BLOCK_ORDER as nat) <= 0 || 0 + pages(u0[c][0]) <= h);
                        }
                    }
                    let b = c;
                    let mb = meta_page(b);
                    assert(p as int == b);
                    lemma_uncut(fresh(u0, b), pb.used(), p as int, BLOCK_ORDER as nat);
                    assert(pb.used()[b] =~= whole);
                    assert(pb.used() =~= u0.insert(b, whole).insert(mb, Map::<int, nat>::empty()));
                    let s = pb.source();
                    assert(!s0.spans.contains_key(b));
                    assert(!metas0.contains(b) && !u0.contains_key(b) && !u0.contains_key(mb));
                    assert forall|c2: int| #[trigger] start.spans.contains_key(c2) implies !(pb.used().contains_key(c2)
                        && !pb.metas().contains(c2)) && s.spans[c2] == start.spans[c2] by {
                        assert(s0.spans.contains_key(c2));
                    }
                    assert forall|c2: int|
                        #![trigger s.spans.contains_key(c2)]
                        #![trigger start.spans.contains_key(c2)]
                        #![trigger pb.used().contains_key(c2)]
                        s.spans.contains_key(c2) <==> start.spans.contains_key(c2) || (pb.used().contains_key(c2)
                            && !pb.metas().contains(c2)) by {
                        if c2 != b && c2 != mb {
                            assert(s.spans.contains_key(c2) == s0.spans.contains_key(c2));
                            assert(pb.used().contains_key(c2) == u0.contains_key(c2));
                        }
                        if c2 == mb {
                            assert(s.spans.contains_key(c2) == s0.spans.contains_key(c2));
                            if !u0.contains_key(c2) && !start.spans.contains_key(c2) {
                                assert(!s0.spans.contains_key(c2));
                            }
                        }
                    }
                    assert forall|j: int| 0 <= j < n implies pb.source().unbacked(
                        runs@[j] as int,
                        runs@[j] as int,
                        BLOCK_PAGES as nat,
                    ) by {
                        let c2 = runs@[j] as int;
                        assert(u0.contains_key(c2));
                        assert(s0.spans.contains_key(c2));
                        assert(pb.source().spans[c2] == s0.spans[c2]);
                    }
                    assert forall|m: int| #[trigger] pb.metas().contains(m) implies pb.used()[m] == Map::<int, nat>::empty() by {
                        if m != mb {
                            assert(metas0.contains(m));
                        }
                    }
                }
                let ghost r0 = runs@;
                runs[n] = p;
                n = n + 1;
                proof {
                    assert forall|c: int| #[trigger] pb.used().contains_key(c) implies pb.metas().contains(c) || exists|j: int|
                        0 <= j < n && runs@[j] as int == c by {
                        if c == p as int {
                            assert(runs@[n - 1] == p);
                        } else if c != meta_page(p as int) {
                            assert(u0.contains_key(c));
                            if !metas0.contains(c) {
                                let j = choose|j: int| 0 <= j < n - 1 && r0[j] as int == c;
                                assert(runs@[j] == r0[j]);
                            }
                        }
                    }
                }
            },
        }
    }
    let cut = n;
    while n > 0
        invariant
            pb.wf(),
            pb.spares() == 0,
            n <= cut <= MANY,
            go == (cut == MANY),
            pages(BLOCK_ORDER as nat) == BLOCK_PAGES as int,
            whole == Map::<int, nat>::empty().insert(0, BLOCK_ORDER as nat),
            whole.remove(0) == Map::<int, nat>::empty(),
            added(start, pb.source(), pb.used(), pb.metas(), !go),
            forall|j: int|
                0 <= j < n ==> {
                    &&& (#[trigger] runs@[j]) as int % BLOCK_BYTES as int == 0
                    &&& pb.used().contains_key(runs@[j] as int)
                    &&& pb.used()[runs@[j] as int] == whole
                    &&& !pb.metas().contains(runs@[j] as int)
                    &&& pb.source().unbacked(runs@[j] as int, runs@[j] as int, BLOCK_PAGES as nat)
                },
            forall|i: int, j: int| 0 <= i < j < n ==> runs@[i] != runs@[j],
            forall|b: int|
                #[trigger] pb.used().contains_key(b) ==> pb.metas().contains(b) || exists|j: int|
                    0 <= j < n && runs@[j] as int == b,
            forall|m: int| #[trigger] pb.metas().contains(m) ==> pb.used()[m] == Map::<int, nat>::empty(),
        decreases n,
    {
        n = n - 1;
        let p = runs[n];
        let ghost u0 = pb.used();
        let ghost s0 = pb.source();
        let ghost metas0 = pb.metas();
        let ghost mp = meta_page(p as int);
        proof {
            pb.lemma_view();
            assert(runs@[n as int] == p);
            lemma_block_head(p as int);
            assert(u0[p as int] == whole);
            assert(metas0.contains(mp));
            assert(u0[mp] == Map::<int, nat>::empty());
            assert(u0.insert(p as int, u0[p as int].remove(0))[p as int].dom() =~= Set::<int>::empty());
            assert(u0.insert(p as int, u0[p as int].remove(0))[mp].dom() =~= Set::<int>::empty());
        }
        pb.free_run(p);
        proof {
            let s = pb.source();
            assert(pb.used() == u0.remove(p as int).remove(mp));
            assert(pb.metas() == metas0.remove(mp));
            assert(s == s0.released_span(p as int));
            assert forall|c: int| #[trigger] start.spans.contains_key(c) implies !(pb.used().contains_key(c)
                && !pb.metas().contains(c)) && s.spans[c] == start.spans[c] by {
                assert(s0.spans.contains_key(c));
                assert(c != p as int);
            }
            assert forall|c: int|
                #![trigger s.spans.contains_key(c)]
                #![trigger start.spans.contains_key(c)]
                #![trigger pb.used().contains_key(c)]
                s.spans.contains_key(c) <==> start.spans.contains_key(c) || (pb.used().contains_key(c)
                    && !pb.metas().contains(c)) by {
                assert(s.spans.contains_key(c) == (s0.spans.contains_key(c) && c != p as int));
                if c == p as int {
                    assert(!start.spans.contains_key(c));
                } else if c != mp {
                    assert(pb.used().contains_key(c) == u0.contains_key(c));
                }
            }
            assert forall|j: int| 0 <= j < n implies pb.source().unbacked(
                runs@[j] as int,
                runs@[j] as int,
                BLOCK_PAGES as nat,
            ) by {
                let c = runs@[j] as int;
                assert(u0.contains_key(c));
                assert(s0.spans.contains_key(c));
                assert(c != p as int);
                assert(pb.source().spans[c] == s0.spans[c]);
            }
            assert forall|j: int| 0 <= j < n implies (#[trigger] runs@[j]) as int != mp by {
                assert(!metas0.contains(runs@[j] as int));
            }
            assert forall|b: int| #[trigger] pb.used().contains_key(b) implies pb.metas().contains(b) || exists|j: int|
                0 <= j < n && runs@[j] as int == b by {
                assert(u0.contains_key(b));
                if !metas0.contains(b) {
                    let j = choose|j: int| 0 <= j < n + 1 && runs@[j] as int == b;
                    assert(j != n);
                }
            }
        }
    }
    proof {
        pb.lemma_view();
        // A held metadata page has its span's first block held too, and that is no metadata page,
        // so it would be a run left in the list.
        assert forall|b: int| !pb.used().contains_key(b) by {
            if pb.used().contains_key(b) && pb.metas().contains(b) {
                assert(pb.used().contains_key(b - BLOCK_BYTES as int));
            }
        }
        assert(pb.used().dom() =~= Set::<int>::empty());
        let s = pb.source();
        assert(s.spans.dom() =~= start.spans.dom());
        assert(s.spans =~= start.spans);
    }
    (pb, cut)
}

/// The block at `p`, block-aligned, has its page 0 at `p`.
proof fn lemma_block_head(p: int)
    requires
        p % BLOCK_BYTES as int == 0,
    ensures
        span_of(p) == p,
        page_of(p) == 0,
        p % PAGE_BYTES as int == 0,
{
    vstd::arithmetic::div_mod::lemma_mod_mod(p, PAGE_BYTES as int, BLOCK_PAGES as int);
}

/// Cuts a run from a page buddy over `src` keeping one spare, frees it, so its span stays as the
/// spare, and cuts a run again, which the idle spare provably gives without asking the source; then
/// frees that run and returns the page buddy, every held span of it idle.
pub fn witness_page_buddy_spare<S: SpanSource>(src: S) -> (pb: PageBuddy<S>)
    requires
        src@.wf(),
    ensures
        pb.wf(),
        pb.spares() == 1,
        forall|b: int| #[trigger] pb.used().contains_key(b) ==> pb.used()[b].dom() == Set::<int>::empty(),
{
    let mut pb = PageBuddy::new(src, 1);
    let first = match pb.alloc_run(0) {
        Err(_) => {
            assert(pb.used().dom() =~= Set::<int>::empty());
            return pb;
        },
        Ok(p) => p,
    };
    let ghost b1 = span_of(first as int);
    let ghost m1 = meta_page(b1);
    let ghost fr = fresh(Map::<int, Map<int, nat>>::empty(), b1);
    proof {
        lemma_uncut(fr, pb.used(), first as int, 0);
        assert(pb.metas() =~= set![m1]);
        assert(pb.idle_spans() =~= Set::<int>::empty()) by {
            assert(pb.used()[b1].contains_key(page_of(first as int)));
        }
        assert(fr[b1].dom() =~= Set::<int>::empty());
        assert(fr[m1].dom() =~= Set::<int>::empty());
    }
    pb.free_run(first);
    proof {
        assert(pb.used() == fr);
        pb.lemma_view();
        pb.lemma_idle_fits(b1, 0);
    }
    let again = pb.alloc_run(0);
    assert(again is Ok);
    let second = match again {
        Ok(p) => p,
        Err(_) => return pb,
    };
    let ghost c2 = span_of(second as int);
    proof {
        assert(fr.contains_key(c2));
        lemma_uncut(fr, pb.used(), second as int, 0);
        assert(pb.metas() =~= set![m1]);
        assert(pb.idle_spans() =~= Set::<int>::empty()) by {
            assert(pb.used()[c2].contains_key(page_of(second as int)));
        }
    }
    pb.free_run(second);
    proof {
        assert(pb.used() == fr);
    }
    pb
}

/// Cuts a run of order 0 from a page buddy over `src` keeping no spare, backs it, writes a byte
/// through the permission and reads it again, releases the run's page and frees the run, and returns
/// the page buddy, which then holds no span and has given every span back to the source, with
/// whether the byte was written: it was exactly when the source refused nothing, and otherwise it
/// refused once.
pub fn witness_backed_run<S: SpanSource>(src: S) -> (r: (PageBuddy<S>, bool))
    requires
        src@.wf(),
    ensures
        r.0.wf(),
        r.0.spans().dom() == Set::<int>::empty(),
        r.0.source() == if r.1 {
            src@
        } else {
            src@.refused()
        },
        r.1 == (r.0.source().refusals == src@.refusals),
{
    let mut pb = PageBuddy::new(src, 0);
    let ghost s0 = pb.source();
    assert(pb.spans().dom() =~= Set::<int>::empty());
    let p = match pb.alloc_run(0) {
        Err(_) => {
            return (pb, false);
        },
        Ok(p) => p,
    };
    let ghost b = span_of(p as int);
    let ghost m = meta_page(b);
    let ghost fr = fresh(Map::<int, Map<int, nat>>::empty(), b);
    let ghost s1 = pb.source();
    proof {
        lemma_uncut(fr, pb.used(), p as int, 0);
        lemma_took_released(s0, b);
        assert(fr[b].dom() =~= Set::<int>::empty());
        assert(fr[m].dom() =~= Set::<int>::empty());
        assert(pages(0) == 1);
    }
    let (ptr, perm) = match pb.back_run(p, 0) {
        None => {
            pb.free_run(p);
            proof {
                assert(pb.used().dom() =~= Set::<int>::empty());
                pb.lemma_view();
            }
            return (pb, false);
        },
        Some(backed) => backed,
    };
    let tracked run = perm.get();
    let ghost first = Set::range(p as int, p as int + 1);
    let tracked (one_byte, rest) = run.split(first);
    assert(size_of::<u8>() == 1 && align_of::<u8>() == 1) by {
        broadcast use layout_of_primitives, align_of_u8;
    }
    assert(one_byte.is_range(p as int, size_of::<u8>() as int));
    let tracked mut byte = one_byte.into_typed::<u8>(p);
    ptr_mut_write(ptr, Tracked(&mut byte), 7u8);
    let v = ptr_mut_read(ptr, Tracked(&mut byte));
    assert(v == 7u8);
    let tracked raw = byte.into_raw();
    let tracked whole = raw.join(rest);
    assert(whole.dom() =~= Set::range(p as int, p as int + PAGE_BYTES as int));
    pb.release_run(p, 0, Tracked(whole));
    proof {
        assert(s1.spans[b].backed.disjoint(run_pages(p as int, 1)));
        assert(pb.source().spans[b].backed =~= s1.spans[b].backed);
        assert(pb.source().spans =~= s1.spans);
    }
    pb.free_run(p);
    proof {
        assert(pb.used().dom() =~= Set::<int>::empty());
        pb.lemma_view();
    }
    (pb, true)
}

} // verus!
