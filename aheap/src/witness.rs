// SPDX-License-Identifier: MIT

//! The witnesses: verified sequences of operations, built into no image, that reach the uses the
//! span source and the block buddy exist for.
//!
//! The span source's witness, from any well-formed source, reserves a span of one block, backs
//! its first page, writes a byte through the permission back returned and reads it again, releases
//! the page and the span, and ends with the view it started with. A source that refuses leaves the
//! view as it was with the refused request recorded, the reserve of one block while it held what it
//! held at the start, or the back of the span's first page while it held that and the span, and the
//! sequence stops there.
//!
//! The page buddy's witness, over any well-formed source and with no spares, cuts a run of order 0
//! and one of order BLOCK_ORDER, frees both, and ends holding no span, with the source's view the one
//! it started with. A refusal stops the sequence after freeing what it cut, and the page buddy refuses
//! only when the source refused a request for a new run span, the reserve of SPAN_BLOCKS blocks or the
//! back of its metadata page, asked while it held what it held at the start, with the first run's span
//! when the second run was refused; so a source that refused neither gave both runs. Its second
//! witness, with one spare, cuts a run, frees it so its span stays as the spare, and cuts again, which
//! is shown to succeed whatever the source does; only a refused request for the first span stops it.
//! Its third, with no spares, cuts MANY whole blocks, each in a span of its own and all held at once,
//! more spans than one page of block buddy records would hold, until the source refuses such a
//! request, asked while it held what it held at the start and run spans; frees them all and ends with
//! the source's view the one it started with, so a source that refused none gave all MANY.
//!
//! The backed run's witness, over any well-formed source and with no spares, cuts a run of order 0,
//! backs it, writes a byte through the permission and reads it again, releases the run's page and
//! frees the run, ending as the page buddy's witness does: a source that refused no request for the
//! run's span and not the back of the run's page, while it held the run's span, gave the byte.
//!
//! The slab's witnesses each take one backed page and make a slab of SLOT_MIN slots over it. The
//! first allocates a slot, writes a byte of it and reads it again, frees the slot, retires the slab
//! and holds the permission to the whole page again. The second allocates every slot, none refused,
//! and is refused one more. The third takes two backed pages and makes a slab over each, both
//! keeping their free slots in one map, and allocates a slot of the second slab and then of the
//! first, whose ownership of the map the frame lemma carries across the second slab's operations.
//!
//! The large-object map's witness, over any well-formed source, allocates an object of one byte
//! more than a block, writes a byte of it and reads it again, frees it, and ends with the map empty
//! and the source's view the one it started with. A refusal stops the sequence, and the map refuses
//! only when the source refused the reserve of the object's span or the back of its run, asked while
//! it held what it held at the start and, for the back, the new span; so a source that refused
//! neither gave the byte.
use vstd::prelude::*;
use vstd::layout::*;
use vstd::raw_ptr::*;

use crate::arch::*;
use crate::buddy::*;
use crate::large::*;
use crate::page::*;
use crate::slab::*;
use crate::source::*;

verus! {

broadcast use group_raw_ptr_axioms;

/// The refusal `r` is of the witness's request of a source whose view is `s`: the reserve of one
/// block while the source held the spans `s` holds, or the back of the first page of a span of one
/// block that fits beside them, while it held them and that span, unbacked.
pub open spec fn page_refusal(s: SourceView, r: Refusal) -> bool {
    match r.request {
        Request::Reserve { blocks } => blocks == 1 && r.spans == s.spans,
        Request::Back { span, start, pages } => {
            &&& start == span
            &&& pages == 1
            &&& s.fits(span, 1)
            &&& r.spans == s.reserved(span, 1).spans
        },
    }
}

/// Writes and reads one byte of a span `src` backs, and gives the span back. Returns whether the
/// byte was written: false when the source refused to reserve the span or to back its page, which
/// it did once.
pub fn witness_one_page<S: SpanSource>(src: &mut S) -> (wrote: bool)
    requires
        old(src)@.wf(),
    ensures
        if wrote {
            final(src)@ == old(src)@
        } else {
            &&& final(src)@ == old(src)@.recorded(final(src)@.refusals.last())
            &&& page_refusal(old(src)@, final(src)@.refusals.last())
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
            assert(src@ == start.recorded(Refusal {
                request: Request::Back { span: addr as int, start: addr as int, pages: 1 },
                spans: start.reserved(addr as int, 1).spans,
            }));
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

/// The view `s` with the run span at `b` taken: reserved, its metadata page backed.
pub open spec fn taken(s: SourceView, b: int) -> SourceView {
    s.reserved(b, SPAN_BLOCKS as nat).backed_run(b, meta_page(b), 1)
}

/// A run span at `b` as `alloc_run` takes it: SPAN_BLOCKS blocks, its metadata page backed.
pub open spec fn run_span(b: int) -> Span {
    Span { blocks: SPAN_BLOCKS as nat, backed: run_pages(meta_page(b), 1) }
}

/// `held` holds every span `start` holds, as `start` holds it, and otherwise only run spans as
/// `alloc_run` takes them.
pub open spec fn holds_runs(start: SourceView, held: SourceView) -> bool {
    &&& forall|c: int| #[trigger]
        start.spans.contains_key(c) ==> held.spans.contains_key(c) && held.spans[c] == start.spans[c]
    &&& forall|c: int| #[trigger]
        held.spans.contains_key(c) ==> start.spans.contains_key(c) || held.spans[c] == run_span(c)
}

/// Taking a run span and giving it back leaves the view as it was.
proof fn lemma_took_released(s: SourceView, b: int)
    requires
        !s.spans.contains_key(b),
    ensures
        taken(s, b).released_span(b) == s,
{
    assert(taken(s, b).released_span(b).spans =~= s.spans);
}

/// Taking a run span, having a request refused and giving the span back leaves the view as it was
/// with that refusal recorded.
proof fn lemma_refused_released(s: SourceView, b: int, r: Refusal)
    requires
        !s.spans.contains_key(b),
    ensures
        taken(s, b).recorded(r).released_span(b) == s.recorded(r),
{
    assert(taken(s, b).recorded(r).released_span(b).spans =~= s.spans);
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
/// whether both runs were cut and the small run's address: both were cut unless the source refused a
/// request for a new run span, which it then did once, holding what it held at the start, and the
/// small run's span when that was cut.
pub fn witness_page_buddy<S: SpanSource>(src: S) -> (r: (PageBuddy<S>, bool, Ghost<int>))
    requires
        src@.wf(),
    ensures
        r.0.wf(),
        r.0.spans().dom() == Set::<int>::empty(),
        if r.1 {
            r.0.source() == src@
        } else {
            let f = r.0.source().refusals.last();
            &&& r.0.source() == src@.recorded(f)
            &&& span_refusal(src@, f) || {
                &&& !src@.spans.contains_key(span_of(r.2@))
                &&& span_refusal(taken(src@, span_of(r.2@)), f)
            }
        },
{
    let mut pb = PageBuddy::new(src, 0);
    let ghost s0 = pb.source();
    assert(pb.spans().dom() =~= Set::<int>::empty());
    let small = match pb.alloc_run(0) {
        Err(_) => {
            return (pb, false, Ghost(0));
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
            let ghost q = pb.source().refusals.last();
            pb.free_run(small);
            proof {
                assert(fr1[b1].dom() =~= Set::<int>::empty());
                assert(pb.used().dom() =~= Set::<int>::empty());
                pb.lemma_view();
                lemma_refused_released(s0, b1, q);
            }
            return (pb, false, Ghost(small as int));
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
    (pb, true, Ghost(small as int))
}

/// The whole blocks the many-spans witness cuts: more than one page of block buddy records would
/// hold, so no table of records in a page bounds the spans the page buddy holds.
pub const MANY: usize = PAGE_BYTES / BLOCK_PAGES + 1;

/// The source's view `s` is `start`, with one refused request for a new run span when `refused`,
/// asked while the source held what `held` holds, and with a run span for each first block `used`
/// holds, every span of `start` as it was.
spec fn added(
    start: SourceView,
    s: SourceView,
    used: Map<int, Map<int, nat>>,
    metas: Set<int>,
    refused: bool,
    held: SourceView,
) -> bool {
    &&& s.provenance == start.provenance
    &&& s.refusals == if refused {
        start.refusals.push(s.refusals.last())
    } else {
        start.refusals
    }
    &&& refused ==> span_refusal(held, s.refusals.last()) && holds_runs(start, held)
    &&& forall|c: int| #[trigger] s.spans.contains_key(c) ==> start.spans.contains_key(c) || s.spans[c] == run_span(c)
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
/// it cut: MANY unless the source refused a request for a new run span, and otherwise fewer, the
/// source having refused once, holding then what it held at the start and run spans, which the view
/// returned holds.
pub fn witness_page_buddy_many<S: SpanSource>(src: S) -> (r: (PageBuddy<S>, usize, Ghost<SourceView>))
    requires
        src@.wf(),
    ensures
        r.0.wf(),
        r.0.spans().dom() == Set::<int>::empty(),
        r.1 <= MANY,
        if r.1 == MANY {
            r.0.source() == src@
        } else {
            let f = r.0.source().refusals.last();
            &&& r.0.source() == src@.recorded(f)
            &&& span_refusal(r.2@, f)
            &&& holds_runs(src@, r.2@)
        },
{
    let ghost start = src@;
    let ghost mut held = start;
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
            added(start, pb.source(), pb.used(), pb.metas(), !go, held),
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
                proof {
                    held = s0;
                }
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
                    assert(s.spans[b].backed =~= run_pages(mb, 1));
                    assert forall|c2: int| #[trigger] s.spans.contains_key(c2) implies start.spans.contains_key(c2)
                        || s.spans[c2] == run_span(c2) by {
                        if c2 != b {
                            assert(s0.spans.contains_key(c2));
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
            added(start, pb.source(), pb.used(), pb.metas(), !go, held),
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
            assert forall|c: int| #[trigger] s.spans.contains_key(c) implies start.spans.contains_key(c)
                || s.spans[c] == run_span(c) by {
                assert(s0.spans.contains_key(c));
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
    (pb, cut, Ghost(held))
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
/// frees that run and returns the page buddy, every held span of it idle, with whether both runs were
/// cut: they were unless the source refused a request for the first run's span, which it then did
/// once, holding what it held at the start, and otherwise the source refused nothing.
pub fn witness_page_buddy_spare<S: SpanSource>(src: S) -> (r: (PageBuddy<S>, bool))
    requires
        src@.wf(),
    ensures
        r.0.wf(),
        r.0.spares() == 1,
        forall|b: int| #[trigger] r.0.used().contains_key(b) ==> r.0.used()[b].dom() == Set::<int>::empty(),
        if r.1 {
            r.0.source().refusals == src@.refusals
        } else {
            span_refused(src@, r.0.source())
        },
{
    let mut pb = PageBuddy::new(src, 1);
    let first = match pb.alloc_run(0) {
        Err(_) => {
            assert(pb.used().dom() =~= Set::<int>::empty());
            return (pb, false);
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
        Err(_) => return (pb, false),
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
    (pb, true)
}

/// Cuts a run of order 0 from a page buddy over `src` keeping no spare, backs it, writes a byte
/// through the permission and reads it again, releases the run's page and frees the run, and returns
/// the page buddy, which then holds no span and has given every span back to the source, with
/// whether the byte was written and the run's address: the byte was written unless the source refused
/// a request for the run's span, holding what it held at the start, or the back of the run's page,
/// holding that and the run's span, which it then did once.
pub fn witness_backed_run<S: SpanSource>(src: S) -> (r: (PageBuddy<S>, bool, Ghost<int>))
    requires
        src@.wf(),
    ensures
        r.0.wf(),
        r.0.spans().dom() == Set::<int>::empty(),
        if r.1 {
            r.0.source() == src@
        } else {
            span_refused(src@, r.0.source()) || {
                let b = span_of(r.2@);
                &&& !src@.spans.contains_key(b)
                &&& r.0.source() == src@.recorded(
                    Refusal { request: Request::Back { span: b, start: r.2@, pages: 1 }, spans: taken(src@, b).spans },
                )
            }
        },
{
    let mut pb = PageBuddy::new(src, 0);
    let ghost s0 = pb.source();
    assert(pb.spans().dom() =~= Set::<int>::empty());
    let p = match pb.alloc_run(0) {
        Err(_) => {
            return (pb, false, Ghost(0));
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
            let ghost q = pb.source().refusals.last();
            pb.free_run(p);
            proof {
                assert(pb.used().dom() =~= Set::<int>::empty());
                pb.lemma_view();
                lemma_refused_released(s0, b, q);
            }
            return (pb, false, Ghost(p as int));
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
    (pb, true, Ghost(p as int))
}

/// A page aligned to its size is aligned to the smallest slot, and holds between one and MAP_SLOTS
/// of them.
proof fn lemma_page_slots(page: *mut u8)
    requires
        page@.addr % PAGE_BYTES == 0,
    ensures
        page@.addr % SLOT_MIN == 0,
        PAGE_BYTES % SLOT_MIN == 0,
        SLOT_MIN <= PAGE_BYTES,
        0 < PAGE_BYTES / SLOT_MIN <= MAP_SLOTS,
{
    assert(PAGE_BYTES == (PAGE_BYTES / SLOT_MIN) * SLOT_MIN);
    let q = page@.addr as int / PAGE_BYTES as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(page@.addr as int, PAGE_BYTES as int);
    assert(page@.addr as int == (q * (PAGE_BYTES / SLOT_MIN) as int) * SLOT_MIN as int) by (nonlinear_arith)
        requires
            page@.addr as int == PAGE_BYTES as int * q + 0,
            PAGE_BYTES as int == (PAGE_BYTES / SLOT_MIN) as int * SLOT_MIN as int,
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        page@.addr as int,
        SLOT_MIN as int,
        q * (PAGE_BYTES / SLOT_MIN) as int,
        0,
    );
}

/// Makes a slab of SLOT_MIN slots over the backed page at `page`, allocates a slot, writes a byte
/// of it and reads it again, frees the slot, retires the slab and returns the permission to the
/// whole page.
pub fn witness_slab(page: *mut u8, run: Tracked<PointsToRaw>) -> (whole: Tracked<PointsToRaw>)
    requires
        page@.addr % PAGE_BYTES == 0,
        page@.addr + PAGE_BYTES <= usize::MAX,
        run@.is_range(page@.addr as int, PAGE_BYTES as int),
        run@.provenance() == page@.provenance,
    ensures
        whole@.is_range(page@.addr as int, PAGE_BYTES as int),
        whole@.provenance() == page@.provenance,
{
    let tracked mut perms = Map::<int, PointsToRaw>::tracked_empty();
    proof {
        lemma_page_slots(page);
    }
    let mut s = Slab::new(page, PAGE_BYTES, SLOT_MIN, run, Tracked(&mut perms));
    let ghost s0 = s;
    assert(s0.free_slots().contains(0));
    let (ptr, perm) = match s.alloc(Tracked(&mut perms)) {
        None => {
            assert(Set::<int>::empty().contains(0));
            unreached()
        },
        Some(slot) => slot,
    };
    let ghost s1 = s;
    let ghost a = ptr@.addr as int;
    let ghost i = s0.index(a);
    let tracked raw = perm.get();
    let tracked (one_byte, rest) = raw.split(Set::range(a, a + 1));
    assert(size_of::<u8>() == 1 && align_of::<u8>() == 1) by {
        broadcast use layout_of_primitives, align_of_u8;
    }
    assert(one_byte.is_range(a, size_of::<u8>() as int));
    let tracked mut byte = one_byte.into_typed::<u8>(ptr@.addr);
    ptr_mut_write(ptr, Tracked(&mut byte), 7u8);
    let v = ptr_mut_read(ptr, Tracked(&mut byte));
    assert(v == 7u8);
    let tracked back = byte.into_raw().join(rest);
    assert(back.dom() =~= Set::range(a, a + SLOT_MIN as int));
    s.free(ptr.addr(), Tracked(back), Tracked(&mut perms));
    assert(s.free_slots() =~= Set::range(0, s.count() as int));
    s.retire(Tracked(&mut perms))
}

/// Makes a slab of SLOT_MIN slots over the backed page at `page`, allocates every slot, none
/// refused, and is refused one more: returns whether it was.
pub fn witness_slab_full(page: *mut u8, run: Tracked<PointsToRaw>) -> (refused: bool)
    requires
        page@.addr % PAGE_BYTES == 0,
        page@.addr + PAGE_BYTES <= usize::MAX,
        run@.is_range(page@.addr as int, PAGE_BYTES as int),
        run@.provenance() == page@.provenance,
    ensures
        refused,
{
    let tracked mut perms = Map::<int, PointsToRaw>::tracked_empty();
    proof {
        lemma_page_slots(page);
    }
    let mut s = Slab::new(page, PAGE_BYTES, SLOT_MIN, run, Tracked(&mut perms));
    let n = PAGE_BYTES / SLOT_MIN;
    proof {
        broadcast use vstd::set_lib::range_set_properties;
        assert(s.free_slots().len() == n);
    }
    let mut k: usize = 0;
    while k < n
        invariant
            s.wf(),
            s.owns(perms),
            k <= n,
            s.free_slots().len() == n - k,
        decreases n - k,
    {
        let ghost before = s;
        match s.alloc(Tracked(&mut perms)) {
            None => {
                assert(before.free_slots().len() == 0);
                unreached()
            },
            Some(_) => {},
        }
        k += 1;
    }
    let ghost full = s;
    proof {
        vstd::set_lib::lemma_set_empty_equivalency_len(full.free_slots());
    }
    s.alloc(Tracked(&mut perms)).is_none()
}

/// Makes a slab of SLOT_MIN slots over each of the backed pages at `first` and `second`, both
/// keeping their free slots in one map, allocates a slot of the second and then a slot of the
/// first, whose ownership of the map the second's new and alloc left as it was: returns the two
/// slots, each in its own page.
pub fn witness_slab_pair(
    first: *mut u8,
    first_run: Tracked<PointsToRaw>,
    second: *mut u8,
    second_run: Tracked<PointsToRaw>,
) -> (slots: (*mut u8, *mut u8))
    requires
        first@.addr % PAGE_BYTES == 0,
        second@.addr % PAGE_BYTES == 0,
        first@.addr + PAGE_BYTES <= second@.addr,
        second@.addr + PAGE_BYTES <= usize::MAX,
        first_run@.is_range(first@.addr as int, PAGE_BYTES as int),
        first_run@.provenance() == first@.provenance,
        second_run@.is_range(second@.addr as int, PAGE_BYTES as int),
        second_run@.provenance() == second@.provenance,
    ensures
        first@.addr <= slots.0@.addr < first@.addr + PAGE_BYTES,
        second@.addr <= slots.1@.addr < second@.addr + PAGE_BYTES,
{
    let tracked mut perms = Map::<int, PointsToRaw>::tracked_empty();
    let ghost empty = perms;
    proof {
        lemma_page_slots(first);
        lemma_page_slots(second);
    }
    let mut a = Slab::new(first, PAGE_BYTES, SLOT_MIN, first_run, Tracked(&mut perms));
    let ghost made_a = perms;
    proof {
        assert forall|x: int| second@.addr <= x < second@.addr + PAGE_BYTES implies !made_a.contains_key(x) by {
            assert(!a.within(x));
            assert(!empty.contains_key(x));
        }
    }
    let mut b = Slab::new(second, PAGE_BYTES, SLOT_MIN, second_run, Tracked(&mut perms));
    let ghost made_b = perms;
    proof {
        assert forall|x: int| a.within(x) implies !b.within(x) by {}
        a.lemma_owns_frame(made_a, made_b);
    }
    assert(b.free_slots().contains(0));
    let (pb, _) = match b.alloc(Tracked(&mut perms)) {
        None => {
            assert(Set::<int>::empty().contains(0));
            unreached()
        },
        Some(slot) => slot,
    };
    let ghost took_b = perms;
    proof {
        assert(b.within(pb@.addr as int));
        assert forall|x: int| a.within(x) implies x != pb@.addr by {}
        a.lemma_owns_frame(made_b, took_b);
    }
    assert(a.free_slots().contains(0));
    let (pa, _) = match a.alloc(Tracked(&mut perms)) {
        None => {
            assert(Set::<int>::empty().contains(0));
            unreached()
        },
        Some(slot) => slot,
    };
    proof {
        assert(a.within(pa@.addr as int));
    }
    (pa, pb)
}

} // verus!

verus! {

/// Allocates an object of one byte more than a block from a new large-object map over `src`, writes
/// and reads its first byte, and frees it. Returns the map, empty again, with whether the byte was
/// written: false when the source refused the reserve of the object's span or the back of its run,
/// which it did once.
pub fn witness_large<S: SpanSource>(src: &mut S) -> (r: (LargeMap, bool))
    requires
        old(src)@.wf(),
    ensures
        final(src)@.wf(),
        r.0.wf(final(src)@),
        r.0.objects() == Map::<int, nat>::empty(),
        if r.1 {
            final(src)@ == old(src)@
        } else {
            large_refused(old(src)@, final(src)@, pages_for(BLOCK_BYTES as nat + 1))
        },
{
    let ghost start = src@;
    let mut map = LargeMap::new();
    let (p, perm) = match map.alloc_large(src, BLOCK_BYTES + 1) {
        None => return (map, false),
        Some(r) => r,
    };
    let addr = p.addr();
    let ghost n = pages_for(BLOCK_BYTES as nat + 1);
    let tracked run = perm.get();
    let ghost first = Set::range(addr as int, addr as int + 1);
    let tracked (one, rest) = run.split(first);
    assert(size_of::<u8>() == 1 && align_of::<u8>() == 1) by {
        broadcast use layout_of_primitives, align_of_u8;
    }
    assert(one.is_range(addr as int, size_of::<u8>() as int));
    let tracked mut byte = one.into_typed::<u8>(addr);
    ptr_mut_write(p, Tracked(&mut byte), 7u8);
    let v = ptr_mut_read(p, Tracked(&mut byte));
    assert(v == 7u8);
    let tracked raw = byte.into_raw();
    let tracked whole = raw.join(rest);
    assert(whole.dom() =~= Set::range(addr as int, addr as int + n * PAGE_BYTES));
    assert(map.objects().contains_key(addr as int));
    map.free_large(src, addr, Tracked(whole));
    assert(src@.spans =~= start.spans);
    assert(map.objects() =~= Map::<int, nat>::empty());
    (map, true)
}

} // verus!
