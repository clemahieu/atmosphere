// SPDX-License-Identifier: MIT

//! The witnesses: verified sequences of operations, built into no image, that reach the uses the
//! span source and the block buddy exist for.
//!
//! The span source's witness, from any well-formed source, reserves a span of one block, backs
//! its first page, writes a byte through the permission back returned and reads it again, releases
//! the page and the span, and ends with the view it started with, the reserve and the back granted.
//! A source that refuses leaves the view as it was with the refused request recorded, the reserve of
//! one block while it held what it held at the start, or the back of the span's first page while it
//! held that and the span, the reserve then granted, and the sequence stops there.
//!
//! Each witness that gives back what it took ends with the spans, refusals and provenance it started
//! with and exactly the grants its sequence made: for a page buddy's new run span the reserve of
//! SPAN_BLOCKS blocks and the back of its metadata page (`span_grants`), for a large object the
//! reserve of its span and the back of its pages and record page (`large_grants`).
//!
//! The page buddy's witness, over any well-formed source and with no spares, cuts a run of order 0
//! and one of order BLOCK_ORDER, frees both, and ends holding no span, with the source's view the one
//! it started with and the requests for the two runs' spans granted. A refusal stops the sequence after freeing what it cut, and the page buddy refuses
//! only when the source refused a request for a new run span, the reserve of SPAN_BLOCKS blocks or the
//! back of its metadata page, asked while it held what it held at the start, with the first run's span
//! when the second run was refused; so a source that refused neither gave both runs. Its second
//! witness, with one spare, cuts a run, frees it so its span stays as the spare, and cuts again, which
//! is shown to succeed whatever the source does; only a refused request for the first span stops it.
//! Its third, with no spares, cuts MANY whole blocks, each in a span of its own and all held at once,
//! more spans than one page of block buddy records would hold, until the source refuses such a
//! request, asked while it held what it held at the start and run spans; frees them all and ends with
//! the source's view the one it started with and the requests for those spans granted, in the order
//! they were cut, so a source that refused none gave all MANY.
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
//! The fourth takes the last page of the address space, which a page buddy may cut at the end of a
//! span there, and allocates every slot, the last of which ends at the top.
//!
//! The size classes' witness names the class of one byte and of a page: the first class, of
//! SLOT_MIN, and the last, of the page, each with a slab order whose run holds at least one slot.
//!
//! The large-object map's witness, over any well-formed source, allocates an object of one byte
//! more than a block, writes a byte of it and reads it again, frees it, and ends with the map empty
//! and the source's view the one it started with, the object's two requests granted. A refusal stops the sequence, and the map refuses
//! only when the source refused the reserve of the object's span or the back of its run, asked while
//! it held what it held at the start and, for the back, the new span; so a source that refused
//! neither gave the byte.
//!
//! The record store's witness, over any well-formed source and with no spares, takes a record,
//! which cuts a run of order 0 and backs it as a record page, puts the record back, which releases
//! the page and frees the run, and ends with no record page, the page buddy holding no span and the
//! source's view the one it started with, the requests for the page's span and its back granted. The
//! store refuses only when the source refused the run's
//! span or the back of the record page.
//!
//! The two classes' witness keeps two size classes over one record store, page buddy and source,
//! with no spares: it allocates a slot of the first class, then of the last, then of the first
//! again, which each makes a slab or takes a slot of one. Each class keeps its invariant across the
//! other's alloc_small, which keeps what a class stands on (`kept`), by its frame lemma; a refusal
//! stops the sequence, with both classes still well formed. The classes' heads stay disjoint, since
//! a class's new slab run is one the page buddy held as no run before, while each head of the other
//! class is a run it holds; so every live slot of one class is apart from every live slot of the
//! other (`lemma_classes_apart`).
//!
//! The partial free's witness keeps the first two classes, of one slab order, the same way: it
//! allocates a slot of the first, one of the second, and a second slot of the first, which the
//! first's one slab still has free since two slots fit its run; frees that slot, which leaves the
//! slab a live slot, so the heads, the store, the page buddy and the source are as they were and the
//! second class stays well formed; and allocates of the first class again. The classes' heads stay
//! disjoint throughout, so every live slot of one is apart from every live slot of the other. The
//! emptying free's witness allocates one slot of the first class and frees it, which empties its
//! slab, and ends with no live slot and no head, the slab's base gone from the heads.
//!
//! The refusal witness takes a size class over a page buddy that has a free block of the class's
//! slab order and a record store with a free record, and allocates a slot: a refusal then is the
//! source's refusal of the back of the slab's run, never the reserve of a run span or the back of a
//! page, since alloc_small asks for a span only when no held span has a free block of the order it
//! needs, and for a record page only when the store is full. Its second takes a full record store
//! and a page buddy that still has a free page once the slab's run is cut: a refusal then is of the
//! back of the slab's run or of the page cut for the record page, asked while the source held the
//! spans it held at the start, never a run span's reserve nor its metadata page's back. The full
//! store's witness shows the same of a record taken alone over a page buddy with a free page.
//!
//! The slab classes' witness keeps the smallest class and the largest over one record store and
//! page buddy holding nothing, with no spares: it allocates a slot of each, writes a byte of each
//! and reads it again, frees both, and ends with no slab in either class, no record taken nor any
//! record page, the page buddy holding no span and the source's view the one it started with, the
//! requests the sequence made granted. Each new slab, its run cut and backed and its record page
//! when the store was full, and each retired one, its run released and freed and its record page
//! given back when no other record lies on it, is followed through the page buddy's cuts and frees
//! (`tracks`): every span the source holds past its start is one the page buddy holds, and every
//! run cut is freed again (`heads_of`), so the page buddy, keeping no spare, gives every span back.
//! A refusal stops the sequence after freeing what it took, and is the source's refusal of a
//! request one of the two allocations made (`slab_refused`).
//!
//! The heap's witness gives one source to a page buddy and a large-object map: it cuts a run, then
//! allocates an object, frees the run, then the object, and ends with both holding nothing and the
//! source's view the one it started with, the requests for the run's span and the object's granted.
//! Each keeps its invariant across the other's changes to the
//! source by its frame lemma; a refusal, which the source then made once, stops the sequence after
//! freeing what it cut.
use vstd::prelude::*;
use vstd::layout::*;
use vstd::raw_ptr::*;

use crate::arch::*;
use crate::buddy::*;
use crate::class::*;
use crate::large::*;
use crate::page::*;
use crate::record::{RecordStore, back_refused, gave_back, page_back_refusal, record_page, took_page};
use crate::slab::*;
use crate::small::*;
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
/// byte was written, with the span's address: false when the source refused to reserve the span or
/// to back its page, which it did once, having granted the reserve when it refused the back; the
/// source granted the reserve and the back otherwise.
pub fn witness_one_page<S: SpanSource>(src: &mut S) -> (r: (bool, Ghost<int>))
    requires
        old(src)@.wf(),
    ensures
        if r.0 {
            final(src)@ == old(src)@.granted(
                seq![Request::Reserve { blocks: 1 }, Request::Back { span: r.1@, start: r.1@, pages: 1 }],
            )
        } else {
            let f = final(src)@.refusals.last();
            &&& final(src)@ == old(src)@.granted(granted_before(f, 1)).recorded(f)
            &&& page_refusal(old(src)@, f)
        },
{
    let ghost start = src@;
    let base = match src.reserve(1) {
        None => {
            proof {
                lemma_granted_none(start);
            }
            return (false, Ghost(0));
        },
        Some(base) => base,
    };
    let addr = base.addr();
    let ghost reserved = src@;
    assert(!start.spans.contains_key(addr as int));
    let perm = match src.back(Ghost(addr as int), addr, 1) {
        None => {
            src.release_span(addr);
            assert(src@.spans =~= start.spans);
            let ghost f = Refusal {
                request: Request::Back { span: addr as int, start: addr as int, pages: 1 },
                spans: start.reserved(addr as int, 1).spans,
            };
            assert(src@.grants =~= start.grants + granted_before(f, 1));
            assert(src@ == start.granted(granted_before(f, 1)).recorded(f));
            return (false, Ghost(addr as int));
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
    assert(src@.grants =~= start.grants + seq![
        Request::Reserve { blocks: 1 },
        Request::Back { span: addr as int, start: addr as int, pages: 1 },
    ]);
    (true, Ghost(addr as int))
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

/// The requests the source grants for the new run spans at `bs`, in order.
pub open spec fn spans_grants(bs: Seq<int>) -> Seq<Request>
    decreases bs.len(),
{
    if bs.len() == 0 {
        Seq::empty()
    } else {
        spans_grants(bs.drop_last()) + span_grants(bs.last())
    }
}

/// Taking a run span and giving it back leaves the view as it was, with the span's two requests
/// granted.
proof fn lemma_took_released(s: SourceView, b: int)
    requires
        !s.spans.contains_key(b),
    ensures
        taken(s, b).released_span(b) == s.granted(span_grants(b)),
{
    assert(taken(s, b).released_span(b).spans =~= s.spans);
    assert(taken(s, b).grants =~= s.grants + span_grants(b));
}

/// Taking a run span, having the requests `g` granted and giving the span back leaves the view as it
/// was, with the span's two requests and `g` granted.
proof fn lemma_granted_released(s: SourceView, b: int, g: Seq<Request>)
    requires
        !s.spans.contains_key(b),
    ensures
        taken(s, b).granted(g).released_span(b) == s.granted(span_grants(b) + g),
{
    assert(taken(s, b).granted(g).released_span(b).spans =~= s.spans);
    assert(taken(s, b).granted(g).grants =~= s.grants + (span_grants(b) + g));
}

/// Taking a run span, having the requests `g` granted and a request refused, and giving the span
/// back leaves the view as it was, with the span's two requests and `g` granted and that refusal
/// recorded.
proof fn lemma_refused_released(s: SourceView, b: int, g: Seq<Request>, r: Refusal)
    requires
        !s.spans.contains_key(b),
    ensures
        taken(s, b).granted(g).recorded(r).released_span(b) == s.granted(span_grants(b) + g).recorded(r),
{
    assert(taken(s, b).granted(g).recorded(r).released_span(b).spans =~= s.spans);
    assert(taken(s, b).granted(g).grants =~= s.grants + (span_grants(b) + g));
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
/// whether both runs were cut and the small run's and the whole block's addresses: both were cut, the
/// source granting the requests for their two spans and no other, unless the source refused a request
/// for a new run span, which it then did once, holding what it held at the start, and the small run's
/// span when that was cut, having granted the requests for that span.
pub fn witness_page_buddy<S: SpanSource>(src: &mut S) -> (r: (PageBuddy, bool, Ghost<int>, Ghost<int>))
    requires
        old(src)@.wf(),
    ensures
        r.0.wf(final(src)@),
        r.0.spans().dom() == Set::<int>::empty(),
        if r.1 {
            final(src)@ == old(src)@.granted(span_grants(span_of(r.2@)) + span_grants(span_of(r.3@)))
        } else {
            let f = final(src)@.refusals.last();
            let b = span_of(r.2@);
            span_refused(old(src)@, final(src)@) || {
                &&& !old(src)@.spans.contains_key(b)
                &&& final(src)@ == old(src)@.granted(span_grants(b) + granted_before(f, SPAN_BLOCKS as nat)).recorded(f)
                &&& span_refusal(taken(old(src)@, b), f)
            }
        },
{
    let mut pb = PageBuddy::new(0);
    let ghost s0 = src@;
    assert(pb.spans().dom() =~= Set::<int>::empty());
    let small = match pb.alloc_run(src, 0) {
        Err(_) => {
            return (pb, false, Ghost(0), Ghost(0));
        },
        Ok(p) => p,
    };
    let ghost b1 = span_of(small as int);
    let ghost m1 = meta_page(b1);
    let ghost h1 = page_of(small as int);
    let ghost fr1 = fresh(Map::<int, Map<int, nat>>::empty(), b1);
    let ghost u1 = pb.used();
    let ghost s1 = src@;
    let ghost spans1 = pb.spans();
    proof {
        lemma_uncut(fr1, u1, small as int, 0);
        lemma_took_released(s0, b1);
        assert(u1[b1].contains_key(h1));
        assert(u1[m1] == Map::<int, nat>::empty());
        assert(spans1.dom() =~= set![b1, m1]);
        pb.lemma_view(src@);
        lemma_pages_pos(0);
    }
    let whole = match pb.alloc_run(src, BLOCK_ORDER) {
        Err(_) => {
            assert(pb.used() == u1);
            let ghost q = src@.refusals.last();
            pb.free_run(src, small);
            proof {
                assert(fr1[b1].dom() =~= Set::<int>::empty());
                assert(pb.used().dom() =~= Set::<int>::empty());
                pb.lemma_view(src@);
                lemma_refused_released(s0, b1, granted_before(q, SPAN_BLOCKS as nat), q);
            }
            return (pb, false, Ghost(small as int), Ghost(0));
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
    let ghost s2 = src@;
    proof {
        assert(!spans1.contains_key(b2));
        assert(b2 != b1 && b2 != m1);
        lemma_uncut(fresh(u1, b2), u2, whole as int, BLOCK_ORDER as nat);
        lemma_took_released(s1, b2);
        assert(u2[b1] == u1[b1]);
        assert(u2[b2].remove(h2) =~= Map::<int, nat>::empty());
        assert(u2[m2] == Map::<int, nat>::empty());
        pb.lemma_view(src@);
    }
    pb.free_run(src, whole);
    proof {
        assert(pb.used() =~= u1);
        assert(src@ == s1.granted(span_grants(b2)));
        assert(pb.span_base(span_of(small as int)) == b1);
        lemma_granted_released(s0, b1, span_grants(b2));
    }
    pb.free_run(src, small);
    proof {
        assert(fr1[b1].dom() =~= Set::<int>::empty());
        assert(pb.used().dom() =~= Set::<int>::empty());
        pb.lemma_view(src@);
    }
    (pb, true, Ghost(small as int), Ghost(whole as int))
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
/// it cut and the base of each one's span: MANY unless the source refused a request for a new run
/// span, and otherwise fewer, the source having refused once, holding then what it held at the start
/// and run spans, which the view returned holds. The source granted the requests for those spans, in
/// the order they were cut, and, when it refused, what it granted before the refusal.
pub fn witness_page_buddy_many<S: SpanSource>(src: &mut S) -> (r: (PageBuddy, usize, Ghost<SourceView>, Ghost<Seq<int>>))
    requires
        old(src)@.wf(),
    ensures
        r.0.wf(final(src)@),
        r.0.spans().dom() == Set::<int>::empty(),
        r.1 <= MANY,
        r.3@.len() == r.1,
        if r.1 == MANY {
            final(src)@ == old(src)@.granted(spans_grants(r.3@))
        } else {
            let f = final(src)@.refusals.last();
            &&& final(src)@ == old(src)@.granted(spans_grants(r.3@) + granted_before(f, SPAN_BLOCKS as nat)).recorded(f)
            &&& span_refusal(r.2@, f)
            &&& holds_runs(old(src)@, r.2@)
        },
{
    let ghost start = src@;
    let ghost mut held = start;
    let ghost mut bases = Seq::<int>::empty();
    let mut pb = PageBuddy::new(0);
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
            pb.wf(src@),
            pb.spares() == 0,
            n <= MANY,
            go || n < MANY,
            pages(BLOCK_ORDER as nat) == BLOCK_PAGES as int,
            whole == Map::<int, nat>::empty().insert(0, BLOCK_ORDER as nat),
            whole.remove(0) == Map::<int, nat>::empty(),
            added(start, src@, pb.used(), pb.metas(), !go, held),
            bases.len() == n,
            src@.grants == start.grants + spans_grants(bases) + if go {
                Seq::<Request>::empty()
            } else {
                granted_before(src@.refusals.last(), SPAN_BLOCKS as nat)
            },
            forall|j: int|
                0 <= j < n ==> {
                    &&& (#[trigger] runs@[j]) as int % BLOCK_BYTES as int == 0
                    &&& pb.used().contains_key(runs@[j] as int)
                    &&& pb.used()[runs@[j] as int] == whole
                    &&& !pb.metas().contains(runs@[j] as int)
                    &&& src@.unbacked(runs@[j] as int, runs@[j] as int, BLOCK_PAGES as nat)
                },
            forall|i: int, j: int| 0 <= i < j < n ==> runs@[i] != runs@[j],
            forall|b: int|
                #[trigger] pb.used().contains_key(b) ==> pb.metas().contains(b) || exists|j: int|
                    0 <= j < n && runs@[j] as int == b,
            forall|m: int| #[trigger] pb.metas().contains(m) ==> pb.used()[m] == Map::<int, nat>::empty(),
        decreases MANY - n + if go { 1int } else { 0int },
    {
        let ghost u0 = pb.used();
        let ghost s0 = src@;
        let ghost metas0 = pb.metas();
        let ghost spans0 = pb.spans();
        proof {
            pb.lemma_view(src@);
        }
        match pb.alloc_run(src, BLOCK_ORDER) {
            Err(e) => {
                assert(e is Source);
                proof {
                    held = s0;
                    assert(s0.grants =~= start.grants + spans_grants(bases));
                    assert(src@.grants =~= start.grants + spans_grants(bases) + granted_before(
                        src@.refusals.last(),
                        SPAN_BLOCKS as nat,
                    ));
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
                    let s = src@;
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
                    assert forall|j: int| #![trigger runs@[j]] 0 <= j < n implies src@.unbacked(
                        runs@[j] as int,
                        runs@[j] as int,
                        BLOCK_PAGES as nat,
                    ) by {
                        let c2 = runs@[j] as int;
                        assert(u0.contains_key(c2));
                        assert(s0.spans.contains_key(c2));
                        assert(src@.spans[c2] == s0.spans[c2]);
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
                    assert(bases.push(b).drop_last() =~= bases);
                    assert(s.grants =~= start.grants + spans_grants(bases.push(b)) + Seq::<Request>::empty());
                    bases = bases.push(b);
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
    let ghost cut_grants = src@.grants;
    let ghost cut_refusals = src@.refusals;
    while n > 0
        invariant
            pb.wf(src@),
            pb.spares() == 0,
            src@.grants == cut_grants,
            src@.refusals == cut_refusals,
            n <= cut <= MANY,
            go == (cut == MANY),
            pages(BLOCK_ORDER as nat) == BLOCK_PAGES as int,
            whole == Map::<int, nat>::empty().insert(0, BLOCK_ORDER as nat),
            whole.remove(0) == Map::<int, nat>::empty(),
            added(start, src@, pb.used(), pb.metas(), !go, held),
            forall|j: int|
                0 <= j < n ==> {
                    &&& (#[trigger] runs@[j]) as int % BLOCK_BYTES as int == 0
                    &&& pb.used().contains_key(runs@[j] as int)
                    &&& pb.used()[runs@[j] as int] == whole
                    &&& !pb.metas().contains(runs@[j] as int)
                    &&& src@.unbacked(runs@[j] as int, runs@[j] as int, BLOCK_PAGES as nat)
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
        let ghost s0 = src@;
        let ghost metas0 = pb.metas();
        let ghost mp = meta_page(p as int);
        proof {
            pb.lemma_view(src@);
            assert(runs@[n as int] == p);
            lemma_block_head(p as int);
            assert(u0[p as int] == whole);
            assert(metas0.contains(mp));
            assert(u0[mp] == Map::<int, nat>::empty());
            assert(u0.insert(p as int, u0[p as int].remove(0))[p as int].dom() =~= Set::<int>::empty());
            assert(u0.insert(p as int, u0[p as int].remove(0))[mp].dom() =~= Set::<int>::empty());
        }
        pb.free_run(src, p);
        proof {
            let s = src@;
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
            assert forall|j: int| #![trigger runs@[j]] 0 <= j < n implies src@.unbacked(
                runs@[j] as int,
                runs@[j] as int,
                BLOCK_PAGES as nat,
            ) by {
                let c = runs@[j] as int;
                assert(u0.contains_key(c));
                assert(s0.spans.contains_key(c));
                assert(c != p as int);
                assert(src@.spans[c] == s0.spans[c]);
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
        pb.lemma_view(src@);
        // A held metadata page has its span's first block held too, and that is no metadata page,
        // so it would be a run left in the list.
        assert forall|b: int| !pb.used().contains_key(b) by {
            if pb.used().contains_key(b) && pb.metas().contains(b) {
                assert(pb.used().contains_key(b - BLOCK_BYTES as int));
            }
        }
        assert(pb.used().dom() =~= Set::<int>::empty());
        let s = src@;
        assert(s.spans.dom() =~= start.spans.dom());
        assert(s.spans =~= start.spans);
        if go {
            assert(s.grants =~= start.grants + spans_grants(bases));
        } else {
            assert(s.grants =~= start.grants + (spans_grants(bases) + granted_before(
                s.refusals.last(),
                SPAN_BLOCKS as nat,
            )));
        }
    }
    (pb, cut, Ghost(held), Ghost(bases))
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
pub fn witness_page_buddy_spare<S: SpanSource>(src: &mut S) -> (r: (PageBuddy, bool))
    requires
        old(src)@.wf(),
    ensures
        r.0.wf(final(src)@),
        r.0.spares() == 1,
        forall|b: int| #[trigger] r.0.used().contains_key(b) ==> r.0.used()[b].dom() == Set::<int>::empty(),
        if r.1 {
            final(src)@.refusals == old(src)@.refusals
        } else {
            span_refused(old(src)@, final(src)@)
        },
{
    let mut pb = PageBuddy::new(1);
    let first = match pb.alloc_run(src, 0) {
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
    pb.free_run(src, first);
    proof {
        assert(pb.used() == fr);
        pb.lemma_view(src@);
        pb.lemma_idle_fits(src@, b1, 0);
    }
    let again = pb.alloc_run(src, 0);
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
    pb.free_run(src, second);
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
/// holding that and the run's span, which it then did once. The source granted the requests for the
/// run's span, and the back of the run's page when it wrote the byte.
pub fn witness_backed_run<S: SpanSource>(src: &mut S) -> (r: (PageBuddy, bool, Ghost<int>))
    requires
        old(src)@.wf(),
    ensures
        r.0.wf(final(src)@),
        r.0.spans().dom() == Set::<int>::empty(),
        if r.1 {
            let b = span_of(r.2@);
            final(src)@ == old(src)@.granted(span_grants(b) + seq![Request::Back { span: b, start: r.2@, pages: 1 }])
        } else {
            span_refused(old(src)@, final(src)@) || {
                let b = span_of(r.2@);
                &&& !old(src)@.spans.contains_key(b)
                &&& final(src)@ == old(src)@.granted(span_grants(b)).recorded(
                    Refusal { request: Request::Back { span: b, start: r.2@, pages: 1 }, spans: taken(old(src)@, b).spans },
                )
            }
        },
{
    let mut pb = PageBuddy::new(0);
    let ghost s0 = src@;
    assert(pb.spans().dom() =~= Set::<int>::empty());
    let p = match pb.alloc_run(src, 0) {
        Err(_) => {
            return (pb, false, Ghost(0));
        },
        Ok(p) => p,
    };
    let ghost b = span_of(p as int);
    let ghost m = meta_page(b);
    let ghost fr = fresh(Map::<int, Map<int, nat>>::empty(), b);
    let ghost s1 = src@;
    proof {
        lemma_uncut(fr, pb.used(), p as int, 0);
        lemma_took_released(s0, b);
        assert(fr[b].dom() =~= Set::<int>::empty());
        assert(fr[m].dom() =~= Set::<int>::empty());
        assert(pages(0) == 1);
    }
    let (ptr, perm) = match pb.back_run(src, p, 0, 1) {
        None => {
            let ghost q = src@.refusals.last();
            pb.free_run(src, p);
            proof {
                assert(pb.used().dom() =~= Set::<int>::empty());
                pb.lemma_view(src@);
                lemma_granted_none(taken(s0, b));
                lemma_refused_released(s0, b, Seq::empty(), q);
                assert(span_grants(b) + Seq::<Request>::empty() =~= span_grants(b));
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
    pb.release_run(src, p, 0, 1, Tracked(whole));
    proof {
        assert(s1.spans[b].backed.disjoint(run_pages(p as int, 1)));
        assert(src@.spans[b].backed =~= s1.spans[b].backed);
        assert(src@.spans =~= s1.spans);
        assert(src@.grants =~= s1.grants + seq![Request::Back { span: b, start: p as int, pages: 1 }]);
        assert(src@ == s1.granted(seq![Request::Back { span: b, start: p as int, pages: 1 }]));
        lemma_granted_released(s0, b, seq![Request::Back { span: b, start: p as int, pages: 1 }]);
    }
    pb.free_run(src, p);
    proof {
        assert(pb.used().dom() =~= Set::<int>::empty());
        pb.lemma_view(src@);
    }
    (pb, true, Ghost(p as int))
}

/// The record store's witness: with no spares, takes a record, which cuts and backs a record page,
/// and puts it back, which gives the page back; ends with no record page, the page buddy holding no
/// span and the source's view the one it started with, with the requests for the record page's span
/// and the back of the page granted; returns the page's address. A refusal stops the sequence, and the
/// store refuses only when the source refused the run's span or the back of the record page.
pub fn witness_record<S: SpanSource>(src: &mut S) -> (r: (PageBuddy, RecordStore, bool, Ghost<int>))
    requires
        old(src)@.wf(),
    ensures
        r.0.wf(final(src)@),
        r.1.wf(r.0, final(src)@),
        if r.2 {
            let c = span_of(r.3@);
            &&& final(src)@ == old(src)@.granted(span_grants(c) + seq![Request::Back { span: c, start: r.3@, pages: 1 }])
            &&& r.0.spans().dom() == Set::<int>::empty()
            &&& r.1.pages() == Set::<int>::empty()
            &&& r.1.taken() == Set::<int>::empty()
        } else {
            span_refused(old(src)@, final(src)@) || exists|pb: PageBuddy| #[trigger] back_refused(pb, old(src)@, final(src)@)
        },
{
    let mut pb = PageBuddy::new(0);
    let mut store = RecordStore::new();
    let ghost s0 = src@;
    let ghost pb0 = pb;
    assert(pb.spans().dom() =~= Set::<int>::empty());
    let (p, perm) = match store.take(&mut pb, src) {
        None => {
            proof {
                if !span_refused(s0, src@) {
                    assert(back_refused(pb0, s0, src@));
                }
            }
            return (pb, store, false, Ghost(0));
        },
        Some(taken) => taken,
    };
    let ghost q = record_page(p@.addr as int);
    let ghost c = span_of(q);
    let ghost pb1 = pb;
    let ghost s1 = src@;
    let ghost fr = fresh(Map::<int, Map<int, nat>>::empty(), c);
    proof {
        assert(!pb0.spans().contains_key(c));
        lemma_uncut(fr, pb1.used(), q, 0);
        assert(fr[c].dom() =~= Set::<int>::empty());
        assert(fr[meta_page(c)].dom() =~= Set::<int>::empty());
        assert(store.taken() =~= Set::<int>::empty().insert(p@.addr as int));
    }
    store.put(&mut pb, src, p, perm);
    proof {
        assert(!(exists|x: int|
            #[trigger] Set::<int>::empty().insert(p@.addr as int).contains(x) && x != p@.addr as int
                && record_page(x) == q));
        assert(src@.spans =~= s0.spans);
        assert(src@.grants =~= s0.grants + (span_grants(c) + seq![Request::Back { span: c, start: q, pages: 1 }]));
        assert(pb.used().dom() =~= Set::<int>::empty());
        assert(store.pages() =~= Set::<int>::empty());
        assert(store.taken() =~= Set::<int>::empty());
        pb.lemma_view(src@);
    }
    (pb, store, true, Ghost(q))
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

/// Makes a slab of SLOT_MIN slots over the backed page at `page`, the last page of the address
/// space, as the page buddy may cut a run at the end of a span there, and allocates every slot, none
/// refused: returns the slab, whose last slot, live, ends at the top.
pub fn witness_slab_top(page: *mut u8, run: Tracked<PointsToRaw>) -> (s: Slab)
    requires
        page@.addr % PAGE_BYTES == 0,
        page@.addr + PAGE_BYTES == usize::MAX + 1,
        run@.is_range(page@.addr as int, PAGE_BYTES as int),
        run@.provenance() == page@.provenance,
    ensures
        s.wf(),
        s.holds(usize::MAX + 1 - SLOT_MIN),
{
    let tracked mut perms = Map::<int, PointsToRaw>::tracked_empty();
    proof {
        lemma_page_slots(page);
    }
    let mut s = Slab::new(page, PAGE_BYTES, SLOT_MIN, run, Tracked(&mut perms));
    let n = PAGE_BYTES / SLOT_MIN;
    proof {
        assert(s.free_slots().len() == n);
    }
    let mut k: usize = 0;
    while k < n
        invariant
            s.wf(),
            s.owns(perms),
            s.base() == page,
            s.bytes() == PAGE_BYTES,
            s.slot() == SLOT_MIN,
            s.count() == n,
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
    proof {
        vstd::set_lib::lemma_set_empty_equivalency_len(s.free_slots());
        let a = usize::MAX + 1 - SLOT_MIN;
        assert(s.index(a) == n - 1);
        assert(s.addr(n - 1) == a);
        assert(s.live().contains(n - 1));
    }
    s
}

} // verus!

verus! {

/// Allocates an object of one byte more than a block from a new large-object map over `src`, writes
/// and reads its first byte, and frees it. Returns the map, empty again, with whether the byte was
/// written and the object's address: false when the source refused the reserve of the object's span
/// or the back of its run, which it did once; the source granted the reserve and the back otherwise.
pub fn witness_large<S: SpanSource>(src: &mut S) -> (r: (LargeMap, bool, Ghost<int>))
    requires
        old(src)@.wf(),
    ensures
        final(src)@.wf(),
        r.0.wf(final(src)@),
        r.0.objects() == Map::<int, nat>::empty(),
        if r.1 {
            final(src)@ == old(src)@.granted(large_grants(r.2@, pages_for(BLOCK_BYTES as nat + 1)))
        } else {
            large_refused(old(src)@, final(src)@, pages_for(BLOCK_BYTES as nat + 1))
        },
{
    let ghost start = src@;
    let mut map = LargeMap::new();
    let (p, perm) = match map.alloc_large(src, BLOCK_BYTES + 1) {
        None => return (map, false, Ghost(0)),
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
    assert(src@.grants =~= start.grants + large_grants(addr as int, n));
    assert(map.objects() =~= Map::<int, nat>::empty());
    (map, true, Ghost(addr as int))
}

/// The class of one byte and of a page: the first class and the last, with the order of each one's
/// slabs' runs, each run holding at least one slot of its class.
pub fn witness_classes() -> (r: (usize, usize, usize, usize))
    ensures
        r.0 == 0,
        class_size(r.0 as nat) == SLOT_MIN,
        r.1 == CLASSES - 1,
        class_size(r.1 as nat) == PAGE_BYTES,
        r.2 as nat == slab_order(r.0 as nat),
        r.3 as nat == slab_order(r.1 as nat),
        SLOT_MIN <= run_bytes(r.2 as nat),
        PAGE_BYTES <= run_bytes(r.3 as nat),
{
    let small = class_of(1);
    let large = class_of(PAGE_BYTES);
    proof {
        lemma_class(0);
        lemma_class(large as nat);
        if large + 1 < CLASSES {
            lemma_class((large + 1) as nat);
        }
    }
    (small, large, order(small), order(large))
}

/// Over one source, cuts a run of order 0 from a page buddy keeping no spare, allocates an object of
/// one byte more than a block from a large-object map, frees the run and then the object, and returns
/// the page buddy and the map, holding nothing, with whether both were given and the run's and the
/// object's addresses: both were unless the source refused a request, which it then did once, the
/// view otherwise the one it started with; the source granted the requests for the run's span and
/// the object's, and when it refused the object, those for the run's span and what it granted the
/// object before the refusal.
pub fn witness_heap<S: SpanSource>(src: &mut S) -> (r: (PageBuddy, LargeMap, bool, Ghost<int>, Ghost<int>))
    requires
        old(src)@.wf(),
    ensures
        final(src)@.wf(),
        r.0.wf(final(src)@),
        r.1.wf(final(src)@),
        r.0.spans().dom() == Set::<int>::empty(),
        r.1.objects() == Map::<int, nat>::empty(),
        if r.2 {
            final(src)@ == old(src)@.granted(
                span_grants(span_of(r.3@)) + large_grants(r.4@, pages_for(BLOCK_BYTES as nat + 1)),
            )
        } else {
            let f = final(src)@.refusals.last();
            span_refused(old(src)@, final(src)@) || final(src)@ == old(src)@.granted(
                span_grants(span_of(r.3@)) + granted_before(f, blocks_for(pages_for(BLOCK_BYTES as nat + 1))),
            ).recorded(f)
        },
{
    let ghost s0 = src@;
    let mut pb = PageBuddy::new(0);
    let mut map = LargeMap::new();
    assert(pb.spans().dom() =~= Set::<int>::empty());
    let small = match pb.alloc_run(src, 0) {
        Err(_) => {
            proof {
                pb.lemma_view(src@);
            }
            return (pb, map, false, Ghost(0), Ghost(0));
        },
        Ok(p) => p,
    };
    let ghost b1 = span_of(small as int);
    let ghost m1 = meta_page(b1);
    let ghost fr1 = fresh(Map::<int, Map<int, nat>>::empty(), b1);
    let ghost u1 = pb.used();
    let ghost s1 = src@;
    proof {
        lemma_uncut(fr1, u1, small as int, 0);
        lemma_took_released(s0, b1);
        assert(u1[m1] == Map::<int, nat>::empty());
        assert(pb.spans().dom() =~= set![b1, m1]);
        assert(pb.span_base(span_of(small as int)) == b1);
        pb.lemma_view(s1);
        assert(s1.spans.contains_key(b1));
    }
    let (p, perm) = match map.alloc_large(src, BLOCK_BYTES + 1) {
        None => {
            let ghost q = src@.refusals.last();
            proof {
                pb.lemma_frame(s1, src@);
            }
            pb.free_run(src, small);
            proof {
                assert(fr1[b1].dom() =~= Set::<int>::empty());
                assert(pb.used().dom() =~= Set::<int>::empty());
                pb.lemma_view(src@);
                let ghost g = granted_before(q, blocks_for(pages_for(BLOCK_BYTES as nat + 1)));
                lemma_refused_released(s0, b1, g, q);
                map.lemma_frame(s1.granted(g).recorded(q), src@);
            }
            return (pb, map, false, Ghost(small as int), Ghost(0));
        },
        Some(r) => r,
    };
    let ghost nb = p@.addr as int;
    let ghost s2 = src@;
    proof {
        assert(s1.apart(nb, blocks_for(pages_for(BLOCK_BYTES as nat + 1)), b1));
        assert(nb != b1);
        pb.lemma_frame(s1, s2);
    }
    pb.free_run(src, small);
    let ghost s3 = src@;
    proof {
        assert(fr1[b1].dom() =~= Set::<int>::empty());
        assert(pb.used().dom() =~= Set::<int>::empty());
        pb.lemma_view(s3);
        map.lemma_frame(s2, s3);
    }
    let addr = p.addr();
    assert(map.objects().contains_key(addr as int));
    map.free_large(src, addr, perm);
    proof {
        assert(src@.spans =~= s0.spans);
        assert(src@.grants =~= s0.grants + (span_grants(b1) + large_grants(nb, pages_for(BLOCK_BYTES as nat + 1))));
        pb.lemma_frame(s3, src@);
        assert(map.objects() =~= Map::<int, nat>::empty());
    }
    (pb, map, true, Ghost(small as int), Ghost(nb))
}

/// Two size classes over one record store and page buddy keeping no spare: allocates a slot of the
/// first class, then of the last, then of the first again, and returns both classes, the store, the
/// page buddy and how many slots were given. Each class is well formed at the end, the first having
/// kept its invariant across the last's alloc_small; the classes' heads are disjoint, so a live
/// slot of one is apart from every live slot of the other; a refusal stops the sequence.
pub fn witness_two_classes<S: SpanSource>(src: &mut S) -> (r: (SizeClass, SizeClass, RecordStore, PageBuddy, usize))
    requires
        old(src)@.wf(),
    ensures
        r.3.wf(final(src)@),
        r.2.wf(r.3, final(src)@),
        r.0.wf(r.2, r.3, final(src)@),
        r.1.wf(r.2, r.3, final(src)@),
        r.0.class() == 0,
        r.1.class() == CLASSES - 1,
        r.4 <= 3,
        r.0.heads().disjoint(r.1.heads()),
        forall|y: int, z: int|
            #![trigger r.0.live().contains(y), r.1.live().contains(z)]
            r.0.live().contains(y) && r.1.live().contains(z) ==> y + class_size(r.0.class()) <= z || z
                + class_size(r.1.class()) <= y,
{
    let mut pb = PageBuddy::new(0);
    let mut store = RecordStore::new();
    let mut first = SizeClass::new(0);
    let mut last = SizeClass::new(CLASSES - 1);
    let ghost st0 = store;
    let ghost pb0 = pb;
    let ghost s0 = src@;
    let ghost f0 = first;
    let ghost l0 = last;
    proof {
        assert(f0.heads().disjoint(l0.heads()));
    }
    let r1 = first.alloc_small(&mut store, &mut pb, src);
    proof {
        last.lemma_frame(st0, pb0, s0, store, pb, src@);
        lemma_heads_grew(f0, first, st0, store, pb0, pb, s0, src@, r1);
        lemma_heads_stay_apart(f0, first, l0, st0, pb0, s0);
    }
    if r1.is_none() {
        proof {
            lemma_witness_apart(first, last, store, pb, src@);
        }
        return (first, last, store, pb, 0);
    }
    let ghost st1 = store;
    let ghost pb1 = pb;
    let ghost s1 = src@;
    let ghost l1 = last;
    let r2 = last.alloc_small(&mut store, &mut pb, src);
    proof {
        first.lemma_frame(st1, pb1, s1, store, pb, src@);
        lemma_heads_grew(l1, last, st1, store, pb1, pb, s1, src@, r2);
        lemma_heads_stay_apart(l1, last, first, st1, pb1, s1);
    }
    if r2.is_none() {
        proof {
            lemma_witness_apart(first, last, store, pb, src@);
        }
        return (first, last, store, pb, 1);
    }
    let ghost st2 = store;
    let ghost pb2 = pb;
    let ghost s2 = src@;
    let ghost f2 = first;
    let r3 = first.alloc_small(&mut store, &mut pb, src);
    proof {
        last.lemma_frame(st2, pb2, s2, store, pb, src@);
        lemma_heads_grew(f2, first, st2, store, pb2, pb, s2, src@, r3);
        lemma_heads_stay_apart(f2, first, last, st2, pb2, s2);
        lemma_witness_apart(first, last, store, pb, src@);
    }
    let given = if r3.is_none() {
        2
    } else {
        3
    };
    (first, last, store, pb, given)
}

/// Two size classes of one slab order over one record store and page buddy keeping no spare:
/// allocates a slot of the first class, one of the second, and a second slot of the first, which
/// the first's one slab gives; frees that slot, which leaves the slab with a live slot; and
/// allocates of the first class again. Each step keeps both classes well formed and their heads
/// disjoint, so at the end a live slot of one is apart from every live slot of the other; a
/// refusal stops the sequence, and the last element says whether it ran to the end.
pub fn witness_free_partial<S: SpanSource>(src: &mut S) -> (r: (SizeClass, SizeClass, RecordStore, PageBuddy, bool))
    requires
        old(src)@.wf(),
    ensures
        r.3.wf(final(src)@),
        r.2.wf(r.3, final(src)@),
        r.0.wf(r.2, r.3, final(src)@),
        r.1.wf(r.2, r.3, final(src)@),
        r.0.class() == 0,
        r.1.class() == 1,
        slab_order(0) == slab_order(1),
        r.0.heads().disjoint(r.1.heads()),
        forall|y: int, z: int|
            #![trigger r.0.live().contains(y), r.1.live().contains(z)]
            r.0.live().contains(y) && r.1.live().contains(z) ==> y + class_size(r.0.class()) <= z || z
                + class_size(r.1.class()) <= y,
{
    proof {
        assert(slab_order(0) == slab_order(1) && 2 * class_size(0) <= run_bytes(slab_order(0))) by (compute_only);
    }
    let mut pb = PageBuddy::new(0);
    let mut store = RecordStore::new();
    let mut first = SizeClass::new(0);
    let mut second = SizeClass::new(1);
    let ghost st0 = store;
    let ghost pb0 = pb;
    let ghost s0 = src@;
    let ghost f0 = first;
    let ghost l0 = second;
    proof {
        assert(f0.heads().disjoint(l0.heads()));
    }
    let r1 = first.alloc_small(&mut store, &mut pb, src);
    proof {
        second.lemma_frame(st0, pb0, s0, store, pb, src@);
        lemma_heads_grew(f0, first, st0, store, pb0, pb, s0, src@, r1);
        lemma_heads_stay_apart(f0, first, l0, st0, pb0, s0);
    }
    let p1 = match r1 {
        Some((p, _)) => p,
        None => {
            proof {
                lemma_witness_apart(first, second, store, pb, src@);
            }
            return (first, second, store, pb, false);
        },
    };
    let ghost st1 = store;
    let ghost pb1 = pb;
    let ghost s1 = src@;
    let ghost f1 = first;
    let ghost l1 = second;
    let ghost a = choose|a: int| #[trigger]
        f1.slabs().contains_key(a) && {
            &&& !f0.slabs().contains_key(a)
            &&& f1.slabs() == f0.slabs().insert(a, f1.slabs()[a])
            &&& f1.slabs()[a].holds(p1@.addr as int)
        };
    proof {
        assert(!exists|b: int| #[trigger]
            f0.slabs().contains_key(b) && f0.slabs()[b].free_slots() != Set::<int>::empty());
        assert(f1.slabs().dom() =~= set![a]);
        assert forall|x: int| #[trigger] f1.slabs()[a].holds(x) implies x == p1@.addr as int by {
            assert(live_of(f1.slabs()).contains(x));
            assert(f0.live().contains(x) || x == p1@.addr as int);
        }
        f1.lemma_one_live_free(st1, pb1, s1, a, p1@.addr as int);
    }
    let r2 = second.alloc_small(&mut store, &mut pb, src);
    proof {
        first.lemma_frame(st1, pb1, s1, store, pb, src@);
        lemma_heads_grew(l1, second, st1, store, pb1, pb, s1, src@, r2);
        lemma_heads_stay_apart(l1, second, first, st1, pb1, s1);
    }
    if r2.is_none() {
        proof {
            lemma_witness_apart(first, second, store, pb, src@);
        }
        return (first, second, store, pb, false);
    }
    let ghost st2 = store;
    let ghost pb2 = pb;
    let ghost s2 = src@;
    let r3 = first.alloc_small(&mut store, &mut pb, src);
    proof {
        assert(f1.slabs().contains_key(a) && f1.slabs()[a].free_slots() != Set::<int>::empty());
        assert(store == st2 && pb == pb2 && src@ == s2);
    }
    let (p3, perm3) = match r3 {
        Some(x) => x,
        None => {
            proof {
                lemma_witness_apart(first, second, store, pb, src@);
            }
            return (first, second, store, pb, false);
        },
    };
    let ghost f3 = first;
    let ghost y = p3@.addr as int;
    proof {
        let a3 = choose|a3: int| #[trigger]
            f1.slabs().contains_key(a3) && {
                &&& f3.slabs() == f1.slabs().insert(a3, f3.slabs()[a3])
                &&& f3.slabs()[a3].base() == f1.slabs()[a3].base()
                &&& forall|x: int| #[trigger] f3.slabs()[a3].holds(x) <==> (x == y || f1.slabs()[a3].holds(x))
            };
        assert(a3 == a);
        assert(f3.slabs()[a].holds(p1@.addr as int));
        assert(f3.slabs()[a].holds(y));
        assert(f3.slabs().contains_key(a) && f3.slabs()[a].holds(y));
        let b = f3.slab_of(y);
        assert(f3.slabs().dom() =~= set![a]);
        assert(b == a);
        assert(f1.live().contains(p1@.addr as int));
        assert(!only_live(f3.slabs()[a], y));
    }
    first.free_small(&mut store, &mut pb, src, p3, perm3);
    proof {
        assert(first.heads().disjoint(second.heads()));
    }
    let ghost f4 = first;
    let r4 = first.alloc_small(&mut store, &mut pb, src);
    proof {
        second.lemma_frame(st2, pb2, s2, store, pb, src@);
        lemma_heads_grew(f4, first, st2, store, pb2, pb, s2, src@, r4);
        lemma_heads_stay_apart(f4, first, second, st2, pb2, s2);
        lemma_witness_apart(first, second, store, pb, src@);
    }
    (first, second, store, pb, r4.is_some())
}

/// One size class over a record store and page buddy keeping no spare: allocates a slot, then frees
/// it, which empties the slab it came from. The class is well formed with no live slot and no
/// head, as it started; the last element says whether the allocation was given.
pub fn witness_free_emptied<S: SpanSource>(src: &mut S) -> (r: (SizeClass, RecordStore, PageBuddy, bool))
    requires
        old(src)@.wf(),
    ensures
        r.2.wf(final(src)@),
        r.1.wf(r.2, final(src)@),
        r.0.wf(r.1, r.2, final(src)@),
        r.0.class() == 0,
        r.0.live() == ISet::<int>::empty(),
        r.0.heads() == ISet::<int>::empty(),
{
    let mut pb = PageBuddy::new(0);
    let mut store = RecordStore::new();
    let mut first = SizeClass::new(0);
    let ghost f0 = first;
    let r1 = first.alloc_small(&mut store, &mut pb, src);
    let (p, perm) = match r1 {
        Some(x) => x,
        None => {
            return (first, store, pb, false);
        },
    };
    let ghost f1 = first;
    let ghost y = p@.addr as int;
    proof {
        assert(!exists|b: int| #[trigger]
            f0.slabs().contains_key(b) && f0.slabs()[b].free_slots() != Set::<int>::empty());
        let a = choose|a: int| #[trigger]
            f1.slabs().contains_key(a) && {
                &&& !f0.slabs().contains_key(a)
                &&& f1.slabs() == f0.slabs().insert(a, f1.slabs()[a])
                &&& f1.slabs()[a].holds(y)
                &&& f1.heads() == f0.heads().insert(f1.slabs()[a].base()@.addr as int)
            };
        assert(f1.slabs().dom() =~= set![a]);
        assert(f1.slabs().contains_key(a) && f1.slabs()[a].holds(y));
        assert(f1.slab_of(y) == a);
        assert forall|x: int| #[trigger] f1.slabs()[a].holds(x) implies x == y by {
            assert(live_of(f1.slabs()).contains(x));
            assert(f0.live().contains(x) || x == y);
        }
        assert(only_live(f1.slabs()[a], y));
        assert(f1.heads() =~= ISet::<int>::empty().insert(f1.slabs()[a].base()@.addr as int));
    }
    first.free_small(&mut store, &mut pb, src, p, perm);
    proof {
        assert(first.live() =~= ISet::<int>::empty());
        assert(first.heads() =~= ISet::<int>::empty());
    }
    (first, store, pb, true)
}

/// A size class over a page buddy with a free block of its slab order and a record store with a free
/// record allocates a slot; returns whether it got one. A refusal is the source's refusal of the back
/// of the slab's run, of its pages(k) pages: no run span was asked for, and no record page.
pub fn witness_small_fits<S: SpanSource>(
    c: &mut SizeClass,
    store: &mut RecordStore,
    pb: &mut PageBuddy,
    src: &mut S,
) -> (got: bool)
    requires
        old(pb).wf(old(src)@),
        old(store).wf(*old(pb), old(src)@),
        old(c).wf(*old(store), *old(pb), old(src)@),
        old(pb).fits(slab_order(old(c).class())),
        !old(store).full(),
    ensures
        final(c).wf(*final(store), *final(pb), final(src)@),
        !got ==> match final(src)@.refusals.last().request {
            Request::Back { pages: n, .. } => n == pages(slab_order(old(c).class())) as nat,
            Request::Reserve { .. } => false,
        },
{
    let ghost st0 = *store;
    let ghost pb0 = *pb;
    let ghost s0 = src@;
    let ghost k = slab_order(c.class());
    let got = c.alloc_small(store, pb, src).is_some();
    proof {
        if !got {
            let r = src@.refusals.last();
            assert(slab_refused(st0, pb0, s0, src@, k));
            assert(pb0.fits(k));
            let (mid, s, q) = choose|mid: PageBuddy, s: SourceView, q: int| #[trigger]
                cut_run(pb0, mid, s0, s, q, k) && run_refused(st0, mid, s, r, q, k);
            assert(run_refused(st0, mid, s, r, q, k));
        }
    }
    got
}

/// A size class over a full record store and a page buddy with a free block of its slab order, and
/// a free page still once the slab's run is cut from it, allocates a slot; returns whether it got
/// one. A refusal is of the back of the slab's run or of the page cut for a record page, asked while
/// the source held the spans it held at the start: no run span was asked for, neither its reserve nor
/// the back of its metadata page.
pub fn witness_small_full<S: SpanSource>(
    c: &mut SizeClass,
    store: &mut RecordStore,
    pb: &mut PageBuddy,
    src: &mut S,
) -> (got: bool)
    requires
        old(pb).wf(old(src)@),
        old(store).wf(*old(pb), old(src)@),
        old(c).wf(*old(store), *old(pb), old(src)@),
        old(pb).fits(slab_order(old(c).class())),
        forall|mid: PageBuddy, s: SourceView, q: int| #[trigger]
            cut_run(*old(pb), mid, old(src)@, s, q, slab_order(old(c).class())) ==> mid.fits(0),
        old(store).full(),
    ensures
        final(c).wf(*final(store), *final(pb), final(src)@),
        !got ==> {
            let r = final(src)@.refusals.last();
            &&& r.request is Back
            &&& r.spans.dom() == old(src)@.spans.dom()
        },
{
    let ghost st0 = *store;
    let ghost pb0 = *pb;
    let ghost s0 = src@;
    let ghost k = slab_order(c.class());
    let got = c.alloc_small(store, pb, src).is_some();
    proof {
        if !got {
            let r = src@.refusals.last();
            assert(slab_refused(st0, pb0, s0, src@, k));
            assert(pb0.fits(k));
            let (mid, s, q) = choose|mid: PageBuddy, s: SourceView, q: int| #[trigger]
                cut_run(pb0, mid, s0, s, q, k) && run_refused(st0, mid, s, r, q, k);
            assert(mid.fits(0));
            assert(s == s0);
            pb0.lemma_view(s0);
            let b = mid.span_base(span_of(q));
            assert(pb0.spans().contains_key(span_of(q)));
            assert(b == pb0.span_base(span_of(q)));
            assert(s0.spans.contains_key(b));
            let t = s0.backed_run(b, q, pages(k) as nat);
            assert(t.spans.dom() =~= s0.spans.dom());
            if !(r.request == (Request::Back { span: b, start: q, pages: pages(k) as nat }) && r.spans == s.spans) {
                assert(page_back_refusal(mid, t, r));
                let (mid2, m, q2) = choose|mid2: PageBuddy, m: SourceView, q2: int| #[trigger]
                    cut_run(mid, mid2, t, m, q2, 0) && r.request == (Request::Back {
                        span: mid2.span_base(span_of(q2)),
                        start: q2,
                        pages: 1,
                    }) && r.spans == m.spans;
                assert(m == t);
            }
        }
    }
    got
}

/// A full record store over a page buddy with a free page takes a record; returns whether it got
/// one. A refusal is of the back of the page cut for the record page, asked while the source held
/// the spans it held at the start: no run span was asked for, neither its reserve nor the back of its
/// metadata page.
pub fn witness_record_full<S: SpanSource>(store: &mut RecordStore, pb: &mut PageBuddy, src: &mut S) -> (got: bool)
    requires
        old(pb).wf(old(src)@),
        old(store).wf(*old(pb), old(src)@),
        old(pb).fits(0),
        old(store).full(),
    ensures
        final(store).wf(*final(pb), final(src)@),
        !got ==> {
            let r = final(src)@.refusals.last();
            &&& r.request is Back
            &&& r.spans == old(src)@.spans
        },
{
    let ghost pb0 = *pb;
    let ghost s0 = src@;
    match store.take(pb, src) {
        None => {
            proof {
                let r = src@.refusals.last();
                assert(back_refused(pb0, s0, src@));
                let (mid, m, q) = choose|mid: PageBuddy, m: SourceView, q: int| #[trigger]
                    cut_run(pb0, mid, s0, m, q, 0) && r.request == (Request::Back {
                        span: mid.span_base(span_of(q)),
                        start: q,
                        pages: 1,
                    }) && r.spans == m.spans;
                assert(m == s0);
            }
            false
        },
        Some(_) => true,
    }
}

/// Two size classes of one slab order over one record store and page buddy keeping no spare:
/// allocates a slot of the first class and one of the second; frees the first's slot, which
/// empties its slab, so its run and record go back while the second keeps its own; and allocates
/// of the first class again. Each step keeps both classes well formed and their heads disjoint, so
/// at the end a live slot of one is apart from every live slot of the other; a refusal stops the
/// sequence, and the last element says whether it ran to the end.
pub fn witness_free_emptied_two<S: SpanSource>(src: &mut S) -> (r: (SizeClass, SizeClass, RecordStore, PageBuddy, bool))
    requires
        old(src)@.wf(),
    ensures
        r.3.wf(final(src)@),
        r.2.wf(r.3, final(src)@),
        r.0.wf(r.2, r.3, final(src)@),
        r.1.wf(r.2, r.3, final(src)@),
        r.0.class() == 0,
        r.1.class() == 1,
        slab_order(0) == slab_order(1),
        r.0.heads().disjoint(r.1.heads()),
        forall|y: int, z: int|
            #![trigger r.0.live().contains(y), r.1.live().contains(z)]
            r.0.live().contains(y) && r.1.live().contains(z) ==> y + class_size(r.0.class()) <= z || z
                + class_size(r.1.class()) <= y,
{
    proof {
        assert(slab_order(0) == slab_order(1)) by (compute_only);
    }
    let mut pb = PageBuddy::new(0);
    let mut store = RecordStore::new();
    let mut first = SizeClass::new(0);
    let mut second = SizeClass::new(1);
    let ghost st0 = store;
    let ghost pb0 = pb;
    let ghost s0 = src@;
    let ghost f0 = first;
    let ghost l0 = second;
    proof {
        assert(f0.heads().disjoint(l0.heads()));
    }
    let r1 = first.alloc_small(&mut store, &mut pb, src);
    proof {
        second.lemma_frame(st0, pb0, s0, store, pb, src@);
        lemma_heads_grew(f0, first, st0, store, pb0, pb, s0, src@, r1);
        lemma_heads_stay_apart(f0, first, l0, st0, pb0, s0);
    }
    let (p1, perm1) = match r1 {
        Some(x) => x,
        None => {
            proof {
                lemma_witness_apart(first, second, store, pb, src@);
            }
            return (first, second, store, pb, false);
        },
    };
    let ghost st1 = store;
    let ghost pb1 = pb;
    let ghost s1 = src@;
    let ghost f1 = first;
    let ghost l1 = second;
    let ghost y = p1@.addr as int;
    let ghost a = choose|a: int| #[trigger]
        f1.slabs().contains_key(a) && {
            &&& !f0.slabs().contains_key(a)
            &&& f1.slabs() == f0.slabs().insert(a, f1.slabs()[a])
            &&& f1.slabs()[a].holds(y)
        };
    proof {
        assert(!exists|b: int| #[trigger]
            f0.slabs().contains_key(b) && f0.slabs()[b].free_slots() != Set::<int>::empty());
        assert(f1.slabs().dom() =~= set![a]);
    }
    let r2 = second.alloc_small(&mut store, &mut pb, src);
    proof {
        first.lemma_frame(st1, pb1, s1, store, pb, src@);
        lemma_heads_grew(l1, second, st1, store, pb1, pb, s1, src@, r2);
        lemma_heads_stay_apart(l1, second, first, st1, pb1, s1);
    }
    if r2.is_none() {
        proof {
            lemma_witness_apart(first, second, store, pb, src@);
        }
        return (first, second, store, pb, false);
    }
    let ghost st2 = store;
    let ghost pb2 = pb;
    let ghost s2 = src@;
    let ghost l2 = second;
    proof {
        assert(first == f1);
        assert(first.slabs().contains_key(a) && first.slabs()[a].holds(y));
        assert(first.slab_of(y) == a);
        assert forall|x: int| #[trigger] f1.slabs()[a].holds(x) implies x == y by {
            assert(live_of(f1.slabs()).contains(x));
            assert(f0.live().contains(x) || x == y);
        }
        assert(only_live(f1.slabs()[a], y));
    }
    first.records_apart(&second, Ghost(st2), Ghost(pb2), Ghost(s2));
    proof {
        assert(first == f1);
        assert(f1.heads().contains(f1.slabs()[a].base()@.addr as int));
    }
    first.free_small(&mut store, &mut pb, src, p1, perm1);
    proof {
        second.lemma_frame_emptied(st2, pb2, s2, store, pb, src@, a, f1.slabs()[a].base()@.addr as int);
        assert(first.heads().disjoint(second.heads()));
    }
    let ghost st3 = store;
    let ghost pb3 = pb;
    let ghost s3 = src@;
    let ghost f3 = first;
    let r3 = first.alloc_small(&mut store, &mut pb, src);
    proof {
        second.lemma_frame(st3, pb3, s3, store, pb, src@);
        lemma_heads_grew(f3, first, st3, store, pb3, pb, s3, src@, r3);
        lemma_heads_stay_apart(f3, first, second, st3, pb3, s3);
        lemma_witness_apart(first, second, store, pb, src@);
    }
    (first, second, store, pb, r3.is_some())
}

/// Two well-formed classes over one store, page buddy and source with disjoint heads have every
/// live slot of one apart from every live slot of the other.
proof fn lemma_witness_apart(first: SizeClass, last: SizeClass, store: RecordStore, pb: PageBuddy, src: SourceView)
    requires
        pb.wf(src),
        first.wf(store, pb, src),
        last.wf(store, pb, src),
        first.heads().disjoint(last.heads()),
    ensures
        forall|y: int, z: int|
            #![trigger first.live().contains(y), last.live().contains(z)]
            first.live().contains(y) && last.live().contains(z) ==> y + class_size(first.class()) <= z || z
                + class_size(last.class()) <= y,
{
    assert forall|y: int, z: int|
        #![trigger first.live().contains(y), last.live().contains(z)]
        first.live().contains(y) && last.live().contains(z) implies y + class_size(first.class()) <= z || z
            + class_size(last.class()) <= y by {
        first.lemma_classes_apart(&last, store, pb, src, y, z);
    }
}

/// The block and page of the run whose head is at `q`: its key in the page buddy's `used`.
spec fn head_of(q: int) -> (int, int) {
    (span_of(q), page_of(q))
}

/// The runs `u` holds, as the block and page of each head.
spec fn heads_of(u: Map<int, Map<int, nat>>) -> ISet<(int, int)> {
    ISet::new(|h: (int, int)| u.contains_key(h.0) && u[h.0].contains_key(h.1))
}

/// The source's view `s` is `start` but for the run spans the page buddy `pb` holds: the
/// provenance and refusals of `start`, its grants and more, every span of `start` as `start` holds
/// it, and every other span the first block of a span `pb` holds, whose base is none of `start`'s;
/// with the shape of `pb`'s spans this rests on, which its invariant holds but an intermediate view
/// of a call is not shown to.
spec fn tracks(start: SourceView, pb: PageBuddy, s: SourceView) -> bool {
    &&& s.provenance == start.provenance
    &&& s.refusals == start.refusals
    &&& start.grants.len() <= s.grants.len()
    &&& s.grants.subrange(0, start.grants.len() as int) == start.grants
    &&& forall|c: int| #[trigger]
        start.spans.contains_key(c) ==> s.spans.contains_key(c) && s.spans[c] == start.spans[c]
    &&& forall|c: int| #[trigger]
        s.spans.contains_key(c) && !start.spans.contains_key(c) ==> pb.spans().contains_key(c)
            && !pb.metas().contains(c)
    &&& forall|c: int| #[trigger] pb.spans().contains_key(c) ==> !start.spans.contains_key(pb.span_base(c))
    &&& forall|m: int| #[trigger]
        pb.metas().contains(m) ==> pb.spans().contains_key(m - BLOCK_BYTES as int) && !pb.metas().contains(
            m - BLOCK_BYTES as int,
        )
    &&& forall|c: int| #[trigger]
        pb.spans().contains_key(c) && !pb.metas().contains(c) ==> pb.metas().contains(meta_page(c))
    &&& pb.used().dom() == pb.spans().dom()
}

/// A page buddy holding no span tracks any source from its start.
proof fn lemma_tracks_new(start: SourceView, pb: PageBuddy)
    requires
        pb.spans() == Map::<int, Map<int, Block>>::empty(),
        pb.used() == Map::<int, Map<int, nat>>::empty(),
        pb.metas() == Set::<int>::empty(),
    ensures
        tracks(start, pb, start),
        heads_of(pb.used()) == ISet::<(int, int)>::empty(),
{
    assert(start.grants.subrange(0, start.grants.len() as int) =~= start.grants);
    assert(pb.used().dom() =~= pb.spans().dom());
    assert(heads_of(pb.used()) =~= ISet::<(int, int)>::empty());
}

/// The base of the span of a block `pb` holds is a first block it holds.
proof fn lemma_tracks_base(start: SourceView, pb: PageBuddy, s: SourceView, c: int)
    requires
        tracks(start, pb, s),
        pb.spans().contains_key(c),
    ensures
        pb.spans().contains_key(pb.span_base(c)),
        !pb.metas().contains(pb.span_base(c)),
        pb.metas().contains(meta_page(pb.span_base(c))),
        c == pb.span_base(c) || c == meta_page(pb.span_base(c)),
        !start.spans.contains_key(pb.span_base(c)),
{
    let b = pb.span_base(c);
    if pb.metas().contains(c) {
        assert(pb.spans().contains_key(c - BLOCK_BYTES as int));
    }
    assert(pb.spans().contains_key(b) && !pb.metas().contains(b));
}

/// Backing or releasing a run in a span the page buddy holds keeps the view tracked.
proof fn lemma_tracks_run(start: SourceView, pb: PageBuddy, s: SourceView, t: SourceView, c: int, q: int, n: nat)
    requires
        tracks(start, pb, s),
        pb.spans().contains_key(c),
        t == s.backed_run(pb.span_base(c), q, n) || t == s.released_run(pb.span_base(c), q, n),
    ensures
        tracks(start, pb, t),
{
    lemma_tracks_base(start, pb, s, c);
    let b = pb.span_base(c);
    assert(t.grants.subrange(0, start.grants.len() as int) =~= start.grants) by {
        assert(t.grants.subrange(0, start.grants.len() as int) =~= s.grants.subrange(0, start.grants.len() as int));
    }
    assert forall|x: int| #[trigger] start.spans.contains_key(x) implies t.spans.contains_key(x) && t.spans[x]
        == start.spans[x] by {
        assert(x != b);
    }
}

/// `alloc_run` cutting the run of order `k` at `q` keeps the view tracked and adds the run.
proof fn lemma_tracks_cut(
    start: SourceView,
    pb: PageBuddy,
    pb2: PageBuddy,
    s: SourceView,
    t: SourceView,
    q: int,
    k: nat,
)
    requires
        tracks(start, pb, s),
        cut_run(pb, pb2, s, t, q, k),
    ensures
        tracks(start, pb2, t),
        pb2.spans().contains_key(span_of(q)),
        heads_of(pb2.used()) == heads_of(pb.used()).insert(head_of(q)),
{
    let c = span_of(q);
    let h = page_of(q);
    let u = pb.used();
    let u2 = pb2.used();
    if pb.spans().contains_key(c) {
        assert(u.contains_key(c));
        assert(u2.dom() =~= pb2.spans().dom());
        assert forall|x: int| #[trigger] pb2.spans().contains_key(x) implies !start.spans.contains_key(
            pb2.span_base(x),
        ) by {
            assert(pb.spans().contains_key(x));
        }
        assert forall|m: int| #[trigger] pb2.metas().contains(m) implies pb2.spans().contains_key(m - BLOCK_BYTES as int)
            && !pb2.metas().contains(m - BLOCK_BYTES as int) by {
            assert(pb.metas().contains(m));
            assert(pb.spans().contains_key(m - BLOCK_BYTES as int));
        }
        assert forall|x: int| #[trigger] pb2.spans().contains_key(x) && !pb2.metas().contains(x) implies pb2.metas().contains(
            meta_page(x),
        ) by {
            assert(pb.spans().contains_key(x));
        }
        assert forall|x: int| #[trigger] t.spans.contains_key(x) && !start.spans.contains_key(x) implies pb2.spans().contains_key(x)
            && !pb2.metas().contains(x) by {
            assert(pb.spans().contains_key(x));
        }
        assert(heads_of(u2) =~= heads_of(u).insert(head_of(q)));
    } else {
        let b = c;
        let mb = meta_page(b);
        let f = fresh(u, b);
        assert(!u.contains_key(b) && !u.contains_key(mb));
        assert(u2.dom() =~= pb2.spans().dom());
        assert(t.grants.subrange(0, start.grants.len() as int) =~= start.grants) by {
            assert(t.grants.subrange(0, start.grants.len() as int) =~= s.grants.subrange(0, start.grants.len() as int));
        }
        assert(!start.spans.contains_key(b));
        assert forall|x: int| #[trigger] start.spans.contains_key(x) implies t.spans.contains_key(x) && t.spans[x]
            == start.spans[x] by {
            assert(x != b);
        }
        assert forall|x: int| #[trigger] t.spans.contains_key(x) && !start.spans.contains_key(x) implies pb2.spans().contains_key(x)
            && !pb2.metas().contains(x) by {
            if x != b {
                assert(s.spans.contains_key(x));
                assert(pb.spans().contains_key(x));
                assert(x != mb);
            }
        }
        assert forall|x: int| #[trigger] pb2.spans().contains_key(x) implies !start.spans.contains_key(
            pb2.span_base(x),
        ) by {
            if x != b && x != mb {
                assert(pb.spans().contains_key(x));
                assert(pb2.span_base(x) == pb.span_base(x));
            } else if x == mb {
                assert(pb2.metas().contains(mb));
            }
        }
        assert forall|m: int| #[trigger] pb2.metas().contains(m) implies pb2.spans().contains_key(m - BLOCK_BYTES as int)
            && !pb2.metas().contains(m - BLOCK_BYTES as int) by {
            if m != mb {
                assert(pb.metas().contains(m));
                assert(pb.spans().contains_key(m - BLOCK_BYTES as int));
            }
        }
        assert forall|x: int| #[trigger] pb2.spans().contains_key(x) && !pb2.metas().contains(x) implies pb2.metas().contains(
            meta_page(x),
        ) by {
            if x != b {
                assert(pb.spans().contains_key(x));
            }
        }
        assert(heads_of(f) =~= heads_of(u));
        assert(heads_of(u2) =~= heads_of(u).insert(head_of(q)));
    }
}

/// `free_run` taking back the run at `q`, which the page buddy holds a block of, keeps the view
/// tracked and takes the run out.
proof fn lemma_tracks_freed(start: SourceView, pb: PageBuddy, pb2: PageBuddy, s: SourceView, t: SourceView, q: int)
    requires
        tracks(start, pb, s),
        pb.used().contains_key(span_of(q)),
        freed(pb, pb2, s, t, q),
    ensures
        tracks(start, pb2, t),
        heads_of(pb2.used()) == heads_of(pb.used()).remove(head_of(q)),
{
    let c = span_of(q);
    let h = page_of(q);
    let u = pb.used();
    let u2 = pb2.used();
    let b = pb.span_base(c);
    let mb = meta_page(b);
    let rest = u.insert(c, u[c].remove(h));
    assert(pb.spans().contains_key(c));
    lemma_tracks_base(start, pb, s, c);
    if rest[b].dom() != Set::<int>::empty() || rest[mb].dom() != Set::<int>::empty() || pb.idle_spans().len()
        < pb.spares() {
        assert(u2.dom() =~= pb2.spans().dom());
        assert forall|x: int| #[trigger] pb2.spans().contains_key(x) implies !start.spans.contains_key(
            pb2.span_base(x),
        ) by {
            assert(pb.spans().contains_key(x));
        }
        assert forall|m: int| #[trigger] pb2.metas().contains(m) implies pb2.spans().contains_key(m - BLOCK_BYTES as int)
            && !pb2.metas().contains(m - BLOCK_BYTES as int) by {
            assert(pb.spans().contains_key(m - BLOCK_BYTES as int));
        }
        assert forall|x: int| #[trigger] pb2.spans().contains_key(x) && !pb2.metas().contains(x) implies pb2.metas().contains(
            meta_page(x),
        ) by {
            assert(pb.spans().contains_key(x));
        }
        assert forall|x: int| #[trigger] t.spans.contains_key(x) && !start.spans.contains_key(x) implies pb2.spans().contains_key(x)
            && !pb2.metas().contains(x) by {
            assert(pb.spans().contains_key(x));
        }
        assert(heads_of(u2) =~= heads_of(u).remove(head_of(q)));
    } else {
        assert(u2.dom() =~= pb2.spans().dom());
        assert forall|x: int| #[trigger] start.spans.contains_key(x) implies t.spans.contains_key(x) && t.spans[x]
            == start.spans[x] by {
            assert(x != b);
        }
        assert forall|x: int| #[trigger] t.spans.contains_key(x) && !start.spans.contains_key(x) implies pb2.spans().contains_key(x)
            && !pb2.metas().contains(x) by {
            assert(s.spans.contains_key(x));
            assert(pb.spans().contains_key(x) && !pb.metas().contains(x));
            assert(x != mb);
        }
        assert forall|x: int| #[trigger] pb2.spans().contains_key(x) implies !start.spans.contains_key(
            pb2.span_base(x),
        ) by {
            assert(pb.spans().contains_key(x));
            assert(x != mb);
            assert(pb2.span_base(x) == pb.span_base(x));
        }
        assert forall|m: int| #[trigger] pb2.metas().contains(m) implies pb2.spans().contains_key(m - BLOCK_BYTES as int)
            && !pb2.metas().contains(m - BLOCK_BYTES as int) by {
            assert(pb.metas().contains(m) && m != mb);
            assert(pb.spans().contains_key(m - BLOCK_BYTES as int));
            assert(!pb.metas().contains(m - BLOCK_BYTES as int));
        }
        assert forall|x: int| #[trigger] pb2.spans().contains_key(x) && !pb2.metas().contains(x) implies pb2.metas().contains(
            meta_page(x),
        ) by {
            assert(pb.spans().contains_key(x));
            assert(x != mb && x != b);
        }
        assert forall|hh: (int, int)| heads_of(u2).contains(hh) == heads_of(u).remove(head_of(q)).contains(hh) by {
            if hh.0 == b || hh.0 == mb {
                if u.contains_key(hh.0) && u[hh.0].contains_key(hh.1) && hh != head_of(q) {
                    assert(rest[hh.0].contains_key(hh.1));
                }
            }
        }
        assert(heads_of(u2) =~= heads_of(u).remove(head_of(q)));
    }
}

/// `alloc_run` cutting the run of order `k` at `q`, then its pages backed, keeps the view tracked
/// and adds the run.
proof fn lemma_tracks_took(
    start: SourceView,
    pb: PageBuddy,
    pb2: PageBuddy,
    s: SourceView,
    m: SourceView,
    t: SourceView,
    q: int,
    k: nat,
    n: nat,
)
    requires
        tracks(start, pb, s),
        cut_run(pb, pb2, s, m, q, k),
        t == m.backed_run(pb2.span_base(span_of(q)), q, n),
    ensures
        tracks(start, pb2, t),
        heads_of(pb2.used()) == heads_of(pb.used()).insert(head_of(q)),
{
    lemma_tracks_cut(start, pb, pb2, s, m, q, k);
    lemma_tracks_run(start, pb2, m, t, span_of(q), q, n);
}

/// `alloc_small` making a new slab keeps the view tracked, and adds the slab's run and, when the
/// store was full, its record page.
proof fn lemma_tracks_new_slab(
    start: SourceView,
    st0: RecordStore,
    st1: RecordStore,
    pb0: PageBuddy,
    pb1: PageBuddy,
    s0: SourceView,
    s1: SourceView,
    a: int,
    x: int,
    k: nat,
)
    requires
        tracks(start, pb0, s0),
        new_slab(st0, st1, pb0, pb1, s0, s1, a, x, k),
    ensures
        tracks(start, pb1, s1),
        heads_of(pb1.used()) == if st0.full() {
            heads_of(pb0.used()).insert(head_of(x)).insert(head_of(record_page(a)))
        } else {
            heads_of(pb0.used()).insert(head_of(x))
        },
{
    let (pbm, sm) = choose|pbm: PageBuddy, sm: SourceView| #[trigger]
        took_run(pb0, pbm, s0, sm, x, k) && if st0.full() {
            took_page(pbm, pb1, sm, s1, record_page(a))
        } else {
            pb1 == pbm && s1 == sm
        };
    let c = span_of(x);
    let m = if pb0.spans().contains_key(c) {
        s0
    } else {
        s0.reserved(c, SPAN_BLOCKS as nat).backed_run(c, meta_page(c), 1)
    };
    lemma_tracks_took(start, pb0, pbm, s0, m, sm, x, k, pages(k) as nat);
    if st0.full() {
        let q = record_page(a);
        let cq = span_of(q);
        let mq = if pbm.spans().contains_key(cq) {
            sm
        } else {
            sm.reserved(cq, SPAN_BLOCKS as nat).backed_run(cq, meta_page(cq), 1)
        };
        lemma_tracks_took(start, pbm, pb1, sm, mq, s1, q, 0, 1);
    }
}

/// `free_small` retiring a slab keeps the view tracked, and takes out the slab's run and, when no
/// other record lay on it, its record page.
proof fn lemma_tracks_emptied(
    start: SourceView,
    st0: RecordStore,
    st1: RecordStore,
    pb0: PageBuddy,
    pb1: PageBuddy,
    s0: SourceView,
    s1: SourceView,
    a: int,
    x: int,
    k: nat,
)
    requires
        tracks(start, pb0, s0),
        emptied_slab(st0, st1, pb0, pb1, s0, s1, a, x, k),
        heads_of(pb0.used()).contains(head_of(x)),
        heads_of(pb0.used()).contains(head_of(record_page(a))),
        head_of(record_page(a)) != head_of(x),
    ensures
        tracks(start, pb1, s1),
        heads_of(pb1.used()) == if page_shared(st0, a) {
            heads_of(pb0.used()).remove(head_of(x))
        } else {
            heads_of(pb0.used()).remove(head_of(x)).remove(head_of(record_page(a)))
        },
{
    let c = span_of(x);
    let sr = s0.released_run(pb0.span_base(c), x, pages(k) as nat);
    let (pbm, sm) = choose|pbm: PageBuddy, sm: SourceView| #[trigger]
        freed(pb0, pbm, sr, sm, x) && if page_shared(st0, a) {
            pb1 == pbm && s1 == sm
        } else {
            gave_back(pbm, pb1, sm, s1, record_page(a))
        };
    assert(pb0.used().contains_key(c));
    lemma_tracks_run(start, pb0, s0, sr, c, x, pages(k) as nat);
    lemma_tracks_freed(start, pb0, pbm, sr, sm, x);
    if !page_shared(st0, a) {
        let q = record_page(a);
        let cq = span_of(q);
        assert(heads_of(pbm.used()).contains(head_of(q)));
        assert(pbm.used().contains_key(cq));
        let sq = sm.released_run(pbm.span_base(cq), q, 1);
        lemma_tracks_run(start, pbm, sm, sq, cq, q, 1);
        lemma_tracks_freed(start, pbm, pb1, sq, s1, q);
    }
}

/// `free_small` retiring a slab keeps the source's provenance and refusals.
proof fn lemma_emptied_refusals(
    st0: RecordStore,
    st1: RecordStore,
    pb0: PageBuddy,
    pb1: PageBuddy,
    s0: SourceView,
    s1: SourceView,
    a: int,
    x: int,
    k: nat,
)
    requires
        emptied_slab(st0, st1, pb0, pb1, s0, s1, a, x, k),
    ensures
        s1.provenance == s0.provenance,
        s1.refusals == s0.refusals,
{
    let sr = s0.released_run(pb0.span_base(span_of(x)), x, pages(k) as nat);
    let (pbm, sm) = choose|pbm: PageBuddy, sm: SourceView| #[trigger]
        freed(pb0, pbm, sr, sm, x) && if page_shared(st0, a) {
            pb1 == pbm && s1 == sm
        } else {
            gave_back(pbm, pb1, sm, s1, record_page(a))
        };
}

/// A page buddy keeping no spare and holding no run holds no span, and a view it tracks is its
/// start with only grants added.
proof fn lemma_tracks_end(start: SourceView, pb: PageBuddy, s: SourceView)
    requires
        tracks(start, pb, s),
        pb.wf(s),
        pb.spares() == 0,
        heads_of(pb.used()) == ISet::<(int, int)>::empty(),
    ensures
        pb.spans().dom() == Set::<int>::empty(),
        s == start.granted(s.grants.subrange(start.grants.len() as int, s.grants.len() as int)),
{
    pb.lemma_view(s);
    let u = pb.used();
    assert forall|m: int| pb.metas().contains(m) implies false by {
        let lo = m - BLOCK_BYTES as int;
        assert(u.contains_key(m) && u.contains_key(lo));
        assert(u[m].dom() =~= Set::<int>::empty()) by {
            assert forall|y: int| !u[m].contains_key(y) by {
                assert(!heads_of(u).contains((m, y)));
            }
        }
        assert(u[lo].dom() =~= Set::<int>::empty()) by {
            assert forall|y: int| !u[lo].contains_key(y) by {
                assert(!heads_of(u).contains((lo, y)));
            }
        }
        assert(pb.idle_spans().contains(m));
        pb.idle_spans().lemma_len0_is_empty();
    }
    assert(pb.spans().dom() =~= Set::<int>::empty()) by {
        assert forall|c: int| !pb.spans().contains_key(c) by {
            if pb.spans().contains_key(c) && !pb.metas().contains(c) {
                assert(pb.metas().contains(meta_page(c)));
            }
        }
    }
    let g = s.grants.subrange(start.grants.len() as int, s.grants.len() as int);
    assert(s.spans =~= start.spans) by {
        assert forall|c: int| s.spans.contains_key(c) implies start.spans.contains_key(c) by {
            if !start.spans.contains_key(c) {
                assert(pb.spans().contains_key(c));
            }
        }
    }
    assert(s.grants =~= start.grants + g);
    assert(s == start.granted(g));
}

/// Two distinct page-aligned addresses are the heads of different runs.
proof fn lemma_heads_differ(x: int, y: int)
    requires
        0 <= x,
        0 <= y,
        x % PAGE_BYTES as int == 0,
        y % PAGE_BYTES as int == 0,
        x != y,
    ensures
        head_of(x) != head_of(y),
{
    lemma_head(x);
    lemma_head(y);
}

/// Before `free_small` retires the slab of `c` whose record is `a`, the page buddy holds the slab's
/// run and the record's page, two runs.
proof fn lemma_free_ready(c: SizeClass, st: RecordStore, pb: PageBuddy, s: SourceView, a: int)
    requires
        c.wf(st, pb, s),
        st.wf(pb, s),
        pb.wf(s),
        c.slabs().contains_key(a),
        c.heads().contains(c.slabs()[a].base()@.addr as int),
        st.taken().contains(a),
    ensures
        heads_of(pb.used()).contains(head_of(c.slabs()[a].base()@.addr as int)),
        heads_of(pb.used()).contains(head_of(record_page(a))),
        head_of(record_page(a)) != head_of(c.slabs()[a].base()@.addr as int),
{
    let x = c.slabs()[a].base()@.addr as int;
    let q = record_page(a);
    c.lemma_heads_held(st, pb, s);
    st.lemma_view(pb, s);
    pb.lemma_view(s);
    assert(run_held(pb, s, x, slab_order(c.class())));
    assert(st.pages().contains(q));
    assert(run_held(pb, s, q, 0));
    assert(pb.spans().contains_key(span_of(q)));
    assert(q >= span_of(q));
    lemma_heads_differ(q, x);
}

/// Writes a byte at `p` through the permission to the `n` bytes from it, reads it again, and
/// returns the permission to the `n` bytes.
fn touch(p: *mut u8, perm: Tracked<PointsToRaw>, Ghost(n): Ghost<int>) -> (r: Tracked<PointsToRaw>)
    requires
        n >= 1,
        perm@.is_range(p@.addr as int, n),
        perm@.provenance() == p@.provenance,
    ensures
        r@.is_range(p@.addr as int, n),
        r@.provenance() == perm@.provenance(),
{
    let addr = p.addr();
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
    assert(whole.dom() =~= Set::range(addr as int, addr as int + n));
    Tracked(whole)
}

/// The smallest and the largest size class over one record store and a page buddy holding nothing
/// and keeping no spare: allocates a slot of each, writes a byte of each and reads it again, and
/// frees both. Returns both classes, the store, the page buddy and whether both slots were given.
/// Either way neither class has a slab and the store has no record taken at the end. When both
/// were given, the store has no record page, the page buddy holds no span, and the source's view
/// is the one it started with, the requests the sequence made granted. Otherwise the source refused
/// once, a request one of the two allocations made (`slab_refused`), with the refusals it had at the
/// start, and the sequence stopped after freeing what it took: either the first allocation, from the
/// source's starting view with no record taken, or the second, once the first had taken a record
/// for the slab it made.
pub fn witness_small_classes<S: SpanSource>(src: &mut S) -> (r: (SizeClass, SizeClass, RecordStore, PageBuddy, bool))
    requires
        old(src)@.wf(),
    ensures
        r.3.wf(final(src)@),
        r.2.wf(r.3, final(src)@),
        r.0.wf(r.2, r.3, final(src)@),
        r.1.wf(r.2, r.3, final(src)@),
        r.0.class() == 0,
        r.1.class() == CLASSES - 1,
        r.0.slabs() == Map::<int, Slab>::empty(),
        r.1.slabs() == Map::<int, Slab>::empty(),
        r.2.taken() == Set::<int>::empty(),
        r.3.spares() == 0,
        if r.4 {
            &&& r.2.pages() == Set::<int>::empty()
            &&& r.3.spans().dom() == Set::<int>::empty()
            &&& final(src)@ == old(src)@.granted(
                final(src)@.grants.subrange(old(src)@.grants.len() as int, final(src)@.grants.len() as int),
            )
        } else {
            let f = final(src)@.refusals.last();
            &&& final(src)@.provenance == old(src)@.provenance
            &&& final(src)@.refusals == old(src)@.refusals.push(f)
            &&& exists|st: RecordStore, pb: PageBuddy, s: SourceView, t: SourceView, c: nat| #[trigger]
                slab_refused(st, pb, s, t, slab_order(c)) && s.refusals == old(src)@.refusals
                    && t.refusals.last() == f && {
                    ||| c == 0 && st.taken() == Set::<int>::empty() && s == old(src)@
                    ||| c == CLASSES - 1 && st.taken() != Set::<int>::empty()
                }
        },
{
    let ghost start = src@;
    let mut pb = PageBuddy::new(0);
    let mut store = RecordStore::new();
    let mut first = SizeClass::new(0);
    let mut last = SizeClass::new(CLASSES - 1);
    let ghost st0 = store;
    let ghost pb0 = pb;
    let ghost s0 = src@;
    let ghost f0 = first;
    let ghost l0 = last;
    let ghost k0 = slab_order(0);
    let ghost k1 = slab_order((CLASSES - 1) as nat);
    proof {
        lemma_class(0);
        lemma_class((CLASSES - 1) as nat);
        lemma_tracks_new(start, pb0);
        assert(f0.heads().disjoint(l0.heads()));
    }
    let r1 = first.alloc_small(&mut store, &mut pb, src);
    proof {
        last.lemma_frame(st0, pb0, s0, store, pb, src@);
        lemma_heads_grew(f0, first, st0, store, pb0, pb, s0, src@, r1);
        lemma_heads_stay_apart(f0, first, l0, st0, pb0, s0);
    }
    let (p1, perm1) = match r1 {
        Some(x) => x,
        None => {
            proof {
                assert(slab_refused(st0, pb0, s0, src@, slab_order(0)));
            }
            return (first, last, store, pb, false);
        },
    };
    let ghost st1 = store;
    let ghost pb1 = pb;
    let ghost s1 = src@;
    let ghost f1 = first;
    let ghost y1 = p1@.addr as int;
    proof {
        assert(!exists|b: int| #[trigger]
            f0.slabs().contains_key(b) && f0.slabs()[b].free_slots() != Set::<int>::empty());
    }
    let ghost a0 = choose|a: int| #[trigger]
        f1.slabs().contains_key(a) && {
            &&& !f0.slabs().contains_key(a)
            &&& f1.slabs() == f0.slabs().insert(a, f1.slabs()[a])
            &&& f1.slabs()[a].holds(y1)
            &&& f1.heads() == f0.heads().insert(f1.slabs()[a].base()@.addr as int)
            &&& new_slab(st0, st1, pb0, pb1, s0, s1, a, f1.slabs()[a].base()@.addr as int, k0)
        };
    let ghost x0 = f1.slabs()[a0].base()@.addr as int;
    proof {
        lemma_tracks_new_slab(start, st0, st1, pb0, pb1, s0, s1, a0, x0, k0);
        assert(f1.slabs().dom() =~= set![a0]);
        assert(st1.taken() =~= set![a0]);
        assert(st1.pages() =~= set![record_page(a0)]);
        assert(f1.slab_of(y1) == a0);
        assert forall|z: int| #[trigger] f1.slabs()[a0].holds(z) implies z == y1 by {
            assert(live_of(f1.slabs()).contains(z));
            assert(f0.live().contains(z) || z == y1);
        }
        assert(only_live(f1.slabs()[a0], y1));
    }
    let perm1 = touch(p1, perm1, Ghost(class_size(0) as int));
    let ghost l1 = last;
    let r2 = last.alloc_small(&mut store, &mut pb, src);
    proof {
        first.lemma_frame(st1, pb1, s1, store, pb, src@);
        lemma_heads_grew(l1, last, st1, store, pb1, pb, s1, src@, r2);
        lemma_heads_stay_apart(l1, last, first, st1, pb1, s1);
    }
    let ghost st2 = store;
    let ghost pb2 = pb;
    let ghost s2 = src@;
    let (p2, perm2) = match r2 {
        Some(x) => x,
        None => {
            proof {
                assert(slab_refused(st1, pb1, s1, s2, slab_order((CLASSES - 1) as nat)));
                assert(st1.taken().contains(a0));
                assert(first == f1);
                assert(f1.heads().contains(x0)) by {
                    assert(f1.slabs().contains_key(a0) && f1.slabs()[a0].base()@.addr == x0);
                }
            }
            first.free_small(&mut store, &mut pb, src, p1, perm1);
            proof {
                last.lemma_frame_emptied(st2, pb2, s2, store, pb, src@, a0, x0);
                lemma_emptied_refusals(st2, store, pb2, pb, s2, src@, a0, x0, k0);
                assert(first.slabs() =~= Map::<int, Slab>::empty());
                assert(store.taken() =~= Set::<int>::empty());
            }
            return (first, last, store, pb, false);
        },
    };
    let ghost l2 = last;
    let ghost y2 = p2@.addr as int;
    proof {
        assert(!exists|b: int| #[trigger]
            l1.slabs().contains_key(b) && l1.slabs()[b].free_slots() != Set::<int>::empty());
    }
    let ghost a1 = choose|a: int| #[trigger]
        l2.slabs().contains_key(a) && {
            &&& !l1.slabs().contains_key(a)
            &&& l2.slabs() == l1.slabs().insert(a, l2.slabs()[a])
            &&& l2.slabs()[a].holds(y2)
            &&& l2.heads() == l1.heads().insert(l2.slabs()[a].base()@.addr as int)
            &&& new_slab(st1, st2, pb1, pb2, s1, s2, a, l2.slabs()[a].base()@.addr as int, k1)
        };
    let ghost x1 = l2.slabs()[a1].base()@.addr as int;
    let ghost r0 = record_page(a0);
    let ghost r1p = record_page(a1);
    proof {
        lemma_tracks_new_slab(start, st1, st2, pb1, pb2, s1, s2, a1, x1, k1);
        assert(l2.slabs().dom() =~= set![a1]);
        assert(st2.taken() =~= set![a0, a1]);
        assert(a0 != a1);
        assert(st2.taken().contains(a1));
        st2.lemma_view(pb2, s2);
        assert(st2.pages().contains(r1p));
        if st1.full() {
            assert(r1p != r0);
        } else {
            assert(r1p == r0);
        }
        assert(l2.slab_of(y2) == a1);
        assert forall|z: int| #[trigger] l2.slabs()[a1].holds(z) implies z == y2 by {
            assert(live_of(l2.slabs()).contains(z));
            assert(l1.live().contains(z) || z == y2);
        }
        assert(only_live(l2.slabs()[a1], y2));
        assert(first == f1);
        assert(f1.heads().contains(x0)) by {
            assert(f1.slabs().contains_key(a0) && f1.slabs()[a0].base()@.addr == x0);
        }
        assert(l2.heads().contains(x1)) by {
            assert(l2.slabs().contains_key(a1) && l2.slabs()[a1].base()@.addr == x1);
        }
        lemma_free_ready(f1, st2, pb2, s2, a0);
    }
    let perm2 = touch(p2, perm2, Ghost(class_size((CLASSES - 1) as nat) as int));
    first.free_small(&mut store, &mut pb, src, p1, perm1);
    let ghost st3 = store;
    let ghost pb3 = pb;
    let ghost s3 = src@;
    proof {
        assert(!l2.slabs().contains_key(a0));
        last.lemma_frame_emptied(st2, pb2, s2, store, pb, src@, a0, x0);
        lemma_tracks_emptied(start, st2, st3, pb2, pb3, s2, s3, a0, x0, k0);
        assert(st3.taken() =~= set![a1]);
        if st1.full() {
            assert(!page_shared(st2, a0)) by {
                assert forall|z: int| #[trigger] st2.taken().contains(z) && z != a0 implies record_page(z) != r0 by {
                    assert(z == a1);
                }
            }
        } else {
            assert(page_shared(st2, a0)) by {
                assert(st2.taken().contains(a1) && a1 != a0 && record_page(a1) == record_page(a0));
            }
        }
        assert(!page_shared(st3, a1)) by {
            assert forall|z: int| #[trigger] st3.taken().contains(z) && z != a1 implies false by {}
        }
        assert(first.slabs() =~= Map::<int, Slab>::empty());
        assert(first.heads() =~= ISet::<int>::empty());
        assert(last == l2);
        lemma_free_ready(l2, st3, pb3, s3, a1);
    }
    last.free_small(&mut store, &mut pb, src, p2, perm2);
    proof {
        first.lemma_frame_emptied(st3, pb3, s3, store, pb, src@, a1, x1);
        lemma_tracks_emptied(start, st3, store, pb3, pb, s3, src@, a1, x1, k1);
        assert(heads_of(pb.used()) =~= ISet::<(int, int)>::empty());
        lemma_tracks_end(start, pb, src@);
        assert(last.slabs() =~= Map::<int, Slab>::empty());
        assert(store.taken() =~= Set::<int>::empty());
        assert(store.pages() =~= Set::<int>::empty());
    }
    (first, last, store, pb, true)
}

} // verus!
