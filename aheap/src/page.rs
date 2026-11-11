// SPDX-License-Identifier: MIT

//! The page buddy: page runs cut from spans of one block each, a block buddy per span.
//!
//! It owns the span source. Each span it holds, a run span, is a reserved span of one block whose
//! backed pages lie in its allocated runs, cut by the `BlockBuddy` of that span. The records of the block buddies lie in the
//! metadata page: the first page of a metadata span of one block that the page buddy reserves and
//! backs itself, cut into SPANS records, one per run span it can hold. No record is in a run span, so
//! a run span can give its whole block. The metadata span is reserved and backed with the first run
//! span, and given back with the last.
//!
//! - `alloc_run(k)` takes from the held span with a free block of the smallest order at or above k,
//!   across every held span; only when none has one does it reserve a new span. It refuses, and
//!   changes no held span, exactly when no held span has such a block and either SPANS spans are
//!   held (`Full`) or the source refused (`Source`).
//! - `free_run(p)` takes back the run at p and never refuses. A span left with no run is given back
//!   to the source, unless fewer than the configured spares are idle, when it stays as a spare. The
//!   run's pages must be unbacked.
//! - `back_run(p, k)` backs the pages of the allocated run at p through the source and returns a
//!   pointer to it with the permission to its bytes, or refuses and changes nothing;
//!   `release_run(p, k, perm)` gives them back. A run `alloc_run` returns has no page backed: the
//!   page buddy does not back the runs it cuts, and its caller backs what it writes.
//!
//! Each states the source's view after it exactly: a refusal by the source leaves it as it was with
//! that one refusal counted, so `Source` and a `None` from `back_run` answer only a refusal the source
//! made in the call; `Full` and a run from a held span leave it as it was, a new span is reserved
//! (`took_span`), and a span given back is released (`gave_span`), so a sequence that frees every run
//! it cut ends at the view it started from.
//!
//! `lemma_view` states the invariant on the view, among it that a held span with no run is the
//! initial block, so `lemma_idle_fits` shows a run of any order fits while such a span is held.
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::layout::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::set::*;

use crate::arch::*;
use crate::buddy::*;
use crate::source::*;

verus! {

broadcast use group_raw_ptr_axioms, vstd::set_lib::range_set_properties;

/// The records one metadata page holds, and so the run spans the page buddy can hold.
pub const SPANS: usize = PAGE_BYTES / BLOCK_PAGES;

/// Why `alloc_run` refused.
pub enum Refused {
    /// SPANS spans are held and none has a free block of the order asked.
    Full,
    /// The source refused to reserve a span, or to back the metadata page, in this call: its view
    /// counts one more refusal.
    Source,
}

/// The base of the span of one block that holds address `p`.
pub open spec fn span_of(p: int) -> int {
    p - p % BLOCK_BYTES as int
}

/// The page of its span that address `p` is in.
pub open spec fn page_of(p: int) -> int {
    (p % BLOCK_BYTES as int) / PAGE_BYTES as int
}

/// The allocated runs of a block's blocks, by head, with their orders.
pub open spec fn used_of(blocks: Map<int, Block>) -> Map<int, nat> {
    Map::new(blocks.dom().filter(|h: int| !blocks[h].free), |h: int| blocks[h].order)
}

/// The spans whose used runs `used` maps to none.
pub open spec fn idle_of(used: Map<int, Map<int, nat>>) -> Set<int> {
    used.dom().filter(|b: int| used[b].dom() == Set::<int>::empty())
}

/// The blocks of the block buddy each span's record holds.
spec fn spans_of(slot: Map<int, int>, records: Map<int, PointsTo<BlockBuddy>>) -> Map<int, Map<int, Block>> {
    slot.map_values(|i: int| records[i].value().blocks())
}

/// The used runs of the block buddy each span's record holds.
spec fn used_in(slot: Map<int, int>, records: Map<int, PointsTo<BlockBuddy>>) -> Map<int, Map<int, nat>> {
    slot.map_values(|i: int| records[i].value().used())
}

/// The pointer to record `i` of the metadata page at `m`.
pub open spec fn record_ptr(m: int, provenance: Provenance, i: int) -> *mut BlockBuddy {
    ptr_mut_from_data(PtrData { addr: (m + i * BLOCK_PAGES as int) as usize, provenance, metadata: () })
}

/// Address `a` is a page of one of the runs `u` holds, by head, in the span at `b`.
pub open spec fn in_runs(b: int, u: Map<int, nat>, a: int) -> bool {
    exists|q: int| #[trigger] u.contains_key(q) && run_pages(b + q * PAGE_BYTES as int, pages(u[q]) as nat).contains(a)
}

/// The span at `b` is a reserved span of one block whose backed pages lie in the runs `u` holds.
pub open spec fn held(src: SourceView, b: int, u: Map<int, nat>) -> bool {
    &&& src.spans.contains_key(b)
    &&& src.spans[b].blocks == 1
    &&& forall|a: int| #[trigger] src.spans[b].backed.contains(a) ==> in_runs(b, u, a)
}

/// `after` is `before` with a run of order `k` cut at `p`, in the span of `p`, apart from every run
/// that span had.
pub open spec fn cut(before: Map<int, Map<int, nat>>, after: Map<int, Map<int, nat>>, p: int, k: nat) -> bool {
    let b = span_of(p);
    let h = page_of(p);
    &&& p % PAGE_BYTES as int == 0
    &&& placed(h, Block { order: k, free: false })
    &&& before.contains_key(b) ==> forall|q: int|
        #[trigger] before[b].contains_key(q) ==> h + pages(k) <= q || q + pages(before[b][q]) <= h
    &&& after == before.insert(
        b,
        if before.contains_key(b) {
            before[b].insert(h, k)
        } else {
            Map::<int, nat>::empty().insert(h, k)
        },
    )
}

/// The block at `h` of the span at `b` is free, of order `k` or more, and no free block of order `k`
/// or more in any span has a smaller order.
pub open spec fn best(spans: Map<int, Map<int, Block>>, b: int, h: int, k: nat) -> bool {
    &&& spans.contains_key(b)
    &&& spans[b].contains_key(h)
    &&& spans[b][h].free
    &&& spans[b][h].order >= k
    &&& forall|c: int, q: int|
        #![trigger spans[c].contains_key(q)]
        spans.contains_key(c) && spans[c].contains_key(q) && spans[c][q].free && spans[c][q].order
            >= k ==> spans[c][q].order >= spans[b][h].order
}

/// The source went from `before` to `after` by reserving the new span at `b`, of one block, and,
/// when no metadata span was held, by first reserving a new metadata span and backing its first
/// page, the metadata span then held.
pub open spec fn took_span(before: SourceView, meta: Option<int>, after: SourceView, meta_after: Option<int>, b: int) -> bool {
    &&& !before.spans.contains_key(b)
    &&& meta_after is Some
    &&& match meta {
        Some(m) => {
            &&& meta_after == meta
            &&& after == before.reserved(b, 1)
        },
        None => {
            let m = meta_after->Some_0;
            &&& !before.spans.contains_key(m)
            &&& m != b
            &&& after == before.reserved(m, 1).backed_run(m, m, 1).reserved(b, 1)
        },
    }
}

/// The source went from `before` to `after` by giving back the span at `b` and, when it was the
/// `last` run span, then releasing the metadata page and giving back the metadata span, which is no
/// longer held.
pub open spec fn gave_span(before: SourceView, meta: Option<int>, after: SourceView, meta_after: Option<int>, b: int, last: bool) -> bool {
    if last {
        let m = meta->Some_0;
        &&& meta is Some
        &&& meta_after is None
        &&& after == before.released_span(b).released_run(m, m, 1).released_span(m)
    } else {
        &&& meta_after == meta
        &&& after == before.released_span(b)
    }
}

/// A record is one tag byte per page of a block, and SPANS of them fill a page.
proof fn lemma_layout()
    ensures
        size_of::<BlockBuddy>() == BLOCK_PAGES,
        align_of::<BlockBuddy>() == 1,
        SPANS * BLOCK_PAGES == PAGE_BYTES,
{
    lemma_block_buddy_layout();
}

/// The page `h` of the block-aligned span at `base` is a page whose span is `base` and whose page
/// is `h`.
proof fn lemma_address(base: int, h: int)
    requires
        base % BLOCK_BYTES as int == 0,
        0 <= h < BLOCK_PAGES,
    ensures
        span_of(base + h * PAGE_BYTES) == base,
        page_of(base + h * PAGE_BYTES) == h,
        (base + h * PAGE_BYTES) % PAGE_BYTES as int == 0,
{
    let bb = BLOCK_BYTES as int;
    let pb = PAGE_BYTES as int;
    let p = base + h * pb;
    let q = base / bb;
    lemma_fundamental_div_mod(base, bb);
    assert(base == q * bb + 0);
    assert(0 <= h * pb < bb);
    assert(p == q * bb + h * pb);
    lemma_fundamental_div_mod_converse_mod(p, bb, q, h * pb);
    lemma_fundamental_div_mod_converse_div(h * pb, pb, h, 0);
    assert(p == (q * BLOCK_PAGES as int + h) * pb + 0) by (nonlinear_arith)
        requires
            p == q * bb + h * pb,
            bb == pb * BLOCK_PAGES as int,
    ;
    lemma_fundamental_div_mod_converse_mod(p, pb, q * BLOCK_PAGES as int + h, 0);
}

/// A page-aligned address is page `page_of(p)` of the block-aligned span at `span_of(p)`: the
/// converse of `lemma_address`.
pub proof fn lemma_head(p: int)
    requires
        0 <= p,
        p % PAGE_BYTES as int == 0,
    ensures
        span_of(p) % BLOCK_BYTES as int == 0,
        0 <= page_of(p) < BLOCK_PAGES,
        p == span_of(p) + page_of(p) * PAGE_BYTES,
{
    let bb = BLOCK_BYTES as int;
    let pb = PAGE_BYTES as int;
    let r = p % bb;
    let q = p / bb;
    lemma_fundamental_div_mod(p, bb);
    assert(p - r == q * bb);
    lemma_mod_multiples_basic(q, bb);
    lemma_mod_mod(p, pb, BLOCK_PAGES as int);
    assert(r % pb == 0);
    lemma_fundamental_div_mod(r, pb);
    let d = r / pb;
    assert(r == pb * d);
    assert(0 <= d < BLOCK_PAGES) by (nonlinear_arith)
        requires
            r == pb * d,
            0 <= r < pb * BLOCK_PAGES as int,
            pb > 0,
    ;
}

/// Runs of `n` pages at page `h` and of `o` pages at page `q` of the span at `b`, apart as pages,
/// share no address.
proof fn lemma_runs_apart(b: int, h: int, n: int, q: int, o: int)
    requires
        h + n <= q || q + o <= h,
        n >= 0,
        o >= 0,
    ensures
        run_pages(b + h * PAGE_BYTES as int, n as nat).disjoint(run_pages(b + q * PAGE_BYTES as int, o as nat)),
{
    let pb = PAGE_BYTES as int;
    if h + n <= q {
        assert(h * pb + n * pb <= q * pb) by (nonlinear_arith)
            requires
                h + n <= q,
                pb > 0,
        ;
    } else {
        assert(q * pb + o * pb <= h * pb) by (nonlinear_arith)
            requires
                q + o <= h,
                pb > 0,
        ;
    }
}

/// Cuts the permission to records `i` up to SPANS of the metadata page at `m` into one typed,
/// uninitialized permission per record.
proof fn carve(tracked raw: PointsToRaw, m: int, i: int) -> (tracked r: Map<int, PointsTo<BlockBuddy>>)
    requires
        0 <= i <= SPANS,
        0 < m,
        m + PAGE_BYTES <= usize::MAX,
        raw.is_range(m + i * BLOCK_PAGES, (SPANS - i) * BLOCK_PAGES),
    ensures
        r.dom() == Set::range(i, SPANS as int),
        forall|j: int|
            i <= j < SPANS ==> #[trigger] r[j].ptr() == record_ptr(m, raw.provenance(), j)
                && r[j].is_uninit(),
    decreases SPANS - i,
{
    lemma_layout();
    if i == SPANS {
        let tracked r = Map::tracked_empty();
        assert(r.dom() =~= Set::range(i, SPANS as int));
        r
    } else {
        let a = m + i * BLOCK_PAGES;
        let tracked (one, rest) = raw.split(Set::range(a, a + BLOCK_PAGES));
        assert(rest.dom() =~= Set::range(m + (i + 1) * BLOCK_PAGES, m + (i + 1) * BLOCK_PAGES + (SPANS
            - (i + 1)) * BLOCK_PAGES));
        let tracked typed = one.into_typed::<BlockBuddy>(a as usize);
        let tracked mut r = carve(rest, m, i + 1);
        r.tracked_insert(i, typed);
        assert(r.dom() =~= Set::range(i, SPANS as int));
        r
    }
}

/// Joins the uninitialized permissions to records `i` up to SPANS of the metadata page at `m` back
/// into one permission to their bytes.
proof fn gather(tracked recs: Map<int, PointsTo<BlockBuddy>>, m: int, provenance: Provenance, i: int) -> (tracked raw: PointsToRaw)
    requires
        0 <= i <= SPANS,
        0 < m,
        m + PAGE_BYTES <= usize::MAX,
        recs.dom() == Set::range(i, SPANS as int),
        forall|j: int|
            i <= j < SPANS ==> #[trigger] recs[j].ptr() == record_ptr(m, provenance, j)
                && recs[j].is_uninit(),
    ensures
        raw.is_range(m + i * BLOCK_PAGES, (SPANS - i) * BLOCK_PAGES),
        raw.provenance() == provenance,
    decreases SPANS - i,
{
    lemma_layout();
    if i == SPANS {
        let tracked raw = PointsToRaw::empty(provenance);
        assert(raw.dom() =~= Set::range(m + i * BLOCK_PAGES, m + i * BLOCK_PAGES));
        raw
    } else {
        let tracked mut recs = recs;
        let tracked one = recs.tracked_remove(i);
        assert(recs.dom() =~= Set::range(i + 1, SPANS as int));
        assert(one.ptr() == record_ptr(m, provenance, i));
        let tracked first = one.into_raw();
        let tracked rest = gather(recs, m, provenance, i + 1);
        let tracked raw = first.join(rest);
        assert(raw.dom() =~= Set::range(m + i * BLOCK_PAGES, m + i * BLOCK_PAGES + (SPANS - i)
            * BLOCK_PAGES));
        raw
    }
}

/// A block buddy's runs are `used_of` its blocks.
proof fn lemma_used_of(bb: BlockBuddy)
    ensures
        used_of(bb.blocks()) == bb.used(),
{
    assert(used_of(bb.blocks()).dom() =~= bb.used().dom());
    assert(used_of(bb.blocks()) =~= bb.used());
}

/// The pointer to record `i` of the metadata page `m` points to.
fn record(m: *mut u8, i: usize) -> (r: *mut BlockBuddy)
    requires
        i < SPANS,
        m@.addr + PAGE_BYTES <= usize::MAX,
    ensures
        r == record_ptr(m@.addr as int, m@.provenance, i as int),
{
    m.with_addr(m.addr() + i * BLOCK_PAGES) as *mut BlockBuddy
}

/// The page buddy over a span source.
pub struct PageBuddy<S: SpanSource> {
    source: S,
    /// The metadata page, while a span is held.
    meta: Option<*mut u8>,
    /// The base of the span each record cuts, or 0 for a free record.
    bases: [usize; SPANS],
    /// The idle spans kept rather than given back.
    spares: usize,
    /// The held spans with no run allocated.
    idle: usize,
    /// The record of each held span, by base.
    slot: Ghost<Map<int, int>>,
    /// The permission to each record, while a span is held.
    records: Tracked<Map<int, PointsTo<BlockBuddy>>>,
}

impl<S: SpanSource> PageBuddy<S> {
    /// The block buddy record `i` holds.
    spec fn rec(&self, i: int) -> BlockBuddy {
        self.records@[i].value()
    }

    /// The held spans, by base, with the blocks of each.
    pub closed spec fn spans(&self) -> Map<int, Map<int, Block>> {
        spans_of(self.slot@, self.records@)
    }

    /// The allocated runs of each held span, by head, with their orders.
    pub closed spec fn used(&self) -> Map<int, Map<int, nat>> {
        used_in(self.slot@, self.records@)
    }

    /// The source's view.
    pub closed spec fn source(&self) -> SourceView {
        self.source@
    }

    /// The idle spans the page buddy keeps rather than gives back.
    pub closed spec fn spares(&self) -> nat {
        self.spares as nat
    }

    /// The base of the metadata span, while one is held.
    pub closed spec fn meta(&self) -> Option<int> {
        match self.meta {
            Some(m) => Some(m@.addr as int),
            None => None,
        }
    }

    /// The held spans with no run allocated.
    pub open spec fn idle_spans(&self) -> Set<int> {
        idle_of(self.used())
    }

    /// Some held span has a free block of order `k` or more.
    pub open spec fn fits(&self, k: nat) -> bool {
        exists|b: int, h: int|
            #![trigger self.spans()[b].contains_key(h)]
            self.spans().contains_key(b) && self.spans()[b].contains_key(h) && self.spans()[b][h].free
                && self.spans()[b][h].order >= k
    }

    /// `p` is the head of an allocated run.
    pub open spec fn holds(&self, p: int) -> bool {
        &&& p % PAGE_BYTES as int == 0
        &&& self.used().contains_key(span_of(p))
        &&& self.used()[span_of(p)].contains_key(page_of(p))
    }

    /// The metadata page at `m` is backed in a span of its own, and each record is the block buddy
    /// of the held span its base names, or uninitialized when it names none.
    spec fn meta_wf(&self, m: *mut u8) -> bool {
        let src = self.source@;
        let ma = m@.addr as int;
        &&& m@.provenance == src.provenance
        &&& src.spans.contains_key(ma)
        &&& src.spans[ma] == (Span { blocks: 1, backed: run_pages(ma, 1) })
        &&& !self.slot@.contains_key(ma)
        &&& forall|i: int| 0 <= i < SPANS ==> #[trigger] self.records@.contains_key(i)
        &&& forall|i: int|
            #![trigger self.records@[i]]
            0 <= i < SPANS ==> {
                &&& self.records@[i].ptr() == record_ptr(ma, src.provenance, i)
                &&& (self.bases@[i] == 0) == self.records@[i].is_uninit()
            }
        &&& forall|i: int|
            #![trigger self.bases@[i]]
            0 <= i < SPANS && self.bases@[i] != 0 ==> {
                &&& self.records@[i].is_init()
                &&& self.rec(i).wf()
                &&& held(src, self.bases@[i] as int, self.rec(i).used())
            }
    }

    /// The table of records and bases agrees with itself, with the source and with the count of
    /// idle spans.
    spec fn table_wf(&self) -> bool {
        &&& self.source@.wf()
        &&& self.idle <= self.spares
        &&& self.idle as int == self.idle_spans().len()
        &&& forall|b: int|
            #[trigger] self.slot@.contains_key(b) ==> {
                &&& 0 <= self.slot@[b] < SPANS
                &&& self.bases@[self.slot@[b]] as int == b
                &&& b != 0
            }
        &&& forall|i: int|
            #![trigger self.bases@[i]]
            0 <= i < SPANS && self.bases@[i] != 0 ==> {
                &&& self.slot@.contains_key(self.bases@[i] as int)
                &&& self.slot@[self.bases@[i] as int] == i
            }
        &&& match self.meta {
            None => forall|i: int| 0 <= i < SPANS ==> #[trigger] self.bases@[i] == 0,
            Some(m) => self.meta_wf(m),
        }
    }

    /// The table is well formed, and the metadata span is held exactly when a run span is.
    pub closed spec fn wf(&self) -> bool {
        &&& self.table_wf()
        &&& (self.meta is None) == (self.slot@.dom() == Set::<int>::empty())
    }

    /// The invariant on the view: every held span is a reserved span of one block whose backed
    /// pages lie in its allocated runs, apart from the metadata span, its blocks partitioned and coalesced; the metadata
    /// span is held, its first page backed, exactly when a run span is; and no more idle spans are
    /// held than the spares.
    pub proof fn lemma_view(&self)
        requires
            self.wf(),
        ensures
            self.source().wf(),
            self.idle_spans().len() <= self.spares(),
            self.used().dom() == self.spans().dom(),
            (self.meta() is None) == (self.spans().dom() == Set::<int>::empty()),
            forall|b: int|
                #[trigger] self.spans().contains_key(b) ==> {
                    &&& partitioned(self.spans()[b])
                    &&& coalesced(self.spans()[b])
                    &&& self.used()[b] == used_of(self.spans()[b])
                    &&& self.used()[b].dom() == Set::<int>::empty() ==> self.spans()[b] == initial()
                    &&& b > 0
                    &&& b % BLOCK_BYTES as int == 0
                    &&& held(self.source(), b, self.used()[b])
                    &&& self.meta() != Some(b)
                },
            match self.meta() {
                Some(m) => {
                    &&& self.source().spans.contains_key(m)
                    &&& self.source().spans[m] == (Span { blocks: 1, backed: run_pages(m, 1) })
                },
                None => true,
            },
    {
        assert(self.used().dom() =~= self.spans().dom());
        assert forall|b: int| #[trigger] self.spans().contains_key(b) implies {
            &&& partitioned(self.spans()[b])
            &&& coalesced(self.spans()[b])
            &&& self.used()[b] == used_of(self.spans()[b])
            &&& self.used()[b].dom() == Set::<int>::empty() ==> self.spans()[b] == initial()
            &&& b > 0
            &&& b % BLOCK_BYTES as int == 0
            &&& held(self.source(), b, self.used()[b])
            &&& self.meta() != Some(b)
        } by {
            let i = self.slot@[b];
            assert(self.bases@[i] as int == b);
            let m = self.meta->Some_0;
            assert(self.meta_wf(m));
            self.rec(i).lemma_view();
            lemma_used_of(self.rec(i));
            if self.used()[b].dom() == Set::<int>::empty() {
                self.rec(i).lemma_idle();
            }
            assert(self.source@.released_span(b).fits(b, self.source@.spans[b].blocks));
        }
    }

    /// A held span with no run allocated is one free block of order BLOCK_ORDER, so a run of any
    /// order fits while it is held.
    pub proof fn lemma_idle_fits(&self, b: int, k: nat)
        requires
            self.wf(),
            self.spans().contains_key(b),
            self.used()[b].dom() == Set::<int>::empty(),
            k <= BLOCK_ORDER,
        ensures
            self.fits(k),
    {
        self.lemma_view();
        assert(self.spans()[b] == initial());
        assert(self.spans()[b].contains_key(0));
    }

    /// A page buddy holding no span, over `source`, keeping `spares` idle spans.
    pub fn new(source: S, spares: usize) -> (r: Self)
        requires
            source@.wf(),
        ensures
            r.wf(),
            r.source() == source@,
            r.spares() == spares,
            r.meta() is None,
            r.spans() == Map::<int, Map<int, Block>>::empty(),
            r.used() == Map::<int, Map<int, nat>>::empty(),
    {
        let r = PageBuddy {
            source,
            meta: None,
            bases: [0;SPANS],
            spares,
            idle: 0,
            slot: Ghost(Map::empty()),
            records: Tracked(Map::tracked_empty()),
        };
        assert(r.spans() =~= Map::<int, Map<int, Block>>::empty());
        assert(r.used() =~= Map::<int, Map<int, nat>>::empty());
        assert(r.idle_spans() =~= Set::<int>::empty());
        r
    }

    /// A record no span holds; or none when every record holds one, which is when SPANS spans are
    /// held.
    fn free_slot(&self) -> (r: Option<usize>)
        requires
            self.table_wf(),
        ensures
            match r {
                None => self.slot@.dom().len() == SPANS,
                Some(i) => {
                    &&& i < SPANS
                    &&& self.bases@[i as int] == 0
                    &&& self.slot@.dom().len() < SPANS
                },
            },
    {
        let mut free: Option<usize> = None;
        let mut i: usize = 0;
        let ghost mut seen = Set::<int>::empty();
        let ghost mut zeros: int = 0;
        while i < SPANS
            invariant
                self.table_wf(),
                i <= SPANS,
                seen.len() + zeros == i,
                forall|b: int| seen.contains(b) <==> self.slot@.contains_key(b) && self.slot@[b] < i,
                match free {
                    None => zeros == 0,
                    Some(j) => j < SPANS && self.bases@[j as int] == 0 && zeros >= 1,
                },
            decreases SPANS - i,
        {
            if self.bases[i] == 0 {
                if free.is_none() {
                    free = Some(i);
                }
                proof {
                    zeros = zeros + 1;
                    assert forall|b: int| seen.contains(b) <==> self.slot@.contains_key(b) && self.slot@[b] < i + 1 by {
                        if self.slot@.contains_key(b) && self.slot@[b] == i {
                            assert(self.bases@[self.slot@[b]] as int == b);
                        }
                    }
                }
            } else {
                proof {
                    let b = self.bases@[i as int] as int;
                    assert(self.slot@.contains_key(b) && self.slot@[b] == i);
                    assert(!seen.contains(b));
                    seen = seen.insert(b);
                    assert forall|c: int| seen.contains(c) <==> self.slot@.contains_key(c) && self.slot@[c] < i + 1 by {
                        if self.slot@.contains_key(c) && self.slot@[c] == i {
                            assert(self.bases@[self.slot@[c]] as int == c);
                        }
                    }
                }
            }
            i = i + 1;
        }
        proof {
            assert(seen =~= self.slot@.dom());
        }
        free
    }

    /// The record of the held span at `b`.
    fn find(&self, b: usize) -> (i: usize)
        requires
            self.table_wf(),
            self.slot@.contains_key(b as int),
        ensures
            i < SPANS,
            self.bases@[i as int] == b,
            self.slot@[b as int] == i,
    {
        let mut i: usize = 0;
        while i < SPANS
            invariant
                self.table_wf(),
                self.slot@.contains_key(b as int),
                i <= SPANS,
                forall|j: int| 0 <= j < i ==> self.bases@[j] != b,
            decreases SPANS - i,
        {
            if self.bases[i] == b {
                return i;
            }
            i = i + 1;
        }
        proof {
            let j = self.slot@[b as int];
            assert(self.bases@[j] as int == b);
        }
        0
    }

    /// Whether no run span is held.
    fn none_held(&self) -> (r: bool)
        requires
            self.table_wf(),
        ensures
            r == (self.slot@.dom() == Set::<int>::empty()),
    {
        let mut i: usize = 0;
        while i < SPANS
            invariant
                self.table_wf(),
                i <= SPANS,
                forall|j: int| 0 <= j < i ==> self.bases@[j] == 0,
            decreases SPANS - i,
        {
            if self.bases[i] != 0 {
                proof {
                    assert(self.slot@.dom().contains(self.bases@[i as int] as int));
                }
                return false;
            }
            i = i + 1;
        }
        proof {
            assert forall|b: int| !self.slot@.dom().contains(b) by {
                if self.slot@.contains_key(b) {
                    let j = self.slot@[b];
                    assert(self.bases@[j] as int == b);
                }
            }
            assert(self.slot@.dom() =~= Set::<int>::empty());
        }
        true
    }

    /// The record holding a free block of the smallest order at or above `k` across every held span,
    /// with that order; or none when no held span has a free block of order `k` or more.
    fn best_span(&self, k: usize) -> (r: Option<(usize, usize)>)
        requires
            self.wf(),
            k <= BLOCK_ORDER,
        ensures
            match r {
                None => !self.fits(k as nat),
                Some((i, o)) => {
                    &&& i < SPANS
                    &&& self.bases@[i as int] != 0
                    &&& k <= o <= BLOCK_ORDER
                    &&& self.rec(i as int).fits(k as nat)
                    &&& exists|h: int|
                        #[trigger] self.rec(i as int).blocks().contains_key(h)
                            && self.rec(i as int).blocks()[h] == (Block { order: o as nat, free: true })
                    &&& forall|b: int, q: int|
                        #![trigger self.spans()[b].contains_key(q)]
                        self.spans().contains_key(b) && self.spans()[b].contains_key(q)
                            && self.spans()[b][q].free && self.spans()[b][q].order >= k
                            ==> self.spans()[b][q].order >= o
                },
            },
    {
        let mut best: Option<(usize, usize)> = None;
        let mut i: usize = 0;
        while i < SPANS
            invariant
                self.wf(),
                k <= BLOCK_ORDER,
                i <= SPANS,
                match best {
                    None => forall|j: int|
                        #![trigger self.bases@[j]]
                        0 <= j < i && self.bases@[j] != 0 ==> !self.rec(j).fits(k as nat),
                    Some((j, o)) => {
                        &&& j < i
                        &&& self.bases@[j as int] != 0
                        &&& k <= o <= BLOCK_ORDER
                        &&& exists|h: int|
                            #[trigger] self.rec(j as int).blocks().contains_key(h)
                                && self.rec(j as int).blocks()[h] == (Block { order: o as nat, free: true })
                        &&& forall|j2: int, q: int|
                            #![trigger self.rec(j2).blocks().contains_key(q)]
                            0 <= j2 < i && self.bases@[j2] != 0 && self.rec(j2).blocks().contains_key(q)
                                && self.rec(j2).blocks()[q].free && self.rec(j2).blocks()[q].order >= k
                                ==> self.rec(j2).blocks()[q].order >= o
                    },
                },
            decreases SPANS - i,
        {
            if self.bases[i] != 0 {
                let m = self.meta.unwrap();
                proof {
                    assert(self.meta_wf(m));
                    assert(self.source@.released_span(m@.addr as int).fits(m@.addr as int, 1));
                }
                let ptr = record(m, i);
                let tracked perm = self.records.borrow().tracked_borrow(i as int);
                let bb = ptr_ref(ptr, Tracked(perm));
                let ghost before = best;
                proof {
                    assert(*bb == self.rec(i as int));
                }
                match bb.fit_order(k) {
                    None => {},
                    Some(o) => {
                        let better = match best {
                            None => true,
                            Some((_, bo)) => o < bo,
                        };
                        if better {
                            best = Some((i, o));
                        }
                        proof {
                            let bo = best->Some_0.1;
                            assert forall|j2: int, q: int|
                                #![trigger self.rec(j2).blocks().contains_key(q)]
                                0 <= j2 < i + 1 && self.bases@[j2] != 0 && self.rec(j2).blocks().contains_key(q)
                                    && self.rec(j2).blocks()[q].free && self.rec(j2).blocks()[q].order >= k
                                    implies self.rec(j2).blocks()[q].order >= bo by {
                                if j2 == i {
                                    assert(bb.blocks().contains_key(q));
                                } else if before is None {
                                    assert(self.rec(j2).fits(k as nat));
                                }
                            }
                        }
                    },
                }
            }
            i = i + 1;
        }
        proof {
            match best {
                None => {
                    if self.fits(k as nat) {
                        let (b, h) = choose|b: int, h: int|
                            #![trigger self.spans()[b].contains_key(h)]
                            self.spans().contains_key(b) && self.spans()[b].contains_key(h)
                                && self.spans()[b][h].free && self.spans()[b][h].order >= k;
                        let j = self.slot@[b];
                        assert(self.bases@[j] as int == b);
                        assert(self.spans()[b] == self.rec(j).blocks());
                        assert(self.rec(j).blocks().contains_key(h));
                    }
                },
                Some((j, o)) => {
                    let h = choose|h: int|
                        #[trigger] self.rec(j as int).blocks().contains_key(h)
                            && self.rec(j as int).blocks()[h] == (Block { order: o as nat, free: true });
                    assert(self.rec(j as int).blocks().contains_key(h));
                    assert forall|b: int, q: int|
                        #![trigger self.spans()[b].contains_key(q)]
                        self.spans().contains_key(b) && self.spans()[b].contains_key(q)
                            && self.spans()[b][q].free && self.spans()[b][q].order >= k
                            implies self.spans()[b][q].order >= o by {
                        let j2 = self.slot@[b];
                        assert(self.bases@[j2] as int == b);
                        assert(self.spans()[b] == self.rec(j2).blocks());
                        assert(self.rec(j2).blocks().contains_key(q));
                    }
                },
            }
        }
        best
    }

    /// Cuts a run of order `k` in the held span of record `i`, from its free block of the smallest
    /// order at or above `k`.
    fn alloc_in(&mut self, i: usize, k: usize) -> (p: usize)
        requires
            old(self).wf(),
            k <= BLOCK_ORDER,
            i < SPANS,
            old(self).bases@[i as int] != 0,
            old(self).rec(i as int).fits(k as nat),
        ensures
            final(self).wf(),
            final(self).spares() == old(self).spares(),
            final(self).spans().dom() == old(self).spans().dom(),
            final(self).source() == old(self).source(),
            final(self).meta() == old(self).meta(),
            span_of(p as int) == old(self).bases@[i as int],
            cut(old(self).used(), final(self).used(), p as int, k as nat),
            final(self).source().unbacked(span_of(p as int), p as int, pages(k as nat) as nat),
            ({
                let s = old(self).spans()[span_of(p as int)];
                let h = page_of(p as int);
                &&& s.contains_key(h)
                &&& s[h].free
                &&& s[h].order >= k
                &&& forall|q: int|
                    #[trigger] s.contains_key(q) && s[q].free && s[q].order >= k ==> s[q].order
                        >= s[h].order
            }),
    {
        let ghost old_used = self.used();
        let ghost old_spans = self.spans();
        let ghost old_idle = self.idle_spans();
        let m = self.meta.unwrap();
        proof {
            assert(self.meta_wf(m));
            assert(self.source@.released_span(m@.addr as int).fits(m@.addr as int, 1));
        }
        let b = self.bases[i];
        let ghost bi = b as int;
        proof {
            assert(held(self.source@, bi, self.rec(i as int).used()));
            assert(self.source@.released_span(bi).fits(bi, 1));
            assert(self.slot@[bi] == i);
        }
        let ghost u0 = self.rec(i as int).used();
        let ptr = record(m, i);
        let tracked mut perm = self.records.borrow_mut().tracked_remove(i as int);
        let mut bb = ptr_mut_read(ptr, Tracked(&mut perm));
        let ghost bb0 = bb;
        let was_idle = bb.is_idle();
        let h = bb.alloc(k).unwrap();
        ptr_mut_write(ptr, Tracked(&mut perm), bb);
        proof {
            self.records.borrow_mut().tracked_insert(i as int, perm);
        }
        proof {
            assert forall|c: int| #[trigger] self.slot@.contains_key(c) && c != bi implies self.slot@[c] != i as int by {
                assert(self.bases@[self.slot@[c]] as int == c);
            }
            assert(self.used() =~= old_used.insert(bi, bb.used()));
            assert(self.spans() =~= old_spans.insert(bi, bb.blocks()));
            assert(bb.used().contains_key(h as int));
            if was_idle {
                assert(self.idle_spans() =~= old_idle.remove(bi));
            } else {
                assert(self.idle_spans() =~= old_idle);
            }
        }
        if was_idle {
            self.idle = self.idle - 1;
        }
        proof {
            lemma_pages_pos(k as nat);
            lemma_address(bi, h as int);
            bb0.lemma_view();
            let u = old_used[bi];
            assert(u == bb0.used());
            assert forall|q: int| #[trigger] u.contains_key(q) implies h + pages(k as nat) <= q || q
                + pages(u[q]) <= h by {
                assert(bb0.blocks().contains_key(q) && !bb0.blocks()[q].free);
                assert(q != h);
                lemma_pages(k as nat, bb0.blocks()[h as int].order);
            }
            assert(old_used.contains_key(bi));
            assert(self.used() == old_used.insert(bi, u.insert(h as int, k as nat)));
            assert forall|i2: int|
                #![trigger self.bases@[i2]]
                0 <= i2 < SPANS && self.bases@[i2] != 0 implies held(self.source@, self.bases@[i2] as int, self.rec(i2).used()) by {
                if i2 == i {
                    assert forall|a: int| #[trigger] self.source@.spans[bi].backed.contains(a) implies in_runs(bi, bb.used(), a) by {
                        let q = choose|q: int| #[trigger] u0.contains_key(q) && run_pages(bi + q * PAGE_BYTES as int, pages(u0[q]) as nat).contains(a);
                        assert(bb.used().contains_key(q) && bb.used()[q] == u0[q]);
                    }
                }
            }
            let run = run_pages(bi + h * PAGE_BYTES as int, pages(k as nat) as nat);
            assert forall|a: int| #[trigger] self.source@.spans[bi].backed.contains(a) implies !run.contains(a) by {
                let q = choose|q: int| #[trigger] u0.contains_key(q) && run_pages(bi + q * PAGE_BYTES as int, pages(u0[q]) as nat).contains(a);
                lemma_pages_pos(u0[q]);
                lemma_runs_apart(bi, h as int, pages(k as nat), q, pages(u0[q]));
            }
        }
        b + h * PAGE_BYTES
    }

    /// Makes sure the metadata span is held: reserves it and backs its first page when no span is
    /// held. Returns whether it did, or none when the source refused.
    fn ensure_meta(&mut self) -> (r: Option<bool>)
        requires
            old(self).wf(),
        ensures
            final(self).table_wf(),
            final(self).slot == old(self).slot,
            final(self).bases == old(self).bases,
            final(self).spares == old(self).spares,
            final(self).idle == old(self).idle,
            final(self).spans() == old(self).spans(),
            final(self).used() == old(self).used(),
            match r {
                None => {
                    &&& final(self).source() == old(self).source().refused()
                    &&& final(self).meta is None
                    &&& old(self).meta is None
                },
                Some(fresh) => {
                    &&& final(self).meta is Some
                    &&& fresh == (old(self).meta is None)
                    &&& !fresh ==> *final(self) == *old(self)
                    &&& fresh ==> {
                        let ma = final(self).meta->Some_0@.addr as int;
                        &&& old(self).slot@.dom() == Set::<int>::empty()
                        &&& !old(self).source().spans.contains_key(ma)
                        &&& final(self).source() == old(self).source().reserved(ma, 1).backed_run(ma, ma, 1)
                    }
                },
            },
    {
        if self.meta.is_some() {
            return Some(false);
        }
        let ghost start = self.source@;
        let ghost old_spans = self.spans();
        let ghost old_used = self.used();
        let base = match self.source.reserve(1) {
            None => return None,
            Some(base) => base,
        };
        let ma = base.addr();
        proof {
            lemma_address(ma as int, 0);
            assert(!start.spans.contains_key(ma as int)) by {
                if start.spans.contains_key(ma as int) {
                    assert(start.apart(ma as int, 1, ma as int));
                }
            }
        }
        let perm = match self.source.back(Ghost(ma as int), ma, 1) {
            None => {
                self.source.release_span(ma);
                proof {
                    assert(self.source@.spans =~= start.spans);
                    assert(self.source@ == start.refused());
                }
                return None;
            },
            Some(perm) => perm,
        };
        proof {
            lemma_layout();
        }
        let tracked raw = perm.get();
        let tracked recs = carve(raw, ma as int, 0);
        self.records = Tracked(recs);
        self.meta = Some(base);
        proof {
            assert(self.slot@.dom() =~= Set::<int>::empty());
            assert(self.spans() =~= old_spans);
            assert(self.used() =~= old_used);
            let s = self.source@;
            assert(s.spans[ma as int].backed =~= run_pages(ma as int, 1));
            assert(self.meta_wf(base));
        }
        Some(true)
    }

    /// Gives back the metadata span, when no run span is held.
    fn drop_meta(&mut self)
        requires
            old(self).table_wf(),
            old(self).meta is Some,
            old(self).slot@.dom() == Set::<int>::empty(),
        ensures
            final(self).wf(),
            final(self).meta is None,
            final(self).slot == old(self).slot,
            final(self).bases == old(self).bases,
            final(self).spares == old(self).spares,
            final(self).idle == old(self).idle,
            final(self).spans() == old(self).spans(),
            final(self).used() == old(self).used(),
            ({
                let ma = old(self).meta->Some_0@.addr as int;
                final(self).source() == old(self).source().released_run(ma, ma, 1).released_span(ma)
            }),
    {
        let ghost old_spans = self.spans();
        let ghost old_used = self.used();
        let m = self.meta.unwrap();
        let ma = m.addr();
        let ghost prov = m@.provenance;
        proof {
            assert(self.meta_wf(m));
            assert(self.source@.released_span(ma as int).fits(ma as int, 1));
            lemma_address(ma as int, 0);
            lemma_layout();
            assert forall|i: int| 0 <= i < SPANS implies #[trigger] self.bases@[i] == 0 by {
                if self.bases@[i] != 0 {
                    assert(self.slot@.contains_key(self.bases@[i] as int));
                }
            }
        }
        let tracked all = self.records.borrow_mut().tracked_remove_keys(Set::range(0, SPANS as int));
        proof {
            assert(all.dom() =~= Set::range(0, SPANS as int));
            assert(forall|j: int| 0 <= j < SPANS ==> #[trigger] all[j] == old(self).records@[j]);
        }
        let tracked raw = gather(all, ma as int, prov, 0);
        self.source.release(Ghost(ma as int), ma, 1, Tracked(raw));
        proof {
            assert(self.source@.spans[ma as int].backed =~= Set::<int>::empty());
        }
        self.source.release_span(ma);
        self.meta = None;
        proof {
            assert(self.spans() =~= old_spans);
            assert(self.used() =~= old_used);
        }
    }

    /// Cuts a run of order `k` from a new span, when no held span has a free block of order `k` or
    /// more.
    fn alloc_new(&mut self, k: usize) -> (r: Result<usize, Refused>)
        requires
            old(self).wf(),
            k <= BLOCK_ORDER,
            !old(self).fits(k as nat),
        ensures
            final(self).wf(),
            final(self).spares() == old(self).spares(),
            match r {
                Err(Refused::Full) => {
                    &&& final(self).spans() == old(self).spans()
                    &&& final(self).used() == old(self).used()
                    &&& final(self).source() == old(self).source()
                    &&& final(self).meta() == old(self).meta()
                    &&& old(self).spans().dom().len() == SPANS
                },
                Err(Refused::Source) => {
                    &&& final(self).spans() == old(self).spans()
                    &&& final(self).used() == old(self).used()
                    &&& final(self).source() == old(self).source().refused()
                    &&& final(self).meta() == old(self).meta()
                    &&& old(self).spans().dom().len() < SPANS
                },
                Ok(p) => {
                    &&& !old(self).spans().contains_key(span_of(p as int))
                    &&& old(self).spans().dom().len() < SPANS
                    &&& final(self).spans().dom() == old(self).spans().dom().insert(span_of(p as int))
                    &&& cut(old(self).used(), final(self).used(), p as int, k as nat)
                    &&& final(self).source().unbacked(span_of(p as int), p as int, pages(k as nat) as nat)
                    &&& took_span(old(self).source(), old(self).meta(), final(self).source(), final(self).meta(), span_of(p as int))
                },
            },
    {
        let ghost old_used = self.used();
        let ghost old_spans = self.spans();
        let ghost old_idle = self.idle_spans();
        let ghost start = self.source@;
        assert(old_spans.dom() == self.slot@.dom());
        let i = match self.free_slot() {
            None => return Err(Refused::Full),
            Some(i) => i,
        };
        let fresh = match self.ensure_meta() {
            None => return Err(Refused::Source),
            Some(fresh) => fresh,
        };
        let ghost before = self.source@;
        let base = match self.source.reserve(1) {
            None => {
                if fresh {
                    self.drop_meta();
                    proof {
                        assert(self.source@.spans =~= start.spans);
                        assert(self.source@ == start.refused());
                    }
                }
                return Err(Refused::Source);
            },
            Some(base) => base,
        };
        let b = base.addr();
        let m = self.meta.unwrap();
        proof {
            assert(self.meta_wf(m));
            assert(self.source@.released_span(m@.addr as int).fits(m@.addr as int, 1));
            assert(!before.spans.contains_key(b as int)) by {
                if before.spans.contains_key(b as int) {
                    assert(before.apart(b as int, 1, b as int));
                }
            }
            assert(!self.slot@.contains_key(b as int)) by {
                if self.slot@.contains_key(b as int) {
                    let j = self.slot@[b as int];
                    assert(self.bases@[j] as int == b as int);
                }
            }
        }
        let mut bb = BlockBuddy::new();
        proof {
            lemma_block_pages();
            assert(bb.blocks().contains_key(0) && bb.blocks()[0].free);
        }
        let ghost fresh_used = bb.used();
        assert(fresh_used =~= Map::<int, nat>::empty());
        let h = bb.alloc(k).unwrap();
        let ptr = record(m, i);
        let tracked mut perm = self.records.borrow_mut().tracked_remove(i as int);
        ptr_mut_write(ptr, Tracked(&mut perm), bb);
        proof {
            self.records.borrow_mut().tracked_insert(i as int, perm);
        }
        self.bases[i] = b;
        self.slot = Ghost(self.slot@.insert(b as int, i as int));
        proof {
            let bi = b as int;
            lemma_address(bi, h as int);
            assert forall|c: int| #[trigger] self.slot@.contains_key(c) && c != bi implies self.slot@[c] != i as int by {
                assert(self.bases@[self.slot@[c]] as int == c);
            }
            assert(self.used() =~= old_used.insert(bi, bb.used()));
            assert(self.spans().dom() =~= old_spans.dom().insert(bi));
            assert(self.idle_spans() =~= old_idle);
            assert(self.meta_wf(m));
            assert(self.slot@.dom().contains(bi));
        }
        Ok(b + h * PAGE_BYTES)
    }

    /// Cuts a run of order `k`: from the held span with a free block of the smallest order at or
    /// above `k`, or from a new span when none has one. Refuses, and changes no held span, when no
    /// held span has one and SPANS spans are held (`Full`) or the source refused in this call, which
    /// its view counts (`Source`).
    pub fn alloc_run(&mut self, k: usize) -> (r: Result<usize, Refused>)
        requires
            old(self).wf(),
            k <= BLOCK_ORDER,
        ensures
            final(self).wf(),
            final(self).spares() == old(self).spares(),
            match r {
                Err(Refused::Full) => {
                    &&& !old(self).fits(k as nat)
                    &&& old(self).spans().dom().len() == SPANS
                    &&& final(self).spans() == old(self).spans()
                    &&& final(self).used() == old(self).used()
                    &&& final(self).source() == old(self).source()
                    &&& final(self).meta() == old(self).meta()
                },
                Err(Refused::Source) => {
                    &&& !old(self).fits(k as nat)
                    &&& old(self).spans().dom().len() < SPANS
                    &&& final(self).spans() == old(self).spans()
                    &&& final(self).used() == old(self).used()
                    &&& final(self).source() == old(self).source().refused()
                    &&& final(self).meta() == old(self).meta()
                },
                Ok(p) => {
                    &&& cut(old(self).used(), final(self).used(), p as int, k as nat)
                    &&& final(self).source().unbacked(span_of(p as int), p as int, pages(k as nat) as nat)
                    &&& old(self).fits(k as nat) || old(self).spans().dom().len() < SPANS
                    &&& if old(self).spans().contains_key(span_of(p as int)) {
                        &&& best(old(self).spans(), span_of(p as int), page_of(p as int), k as nat)
                        &&& final(self).source() == old(self).source()
                        &&& final(self).meta() == old(self).meta()
                    } else {
                        &&& !old(self).fits(k as nat)
                        &&& took_span(old(self).source(), old(self).meta(), final(self).source(), final(self).meta(), span_of(p as int))
                    }
                },
            },
    {
        let ghost old_spans = self.spans();
        match self.best_span(k) {
            Some((i, o)) => {
                proof {
                    let b = self.bases@[i as int] as int;
                    assert(self.slot@[b] == i as int);
                    assert(old_spans.contains_key(b));
                    assert(old_spans[b] == self.rec(i as int).blocks());
                }
                let p = self.alloc_in(i, k);
                proof {
                    let b = span_of(p as int);
                    let h = page_of(p as int);
                    let s = old_spans[b];
                    assert(old_spans.contains_key(b));
                    let h0 = choose|h0: int|
                        #[trigger] old(self).rec(i as int).blocks().contains_key(h0)
                            && old(self).rec(i as int).blocks()[h0] == (Block { order: o as nat, free: true });
                    assert(s.contains_key(h0));
                    assert(s[h].order <= o);
                    assert(s.contains_key(h) && s[h].free && s[h].order >= k);
                    assert(old(self).fits(k as nat)) by {
                        assert(old_spans[b].contains_key(h));
                    }
                }
                Ok(p)
            },
            None => self.alloc_new(k),
        }
    }

    /// Takes back the run at `p`, none of whose pages is backed. A span left with no run is given
    /// back to the source, unless fewer than the spares are idle, when it stays as a spare.
    pub fn free_run(&mut self, p: usize)
        requires
            old(self).wf(),
            old(self).holds(p as int),
            old(self).source().unbacked(
                span_of(p as int),
                p as int,
                pages(old(self).used()[span_of(p as int)][page_of(p as int)]) as nat,
            ),
        ensures
            final(self).wf(),
            final(self).spares() == old(self).spares(),
            ({
                let b = span_of(p as int);
                let u = old(self).used()[b].remove(page_of(p as int));
                if u.dom() != Set::<int>::empty() || old(self).idle_spans().len() < old(self).spares() {
                    &&& final(self).used() == old(self).used().insert(b, u)
                    &&& final(self).source() == old(self).source()
                    &&& final(self).meta() == old(self).meta()
                } else {
                    &&& final(self).used() == old(self).used().remove(b)
                    &&& gave_span(old(self).source(), old(self).meta(), final(self).source(), final(self).meta(), b, old(self).used().remove(b).dom() == Set::<int>::empty())
                }
            }),
    {
        let ghost old_used = self.used();
        let ghost old_idle = self.idle_spans();
        let b = p - p % BLOCK_BYTES;
        let h = (p % BLOCK_BYTES) / PAGE_BYTES;
        let ghost bi = b as int;
        let i = self.find(b);
        let m = self.meta.unwrap();
        proof {
            assert(self.meta_wf(m));
            assert(self.source@.released_span(m@.addr as int).fits(m@.addr as int, 1));
            assert(held(self.source@, bi, self.rec(i as int).used()));
        }
        let ptr = record(m, i);
        let tracked mut perm = self.records.borrow_mut().tracked_remove(i as int);
        let mut bb = ptr_mut_read(ptr, Tracked(&mut perm));
        proof {
            assert(old_used[bi] == bb.used());
        }
        bb.free(h);
        let idle = bb.is_idle();
        proof {
            assert forall|c: int| #[trigger] self.slot@.contains_key(c) && c != bi implies self.slot@[c] != i as int by {
                assert(self.bases@[self.slot@[c]] as int == c);
            }
            assert(!old_idle.contains(bi));
        }
        if idle && self.idle >= self.spares {
            proof {
                self.records.borrow_mut().tracked_insert(i as int, perm);
            }
            self.source.release_span(b);
            self.bases[i] = 0;
            self.slot = Ghost(self.slot@.remove(bi));
            proof {
                assert(self.used() =~= old_used.remove(bi));
                assert(self.idle_spans() =~= old_idle);
                assert(bb.used().dom() =~= Set::<int>::empty());
                let ma = m@.addr as int;
                assert(ma != bi);
                assert forall|i2: int|
                    #![trigger self.bases@[i2]]
                    0 <= i2 < SPANS && self.bases@[i2] != 0 implies held(self.source@, self.bases@[i2] as int, self.rec(i2).used()) by {
                    assert(self.bases@[i2] as int != bi);
                }
                assert(self.meta_wf(m));
            }
            if self.none_held() {
                self.drop_meta();
            }
        } else {
            ptr_mut_write(ptr, Tracked(&mut perm), bb);
            proof {
                self.records.borrow_mut().tracked_insert(i as int, perm);
                assert(self.used() =~= old_used.insert(bi, bb.used()));
                if idle {
                    assert(self.idle_spans() =~= old_idle.insert(bi));
                } else {
                    assert(self.idle_spans() =~= old_idle);
                }
            }
            if idle {
                self.idle = self.idle + 1;
            }
        }
    }

    /// The allocated run of order `k` at `p` lies in its span, a held span other than the metadata
    /// span, with `p` its page `page_of(p)`.
    proof fn lemma_run(&self, p: int, k: nat)
        requires
            self.wf(),
            self.holds(p),
            self.used()[span_of(p)][page_of(p)] == k,
        ensures
            k <= BLOCK_ORDER,
            self.meta is Some,
            self.slot@.contains_key(span_of(p)),
            span_of(p) != self.meta->Some_0@.addr,
            self.meta_wf(self.meta->Some_0),
            p == span_of(p) + page_of(p) * PAGE_BYTES,
            self.source@.runs_in(span_of(p), p, pages(k) as nat),
            self.rec(self.slot@[span_of(p)]).used() == self.used()[span_of(p)],
            self.bases@[self.slot@[span_of(p)]] as int == span_of(p),
    {
        let b = span_of(p);
        let h = page_of(p);
        let pb = PAGE_BYTES as int;
        assert(self.used().dom() =~= self.slot@.dom());
        let i = self.slot@[b];
        assert(self.bases@[i] as int == b);
        let m = self.meta->Some_0;
        assert(self.meta_wf(m));
        let r = self.rec(i);
        r.lemma_view();
        lemma_used_of(r);
        assert(r.blocks().contains_key(h) && !r.blocks()[h].free && r.blocks()[h].order == k);
        assert(placed(h, r.blocks()[h]));
        lemma_pages_pos(k);
        lemma_head(p);
        assert(held(self.source@, b, self.rec(i).used()));
        assert(p + pages(k) * pb <= b + BLOCK_BYTES as int) by (nonlinear_arith)
            requires
                p == b + h * pb,
                h + pages(k) <= BLOCK_PAGES as int,
                BLOCK_BYTES as int == pb * BLOCK_PAGES as int,
                pb > 0,
        ;
    }

    /// Backs the pages of the allocated run of order `k` at `p`, none of them backed, through the
    /// source, and returns a pointer to the run with the permission to exactly its bytes; or
    /// refuses, backs nothing and changes nothing.
    pub fn back_run(&mut self, p: usize, k: usize) -> (r: Option<(*mut u8, Tracked<PointsToRaw>)>)
        requires
            old(self).wf(),
            old(self).holds(p as int),
            old(self).used()[span_of(p as int)][page_of(p as int)] == k,
            old(self).source().unbacked(span_of(p as int), p as int, pages(k as nat) as nat),
        ensures
            final(self).wf(),
            final(self).spares() == old(self).spares(),
            final(self).spans() == old(self).spans(),
            final(self).used() == old(self).used(),
            final(self).meta() == old(self).meta(),
            match r {
                None => {
                    &&& final(self).source() == old(self).source().refused()
                },
                Some((ptr, perm)) => {
                    &&& ptr@.addr == p
                    &&& ptr@.provenance == old(self).source().provenance
                    &&& perm@.is_range(p as int, pages(k as nat) * PAGE_BYTES)
                    &&& perm@.provenance() == old(self).source().provenance
                    &&& final(self).source() == old(self).source().backed_run(
                        span_of(p as int),
                        p as int,
                        pages(k as nat) as nat,
                    )
                },
            },
    {
        let ghost bi = span_of(p as int);
        let ghost run = run_pages(p as int, pages(k as nat) as nat);
        proof {
            self.lemma_run(p as int, k as nat);
        }
        let m = self.meta.unwrap();
        let n = order_pages(k);
        let ghost start = self.source@;
        let perm = match self.source.back(Ghost(bi), p, n) {
            None => return None,
            Some(perm) => perm,
        };
        proof {
            let ma = m@.addr as int;
            assert(self.source@.spans[ma] == start.spans[ma]);
            assert forall|i2: int|
                #![trigger self.bases@[i2]]
                0 <= i2 < SPANS && self.bases@[i2] != 0 implies held(
                self.source@,
                self.bases@[i2] as int,
                self.rec(i2).used(),
            ) by {
                let c = self.bases@[i2] as int;
                assert(held(start, c, self.rec(i2).used()));
                if c == bi {
                    assert(self.slot@[c] == i2);
                    let u = self.rec(i2).used();
                    assert forall|a: int| #[trigger] self.source@.spans[c].backed.contains(a) implies in_runs(c, u, a) by {
                        if run.contains(a) {
                            assert(u.contains_key(page_of(p as int)));
                        }
                    }
                }
            }
            assert(self.meta_wf(m));
        }
        Some((m.with_addr(p), perm))
    }

    /// Gives back through the source the pages of the allocated run of order `k` at `p`, every one
    /// of them backed, taking the permission to its bytes.
    pub fn release_run(&mut self, p: usize, k: usize, perm: Tracked<PointsToRaw>)
        requires
            old(self).wf(),
            old(self).holds(p as int),
            old(self).used()[span_of(p as int)][page_of(p as int)] == k,
            old(self).source().backed(span_of(p as int), p as int, pages(k as nat) as nat),
            perm@.is_range(p as int, pages(k as nat) * PAGE_BYTES),
            perm@.provenance() == old(self).source().provenance,
        ensures
            final(self).wf(),
            final(self).spares() == old(self).spares(),
            final(self).spans() == old(self).spans(),
            final(self).used() == old(self).used(),
            final(self).meta() == old(self).meta(),
            final(self).source() == old(self).source().released_run(
                span_of(p as int),
                p as int,
                pages(k as nat) as nat,
            ),
    {
        let ghost bi = span_of(p as int);
        proof {
            self.lemma_run(p as int, k as nat);
        }
        let m = self.meta.unwrap();
        let n = order_pages(k);
        let ghost start = self.source@;
        self.source.release(Ghost(bi), p, n, perm);
        proof {
            let ma = m@.addr as int;
            assert(self.source@.spans[ma] == start.spans[ma]);
            assert forall|i2: int|
                #![trigger self.bases@[i2]]
                0 <= i2 < SPANS && self.bases@[i2] != 0 implies held(
                self.source@,
                self.bases@[i2] as int,
                self.rec(i2).used(),
            ) by {
                let c = self.bases@[i2] as int;
                assert(held(start, c, self.rec(i2).used()));
                let u = self.rec(i2).used();
                assert forall|a: int| #[trigger] self.source@.spans[c].backed.contains(a) implies in_runs(c, u, a) by {
                    assert(start.spans[c].backed.contains(a));
                }
            }
            assert(self.meta_wf(m));
        }
    }
}

} // verus!
