// SPDX-License-Identifier: MIT
//! The heap: one size class per class over one record store and one page buddy, the buddy-run
//! objects cut from that page buddy, and the large-object map, under one invariant.
//!
//! - `wf(src)` is the invariant over the source's view `src`: the page buddy and the store are well
//!   formed over it, class `i` is the `i`-th size class and well formed over them, no two classes
//!   share a head or a record, so a live slot of one shares no byte with a live slot of another;
//!   each buddy-run object (`parts`) is a run the page buddy holds with only the pages the object
//!   needs backed (`run_part`), no record page and no class's slab run; and the large-object map
//!   is well formed over it, each large object's span one the page buddy does not hold. The page
//!   buddy's callers leave every span it does not hold as it was, and the map leaves every span it
//!   does not hold as it was, so each arm keeps the others' invariant.
//! - `live()` is every class's live slots, every buddy-run object's base and every large object's
//!   base.
//! - `alloc(src, size, align)`, for a layout of at most the page whose alignment divides the page,
//!   takes a slot of `class_for(size, align)`, the first class whose slot holds `size` bytes and is a
//!   multiple of `align`. It refuses exactly as that class's `alloc_small` does: only when none of
//!   its slabs has a free slot and the source refused one request in this call (`slab_refused`).
//!   Otherwise the slot is aligned to `align` and joins the live slots (`slot_alloc`). For a layout
//!   of more than one block whose alignment divides the page, it takes a large object of
//!   `pages_for(size)` pages, a span of its own, and refuses exactly as `alloc_large` does: only
//!   when the source refused the span's reserve or the back of its pages in this call
//!   (`large_refused`), with nothing else changed. Otherwise the object is block-aligned, so aligned
//!   to `align`, and joins the large objects (`large_alloc`). For a layout of more than the page
//!   and at most one block whose alignment divides the page, it cuts a run of the smallest order
//!   holding `pages_for(size)` pages and backs only those pages (`part_alloc`). It refuses exactly
//!   when no held span had a free block of that order and the source refused the span, or the
//!   source refused the back of the pages, when it frees the run again so the page buddy holds the
//!   runs it held and the source's spans are those freeing the run leaves (`part_refused`). Otherwise the object is page-aligned, so aligned to `align`,
//!   and joins the buddy-run objects. Whatever it returns is apart from every live slot, buddy-run
//!   object and large object, and alloc says nothing of its bytes.
//! - `free(src, p, size, align, perm)` takes back what alloc returned at `p` for that layout and
//!   never refuses. A slab left with no live slot is retired, its run released and freed to the
//!   page buddy, which gives back a span left with no run unless it keeps it as a spare
//!   (`emptied_slab`). A buddy-run object's pages are released and its run freed, which gives
//!   back a span left with no run unless the page buddy keeps it as a spare (`part_free`). A large
//!   object's span is given back whole (`large_free`).
use vstd::prelude::*;
use vstd::raw_ptr::*;

use crate::arch::*;
use crate::buddy::*;
use crate::class::*;
use crate::large::*;
use crate::page::*;
use crate::record::*;
use crate::small::*;
use crate::source::*;

verus! {

/// From class `c` up, the first class whose slot holds `size` bytes and is a multiple of `align`, or
/// the last class.
pub open spec fn class_from(size: nat, align: nat, c: nat) -> nat
    decreases CLASSES - c,
{
    if c + 1 >= CLASSES || (size <= class_size(c) && class_size(c) % align == 0) {
        c
    } else {
        class_from(size, align, c + 1)
    }
}

/// The class an object of `size` bytes aligned to `align` is a slot of.
pub open spec fn class_for(size: nat, align: nat) -> nat {
    class_from(size, align, 0)
}

/// A layout a slot holds: at most the page, its alignment dividing the page, so the page's class
/// holds it if no smaller class does.
pub open spec fn small_layout(size: nat, align: nat) -> bool {
    &&& size <= PAGE_BYTES
    &&& 0 < align
    &&& PAGE_BYTES as nat % align == 0
}

/// A layout a large object holds: more than one block's bytes and no more than isize::MAX, its
/// alignment dividing the page, so the object's block-aligned base is aligned to it.
pub open spec fn large_layout(size: nat, align: nat) -> bool {
    &&& BLOCK_BYTES < size <= isize::MAX
    &&& 0 < align
    &&& PAGE_BYTES as nat % align == 0
}

/// A layout a buddy run holds: more than the page and at most one block, its alignment dividing
/// the page, so the run's page-aligned base is aligned to it.
pub open spec fn run_layout(size: nat, align: nat) -> bool {
    &&& PAGE_BYTES < size <= BLOCK_BYTES
    &&& 0 < align
    &&& PAGE_BYTES as nat % align == 0
}

/// From order `k` up, the first order whose run holds `n` pages, or BLOCK_ORDER.
pub open spec fn order_up(n: nat, k: nat) -> nat
    decreases BLOCK_ORDER - k,
{
    if k >= BLOCK_ORDER || n <= pages(k) {
        k
    } else {
        order_up(n, k + 1)
    }
}

/// The smallest order whose run holds `n` pages, `n` at most a block's.
pub open spec fn run_order(n: nat) -> nat {
    order_up(n, 0)
}

/// `after` is `before` with one refusal recorded, of a request `alloc` makes for a buddy-run object
/// of `n` pages in a run of order `k` from the page buddy `pb`: the reserve of a run span or the
/// back of its metadata page, only when `pb` had no free block of order `k` (`span_refused`); or
/// the back of the object's `n` pages from the run `pb` cut at `q`, while the source held the spans
/// it held once the run was cut, after which the run is freed again, leaving the page buddy `fin`
/// and the source's spans as `freed` says: as they were once the run was cut, or without the run's
/// span when no run is left in it and the spares are kept.
pub open spec fn part_refused(pb: PageBuddy, fin: PageBuddy, before: SourceView, after: SourceView, k: nat, n: nat) -> bool {
    let r = after.refusals.last();
    &&& after.provenance == before.provenance
    &&& after.refusals == before.refusals.push(r)
    &&& {
        ||| !pb.fits(k) && span_refused(before, after)
        ||| exists|mid: PageBuddy, s: SourceView, q: int| #[trigger]
            cut_run(pb, mid, before, s, q, k) && r == (Refusal {
                request: Request::Back { span: mid.span_base(span_of(q)), start: q, pages: n },
                spans: s.spans,
            }) && freed(mid, fin, s.recorded(r), after, q)
    }
}

/// Two classes share no head and no record.
pub open spec fn apart(a: SizeClass, b: SizeClass) -> bool {
    &&& a.heads().disjoint(b.heads())
    &&& a.slabs().dom().disjoint(b.slabs().dom())
}

/// Every record of `n` was one of `o`'s or was not taken in `store`.
pub open spec fn records_grew(o: SizeClass, n: SizeClass, store: RecordStore) -> bool {
    forall|a: int| #[trigger] n.slabs().contains_key(a) ==> o.slabs().contains_key(a) || !store.taken().contains(a)
}

/// `alloc` of a small layout went from `h0` to `h1`, and the source's view from `s0` to `s1`,
/// returning `r`: a slot of `class_for(size, align)`, or a refusal only when none of that class's
/// slabs had a free slot and the source refused one request in the call (`slab_refused`), which
/// leaves every class as it was. Every other class and the large objects are as they were either
/// way. The slot is aligned to `align` and apart from every slot, buddy-run object and large object
/// live before, and the class, the store, the page buddy and the source changed as `alloc_small`
/// says (`slot_taken`).
pub open spec fn slot_alloc(
    h0: Heap,
    h1: Heap,
    s0: SourceView,
    s1: SourceView,
    size: nat,
    align: nat,
    r: Option<(*mut u8, Tracked<PointsToRaw>)>,
) -> bool {
    let c = class_for(size, align) as int;
    let n = class_size(c as nat);
    &&& c < CLASSES
    &&& size <= n
    &&& h1.large() == h0.large()
    &&& h1.parts() == h0.parts()
    &&& forall|i: int| #![trigger h1.classes()[i]] 0 <= i < CLASSES && i != c ==> h1.classes()[i] == h0.classes()[i]
    &&& match r {
        None => {
            &&& forall|a: int| #[trigger]
                h0.classes()[c].slabs().contains_key(a) ==> h0.classes()[c].slabs()[a].free_slots() == Set::<int>::empty()
            &&& h1.classes() == h0.classes()
            &&& h1.live() == h0.live()
            &&& slab_refused(h0.store(), h0.pb(), s0, s1, slab_order(c as nat))
        },
        Some((p, perm)) => {
            &&& perm@.is_range(p@.addr as int, n as int)
            &&& perm@.provenance() == s0.provenance
            &&& p@.provenance == s0.provenance
            &&& p@.addr as int % align as int == 0
            &&& !h0.live().contains(p@.addr as int)
            &&& h1.live() == h0.live().insert(p@.addr as int)
            &&& h1.classes()[c].live() == h0.classes()[c].live().insert(p@.addr as int)
            &&& slot_taken(h0.classes()[c], h1.classes()[c], h0.store(), h1.store(), h0.pb(), h1.pb(), s0, s1, p@.addr as int)
            &&& forall|i: int, y: int|
                0 <= i < CLASSES && #[trigger] h0.classes()[i].live().contains(y) ==> p@.addr + n <= y || y
                    + class_size(i as nat) <= p@.addr
            &&& forall|x: int| #[trigger]
                h0.parts().contains_key(x) ==> p@.addr + n <= x || x + h0.parts()[x] * PAGE_BYTES <= p@.addr
            &&& forall|b: int| #[trigger]
                h0.large().contains_key(b) ==> p@.addr + n <= b || b + h0.large()[b] * PAGE_BYTES <= p@.addr
        },
    }
}

/// `alloc` of a large layout went from `h0` to `h1`, and the source's view from `s0` to `s1`,
/// returning `r`: a large object of `pages_for(size)` pages, or a refusal only when the source
/// refused the reserve of its span or the back of its pages in the call (`large_refused`), with
/// nothing else changed. The classes, the store, the page buddy and the buddy-run objects are as
/// they were either way. The object is a new span reserved and backed, aligned to `align`, and
/// apart from every slot, buddy-run object and large object live before.
pub open spec fn large_alloc(
    h0: Heap,
    h1: Heap,
    s0: SourceView,
    s1: SourceView,
    size: nat,
    align: nat,
    r: Option<(*mut u8, Tracked<PointsToRaw>)>,
) -> bool {
    let n = pages_for(size);
    &&& h1.classes() == h0.classes()
    &&& h1.store() == h0.store()
    &&& h1.pb() == h0.pb()
    &&& h1.parts() == h0.parts()
    &&& match r {
        None => {
            &&& h1.large() == h0.large()
            &&& h1.live() == h0.live()
            &&& large_refused(s0, s1, n)
        },
        Some((p, perm)) => {
            let b = p@.addr as int;
            &&& perm@.is_range(b, n * PAGE_BYTES)
            &&& size <= n * PAGE_BYTES
            &&& perm@.provenance() == s0.provenance
            &&& p@.provenance == s0.provenance
            &&& b % align as int == 0
            &&& !h0.live().contains(b)
            &&& h1.live() == h0.live().insert(b)
            &&& h1.large() == h0.large().insert(b, n)
            &&& s1 == s0.reserved(b, blocks_for(n)).backed_run(b, b, n + 1)
            &&& forall|i: int, y: int|
                0 <= i < CLASSES && #[trigger] h0.classes()[i].live().contains(y) ==> b + n * PAGE_BYTES <= y || y
                    + class_size(i as nat) <= b
            &&& forall|x: int| #[trigger]
                h0.parts().contains_key(x) ==> b + n * PAGE_BYTES <= x || x + h0.parts()[x] * PAGE_BYTES <= b
            &&& forall|x: int| #[trigger]
                h0.large().contains_key(x) ==> b + n * PAGE_BYTES <= x || x + h0.large()[x] * PAGE_BYTES <= b
        },
    }
}

/// `free` of the slot at `p` of a small layout went from `h0` to `h1`, and the source's view from
/// `s0` to `s1`: every other class, the buddy-run objects and the large objects are as they were,
/// and a slab left with a
/// live slot keeps the store, the page buddy and the source as they were; a slab left with none is
/// retired (`emptied_slab`).
pub open spec fn slot_free(h0: Heap, h1: Heap, s0: SourceView, s1: SourceView, p: int, size: nat, align: nat) -> bool {
    let c = class_for(size, align) as int;
    let oc = h0.classes()[c];
    let a = oc.slab_of(p);
    let b = oc.slabs()[a].base()@.addr as int;
    &&& h1.large() == h0.large()
    &&& h1.parts() == h0.parts()
    &&& forall|i: int| #![trigger h1.classes()[i]] 0 <= i < CLASSES && i != c ==> h1.classes()[i] == h0.classes()[i]
    &&& h1.classes()[c].live() == oc.live().remove(p)
    &&& if only_live(oc.slabs()[a], p) {
        emptied_slab(h0.store(), h1.store(), h0.pb(), h1.pb(), s0, s1, a, b, slab_order(c as nat))
    } else {
        &&& h1.store() == h0.store()
        &&& h1.pb() == h0.pb()
        &&& s1 == s0
    }
}

/// `free` of the large object at `p` went from `h0` to `h1`, and the source's view from `s0` to
/// `s1`: the classes, the store, the page buddy and the buddy-run objects are as they were, and
/// the object's span is given back whole.
pub open spec fn large_free(h0: Heap, h1: Heap, s0: SourceView, s1: SourceView, p: int) -> bool {
    &&& h1.classes() == h0.classes()
    &&& h1.store() == h0.store()
    &&& h1.pb() == h0.pb()
    &&& h1.parts() == h0.parts()
    &&& h1.large() == h0.large().remove(p)
    &&& s1 == s0.released_span(p)
}

/// `alloc` of a run layout went from `h0` to `h1`, and the source's view from `s0` to `s1`,
/// returning `r`: a buddy-run object of `n = pages_for(size)` pages in a run of the smallest order
/// `k` holding them, or a refusal only when the source refused a request in the call
/// (`part_refused`), which leaves the page buddy holding the runs it held. The classes, the store
/// and the large objects are as they were either way. The object is the run `alloc_run` cut with
/// only its first `n` pages backed, the permission to exactly those pages' bytes, page-aligned, so
/// aligned to `align`, and apart from every slot, buddy-run object and large object live before.
pub open spec fn part_alloc(
    h0: Heap,
    h1: Heap,
    s0: SourceView,
    s1: SourceView,
    size: nat,
    align: nat,
    r: Option<(*mut u8, Tracked<PointsToRaw>)>,
) -> bool {
    let n = pages_for(size);
    let k = run_order(n);
    &&& n <= pages(k)
    &&& k == 0 || pages((k - 1) as nat) < n
    &&& size <= n * PAGE_BYTES
    &&& h1.classes() == h0.classes()
    &&& h1.store() == h0.store()
    &&& h1.large() == h0.large()
    &&& match r {
        None => {
            &&& h1.parts() == h0.parts()
            &&& h1.live() == h0.live()
            &&& runs(h1.pb().used()) == runs(h0.pb().used())
            &&& part_refused(h0.pb(), h1.pb(), s0, s1, k, n)
        },
        Some((p, perm)) => {
            let b = p@.addr as int;
            &&& perm@.is_range(b, n * PAGE_BYTES)
            &&& perm@.provenance() == s0.provenance
            &&& p@.provenance == s0.provenance
            &&& b % PAGE_BYTES as int == 0
            &&& b % align as int == 0
            &&& !h0.live().contains(b)
            &&& h1.live() == h0.live().insert(b)
            &&& h1.parts() == h0.parts().insert(b, n)
            &&& run_part(h1.pb(), s1, b, k, n)
            &&& exists|mid: PageBuddy, sm: SourceView| #[trigger]
                cut_run(h0.pb(), mid, s0, sm, b, k) && s1 == sm.backed_run(mid.span_base(span_of(b)), b, n)
            &&& forall|i: int, y: int|
                0 <= i < CLASSES && #[trigger] h0.classes()[i].live().contains(y) ==> b + n * PAGE_BYTES <= y || y
                    + class_size(i as nat) <= b
            &&& forall|x: int| #[trigger]
                h0.parts().contains_key(x) ==> b + n * PAGE_BYTES <= x || x + h0.parts()[x] * PAGE_BYTES <= b
            &&& forall|x: int| #[trigger]
                h0.large().contains_key(x) ==> b + n * PAGE_BYTES <= x || x + h0.large()[x] * PAGE_BYTES <= b
        },
    }
}

/// `free` of the buddy-run object at `p` went from `h0` to `h1`, and the source's view from `s0`
/// to `s1`: the classes, the store and the large objects are as they were; the object's pages are
/// released, and its run freed (`freed`), which gives its span back to the source when no run is
/// left in it and the page buddy keeps as many idle spans as its spares.
pub open spec fn part_free(h0: Heap, h1: Heap, s0: SourceView, s1: SourceView, p: int) -> bool {
    &&& h1.classes() == h0.classes()
    &&& h1.store() == h0.store()
    &&& h1.large() == h0.large()
    &&& h1.parts() == h0.parts().remove(p)
    &&& freed(h0.pb(), h1.pb(), s0.released_run(h0.pb().span_base(span_of(p)), p, h0.parts()[p]), s1, p)
}

/// The smallest order whose run holds `n` pages.
fn order_for(n: usize) -> (r: usize)
    requires
        0 < n <= BLOCK_PAGES,
    ensures
        r as nat == run_order(n as nat),
        r <= BLOCK_ORDER,
        n <= pages(r as nat),
        r == 0 || pages((r - 1) as nat) < n,
{
    proof {
        lemma_block_pages();
    }
    let mut k: usize = 0;
    loop
        invariant
            k <= BLOCK_ORDER,
            0 < n <= BLOCK_PAGES,
            pages(BLOCK_ORDER as nat) == BLOCK_PAGES as int,
            order_up(n as nat, k as nat) == run_order(n as nat),
            k == 0 || pages((k - 1) as nat) < n,
        decreases BLOCK_ORDER - k,
    {
        if n <= order_pages(k) {
            return k;
        }
        k = k + 1;
    }
}

/// A run layout's object is of at least two pages and at most a block's, which hold its bytes.
proof fn lemma_run_sizes(size: nat)
    requires
        PAGE_BYTES < size <= BLOCK_BYTES,
    ensures
        2 <= pages_for(size) <= BLOCK_PAGES,
        size <= pages_for(size) * PAGE_BYTES,
{
    let pg = PAGE_BYTES as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(size - 1, pg);
    let q = (size - 1) / pg;
    let m = (size - 1) % pg;
    assert(q >= 1) by (nonlinear_arith)
        requires
            size - 1 == pg * q + m,
            0 <= m < pg,
            size - 1 >= pg,
    ;
    assert(q <= BLOCK_PAGES - 1) by (nonlinear_arith)
        requires
            size - 1 == pg * q + m,
            0 <= m,
            size - 1 < pg * BLOCK_PAGES,
            pg > 0,
    ;
    assert(size <= (q + 1) * pg) by (nonlinear_arith)
        requires
            size - 1 == pg * q + m,
            m < pg,
    ;
}

/// `n` pages of `m` or fewer take no more bytes than `m` pages.
proof fn lemma_page_bytes(n: int, m: int)
    requires
        n <= m,
    ensures
        n * PAGE_BYTES <= m * PAGE_BYTES,
{
    assert(n * PAGE_BYTES <= m * PAGE_BYTES) by (nonlinear_arith)
        requires
            n <= m,
            PAGE_BYTES > 0,
    ;
}

/// The first `n` pages of a run of `m` pages with none backed have none backed.
proof fn lemma_fewer_unbacked(s: SourceView, b: int, q: int, n: nat, m: nat)
    requires
        s.unbacked(b, q, m),
        n <= m,
    ensures
        s.unbacked(b, q, n),
{
    lemma_page_bytes(n as int, m as int);
    assert(run_pages(q, n).subset_of(run_pages(q, m)));
}

/// The class of a small layout, its slot holding `size` bytes and a multiple of `align`.
fn class_index(n: usize, align: usize) -> (c: usize)
    requires
        small_layout(n as nat, align as nat),
    ensures
        c as nat == class_for(n as nat, align as nat),
        c < CLASSES,
        n <= class_size(c as nat),
        class_size(c as nat) % align as nat == 0,
{
    proof {
        lemma_class((CLASSES - 1) as nat);
    }
    let mut c: usize = 0;
    loop
        invariant
            c < CLASSES,
            class_from(n as nat, align as nat, c as nat) == class_for(n as nat, align as nat),
            small_layout(n as nat, align as nat),
            class_size((CLASSES - 1) as nat) == PAGE_BYTES,
        decreases CLASSES - c,
    {
        if c + 1 >= CLASSES {
            return c;
        }
        let s = size(c);
        if n <= s && s % align == 0 {
            return c;
        }
        c = c + 1;
    }
}

/// An address `b + k` with `b` a multiple of the page and `k` a multiple of `n`, when `align`
/// divides both the page and `n`, is a multiple of `align`.
proof fn lemma_aligned(y: int, b: int, n: int, align: int)
    requires
        0 < align,
        0 < n,
        b % PAGE_BYTES as int == 0,
        (y - b) % n == 0,
        PAGE_BYTES as int % align == 0,
        n % align == 0,
    ensures
        y % align == 0,
{
    let pb = PAGE_BYTES as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b, pb);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(y - b, n);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(pb, align);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n, align);
    let q = b / pb;
    let k = (y - b) / n;
    let u = pb / align;
    let v = n / align;
    assert(y == align * (u * q + v * k)) by (nonlinear_arith)
        requires
            b == pb * q,
            y - b == n * k,
            pb == align * u,
            n == align * v,
    ;
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(u * q + v * k, align);
    assert(align * (u * q + v * k) == (u * q + v * k) * align) by (nonlinear_arith);
}

/// A span at `b` of `blocks` blocks, apart from every span the page buddy holds, lies before or
/// after the span of each block the page buddy holds, so it is none of those blocks.
proof fn lemma_beside_span(pb: PageBuddy, s: SourceView, c: int, b: int, blocks: nat)
    requires
        pb.wf(s),
        pb.spans().contains_key(c),
        blocks > 0,
        forall|x: int| #[trigger] pb.spans().contains_key(x) && s.spans.contains_key(x) ==> s.apart(b, blocks, x),
    ensures
        b + span_bytes(blocks) <= pb.span_base(c) || pb.span_base(c) + 2 * BLOCK_BYTES <= b,
        pb.span_base(c) <= c <= pb.span_base(c) + BLOCK_BYTES,
        span_bytes(blocks) >= BLOCK_BYTES,
        b != c,
{
    lemma_span_base(pb, s, c);
    let x = pb.span_base(c);
    assert(s.apart(b, blocks, x));
    assert(blocks * BLOCK_BYTES as int >= BLOCK_BYTES as int) by (nonlinear_arith)
        requires
            blocks >= 1,
    ;
}

/// The heap: a size class per class over one record store and one page buddy, the buddy-run
/// objects, and the large-object map.
pub struct Heap {
    /// Class `i` at index `i`.
    classes: [SizeClass; CLASSES],
    /// The records of every class's slabs.
    store: RecordStore,
    /// The runs of every class's slabs and the store's record pages.
    pb: PageBuddy,
    /// The large objects, a span each.
    large: LargeMap,
    /// The buddy-run objects, by base, with the pages each has backed: each a run of the page
    /// buddy's, of the smallest order holding those pages.
    parts: Ghost<Map<int, nat>>,
}

impl Heap {
    /// The size classes, class `i` at index `i`.
    pub closed spec fn classes(&self) -> Seq<SizeClass> {
        self.classes@
    }

    /// The record store.
    pub closed spec fn store(&self) -> RecordStore {
        self.store
    }

    /// The page buddy.
    pub closed spec fn pb(&self) -> PageBuddy {
        self.pb
    }

    /// The large objects, by base, with their pages.
    pub closed spec fn large(&self) -> Map<int, nat> {
        self.large.objects()
    }

    /// The buddy-run objects, by base, with the pages each has backed.
    pub closed spec fn parts(&self) -> Map<int, nat> {
        self.parts@
    }

    /// The idle spans the page buddy keeps rather than give back.
    pub closed spec fn spares(&self) -> nat {
        self.pb.spares()
    }

    /// The live slots of every class and the bases of the buddy-run objects and the large objects.
    pub open spec fn live(&self) -> ISet<int> {
        ISet::new(
            |y: int|
                (exists|i: int| 0 <= i < CLASSES && #[trigger] self.classes()[i].live().contains(y))
                    || self.parts().contains_key(y) || self.large().contains_key(y),
        )
    }

    /// The slab arm's invariant: the page buddy and the store are well formed over `src`; class `i`
    /// is the `i`-th class and well formed over them; and no two classes share a head or a record.
    spec fn small_wf(&self, src: SourceView) -> bool {
        &&& self.classes@.len() == CLASSES
        &&& self.pb.wf(src)
        &&& self.store.wf(self.pb, src)
        &&& forall|i: int| 0 <= i < CLASSES ==> (#[trigger] self.classes@[i]).class() == i
        &&& forall|i: int| 0 <= i < CLASSES ==> (#[trigger] self.classes@[i]).wf(self.store, self.pb, src)
        &&& forall|i: int, j: int|
            0 <= i < CLASSES && 0 <= j < CLASSES && i != j ==> #[trigger] apart(self.classes@[i], self.classes@[j])
    }

    /// The buddy-run object at `x` is a run the page buddy holds, of the smallest order holding the
    /// object's pages, with only those pages backed, and no record page or slab run.
    spec fn part_ok(&self, src: SourceView, x: int) -> bool {
        let n = self.parts@[x];
        &&& run_part(self.pb, src, x, run_order(n), n)
        &&& !self.store.pages().contains(x)
        &&& forall|i: int| 0 <= i < CLASSES ==> !(#[trigger] self.classes@[i]).heads().contains(x)
    }

    /// The slab arm's invariant; each buddy-run object a run the page buddy holds with only its
    /// pages backed; and the large-object map well formed over `src`, each large object's span one
    /// the page buddy does not hold.
    pub closed spec fn wf(&self, src: SourceView) -> bool {
        &&& self.small_wf(src)
        &&& forall|x: int| #[trigger] self.parts@.contains_key(x) ==> self.part_ok(src, x)
        &&& self.large.wf(src)
        &&& forall|b: int| #[trigger] self.large.objects().contains_key(b) ==> !self.pb.spans().contains_key(b)
    }

    /// The invariant's parts a caller follows a sequence by: the page buddy and the store well
    /// formed over `src`, class `i` the `i`-th class and well formed over them, no two classes sharing
    /// a head or a record, and each buddy-run object a run the page buddy holds, of the smallest
    /// order holding its pages, with only those pages backed.
    pub proof fn lemma_parts(&self, src: SourceView)
        requires
            self.wf(src),
        ensures
            self.classes().len() == CLASSES,
            self.pb().wf(src),
            self.store().wf(self.pb(), src),
            forall|i: int| 0 <= i < CLASSES ==> (#[trigger] self.classes()[i]).class() == i,
            forall|i: int| 0 <= i < CLASSES ==> (#[trigger] self.classes()[i]).wf(self.store(), self.pb(), src),
            forall|i: int, j: int|
                0 <= i < CLASSES && 0 <= j < CLASSES && i != j ==> #[trigger] apart(self.classes()[i], self.classes()[j]),
            forall|x: int| #[trigger]
                self.parts().contains_key(x) ==> run_part(self.pb(), src, x, run_order(self.parts()[x]), self.parts()[x]),
    {
        assert forall|x: int| #[trigger] self.parts().contains_key(x) implies run_part(
            self.pb(),
            src,
            x,
            run_order(self.parts()[x]),
            self.parts()[x],
        ) by {
            assert(self.part_ok(src, x));
        }
    }

    /// A change to the page buddy and the source that keeps the provenance, every span the page
    /// buddy does not hold, and every run it holds, whole or with only its first pages backed, but
    /// the one at `b`, which is no record page or slab run if the page buddy holds it, keeps the
    /// store's, every class's and the large-object map's invariants, and every other buddy-run
    /// object.
    proof fn lemma_pb_frame(&self, s0: SourceView, pb1: PageBuddy, s1: SourceView, b: int)
        requires
            self.wf(s0),
            pb1.wf(s1),
            s1.provenance == s0.provenance,
            forall|x: int, j: nat| #[trigger] run_held(self.pb, s0, x, j) && x != b ==> run_held(pb1, s1, x, j),
            forall|x: int, j: nat, n: nat| #[trigger]
                run_part(self.pb, s0, x, j, n) && x != b ==> run_part(pb1, s1, x, j, n),
            others_kept(self.pb, pb1, s0, s1),
            !self.pb.holds(b) || (!self.store.pages().contains(b) && forall|i: int|
                0 <= i < CLASSES ==> !(#[trigger] self.classes@[i]).heads().contains(b)),
        ensures
            self.store.wf(pb1, s1),
            forall|i: int| 0 <= i < CLASSES ==> (#[trigger] self.classes@[i]).wf(self.store, pb1, s1),
            self.large.wf(s1),
            forall|c: int| #[trigger] self.large.objects().contains_key(c) ==> !pb1.spans().contains_key(c),
            forall|x: int| #[trigger]
                self.parts@.contains_key(x) && x != b ==> run_part(pb1, s1, x, run_order(self.parts@[x]), self.parts@[x]),
    {
        self.store.lemma_view(self.pb, s0);
        assert forall|r: int| #[trigger] self.store.pages().contains(r) implies run_held(pb1, s1, r, 0) by {
            assert(run_held(self.pb, s0, r, 0));
        }
        self.store.lemma_frame(self.pb, s0, pb1, s1);
        assert forall|i: int| 0 <= i < CLASSES implies (#[trigger] self.classes@[i]).wf(self.store, pb1, s1) by {
            let ci = self.classes@[i];
            assert(ci.wf(self.store, self.pb, s0));
            ci.lemma_heads_held(self.store, self.pb, s0);
            assert(!ci.heads().contains(b)) by {
                if ci.heads().contains(b) {
                    assert(run_held(self.pb, s0, b, slab_order(ci.class())));
                }
            }
            ci.lemma_frame_but_run(self.store, self.pb, s0, pb1, s1, b);
        }
        self.large.lemma_view(s0);
        assert forall|c: int| #[trigger] self.large.objects().contains_key(c) implies {
            &&& s1.spans.contains_key(c)
            &&& s1.spans[c] == s0.spans[c]
            &&& !pb1.spans().contains_key(c)
        } by {
            assert(s0.spans.contains_key(c));
            assert(!self.pb.spans().contains_key(c));
        }
        self.large.lemma_frame(s0, s1);
        assert forall|x: int| #[trigger] self.parts@.contains_key(x) && x != b implies run_part(
            pb1,
            s1,
            x,
            run_order(self.parts@[x]),
            self.parts@[x],
        ) by {
            assert(self.part_ok(s0, x));
        }
    }

    /// A live slot of class `i` and a buddy-run object share no byte.
    proof fn lemma_slot_beside_part(&self, src: SourceView, i: int, y: int, x: int)
        requires
            self.wf(src),
            0 <= i < CLASSES,
            self.classes()[i].live().contains(y),
            self.parts().contains_key(x),
        ensures
            y + class_size(i as nat) <= x || x + self.parts()[x] * PAGE_BYTES <= y,
            y != x,
    {
        let ci = self.classes@[i];
        let n = self.parts@[x];
        let k = run_order(n);
        assert(self.part_ok(src, x));
        assert(ci.wf(self.store, self.pb, src));
        assert(ci.class() == i);
        assert(!ci.heads().contains(x));
        ci.lemma_live_apart_from_run(self.store, self.pb, src, y, x, k);
        lemma_page_bytes(n as int, pages(k));
        lemma_class(i as nat);
        assert(n * PAGE_BYTES > 0) by (nonlinear_arith)
            requires
                n > 0,
        ;
    }

    /// A buddy-run object and a large object share no byte.
    proof fn lemma_part_beside_large(&self, src: SourceView, x: int, b: int)
        requires
            self.wf(src),
            self.parts().contains_key(x),
            self.large().contains_key(b),
        ensures
            x + self.parts()[x] * PAGE_BYTES <= b || b + self.large()[b] * PAGE_BYTES <= x,
            x != b,
    {
        let n = self.parts@[x];
        let k = run_order(n);
        assert(self.part_ok(src, x));
        lemma_held_bounds(self.pb, src, x, k);
        self.lemma_large_beside(src, b);
        lemma_beside_span(self.pb, src, span_of(x), b, blocks_for(self.large()[b]));
        lemma_page_bytes(n as int, pages(k));
        assert(n * PAGE_BYTES > 0) by (nonlinear_arith)
            requires
                n > 0,
        ;
    }

    /// Two buddy-run objects share no byte.
    proof fn lemma_parts_apart(&self, src: SourceView, x: int, z: int)
        requires
            self.wf(src),
            self.parts().contains_key(x),
            self.parts().contains_key(z),
            x != z,
        ensures
            x + self.parts()[x] * PAGE_BYTES <= z || z + self.parts()[z] * PAGE_BYTES <= x,
    {
        let n = self.parts@[x];
        let m = self.parts@[z];
        assert(self.part_ok(src, x));
        assert(self.part_ok(src, z));
        lemma_held_apart(self.pb, src, x, run_order(n), z, run_order(m));
        lemma_page_bytes(n as int, pages(run_order(n)));
        lemma_page_bytes(m as int, pages(run_order(m)));
    }

    /// A live slot of class `i` and one of another class `j` share no byte.
    pub proof fn lemma_live_apart(&self, src: SourceView, i: int, j: int, y: int, z: int)
        requires
            self.wf(src),
            0 <= i < CLASSES,
            0 <= j < CLASSES,
            self.classes()[i].live().contains(y),
            self.classes()[j].live().contains(z),
            i != j,
        ensures
            y + class_size(i as nat) <= z || z + class_size(j as nat) <= y,
    {
        let ci = self.classes@[i];
        let cj = self.classes@[j];
        assert(apart(ci, cj));
        ci.lemma_classes_apart(&cj, self.store, self.pb, src, y, z);
    }

    /// A change to the source that keeps every span the page buddy holds, and the provenance,
    /// keeps the slab arm's invariant.
    proof fn lemma_small_frame(&self, s: SourceView, t: SourceView)
        requires
            self.small_wf(s),
            t.wf(),
            t.provenance == s.provenance,
            forall|x: int| #[trigger]
                self.pb.spans().contains_key(x) && s.spans.contains_key(x) ==> t.spans.contains_key(x) && t.spans[x]
                    == s.spans[x],
        ensures
            self.small_wf(t),
            forall|x: int, k: nat, n: nat| #[trigger] run_part(self.pb, s, x, k, n) ==> run_part(self.pb, t, x, k, n),
    {
        let pb = self.pb;
        assert forall|x: int, k: nat| #[trigger] run_held(pb, s, x, k) implies run_held(pb, t, x, k) by {
            lemma_span_base(pb, s, span_of(x));
        }
        assert forall|x: int, k: nat, n: nat| #[trigger] run_part(pb, s, x, k, n) implies run_part(pb, t, x, k, n) by {
            lemma_span_base(pb, s, span_of(x));
        }
        assert forall|c: int| #[trigger]
            pb.spans().contains_key(c) && !pb.metas().contains(c) implies t.spans.contains_key(c) && t.spans[c]
            == s.spans[c] by {
            lemma_span_base(pb, s, c);
        }
        pb.lemma_frame(s, t);
        self.store.lemma_view(pb, s);
        self.store.lemma_frame(pb, s, pb, t);
        assert(kept(self.store, pb, s, self.store, pb, t));
        assert forall|i: int| 0 <= i < CLASSES implies (#[trigger] self.classes@[i]).wf(self.store, pb, t) by {
            self.classes@[i].lemma_frame(self.store, pb, s, self.store, pb, t);
        }
    }

    /// A large object's span is reserved as the map holds it, holds its pages with room for its
    /// record page, and is apart from every span the page buddy holds.
    proof fn lemma_large_beside(&self, src: SourceView, b: int)
        requires
            self.wf(src),
            self.large().contains_key(b),
        ensures
            src.spans.contains_key(b),
            src.spans[b] == large_span(b, self.large()[b]),
            self.large()[b] * PAGE_BYTES > 0,
            self.large()[b] * PAGE_BYTES < span_bytes(blocks_for(self.large()[b])),
            blocks_for(self.large()[b]) > 0,
            !self.pb.spans().contains_key(b),
            forall|x: int| #[trigger]
                self.pb.spans().contains_key(x) && src.spans.contains_key(x) ==> src.apart(b, blocks_for(self.large()[b]), x),
    {
        let n = self.large()[b];
        self.large.lemma_view(src);
        self.pb.lemma_view(src);
        lemma_blocks_for(n);
        assert(n * PAGE_BYTES > 0) by (nonlinear_arith)
            requires
                n > 0,
                PAGE_BYTES > 0,
        ;
        assert(src.released_span(b).fits(b, src.spans[b].blocks));
        assert forall|x: int| #[trigger]
            self.pb.spans().contains_key(x) && src.spans.contains_key(x) implies src.apart(b, blocks_for(n), x) by {
            assert(x != b);
            assert(src.released_span(b).spans.contains_key(x));
        }
    }

    /// A live slot of class `i` lies before or after a span at `b` of `blocks` blocks apart from
    /// every span the page buddy holds.
    proof fn lemma_slot_beside(&self, src: SourceView, i: int, y: int, b: int, blocks: nat)
        requires
            self.small_wf(src),
            0 <= i < CLASSES,
            self.classes()[i].live().contains(y),
            blocks > 0,
            forall|x: int| #[trigger] self.pb.spans().contains_key(x) && src.spans.contains_key(x) ==> src.apart(b, blocks, x),
        ensures
            b + span_bytes(blocks) <= y || y + class_size(i as nat) <= b,
    {
        let ci = self.classes@[i];
        assert(ci.wf(self.store, self.pb, src));
        assert(ci.class() == i);
        let h = ci.lemma_live_in_run(self.store, self.pb, src, y);
        let k = slab_order(ci.class());
        lemma_held_bounds(self.pb, src, h, k);
        lemma_beside_span(self.pb, src, span_of(h), b, blocks);
    }

    /// The heap with no slab and no large object, keeping `spares` idle spans, well formed over
    /// every well-formed source's view.
    pub fn new(spares: usize) -> (r: Self)
        ensures
            forall|src: SourceView| #[trigger] src.wf() ==> r.wf(src),
            r.spares() == spares,
            r.live() == ISet::<int>::empty(),
    {
        // One entry per class: the array's type fixes the count at CLASSES, so a target whose
        // CLASSES differs does not compile until the list follows it.
        let classes: [SizeClass; CLASSES] = [
            SizeClass::new(0),
            SizeClass::new(1),
            SizeClass::new(2),
            SizeClass::new(3),
            SizeClass::new(4),
            SizeClass::new(5),
            SizeClass::new(6),
            SizeClass::new(7),
            SizeClass::new(8),
            SizeClass::new(9),
            SizeClass::new(10),
            SizeClass::new(11),
            SizeClass::new(12),
            SizeClass::new(13),
            SizeClass::new(14),
            SizeClass::new(15),
            SizeClass::new(16),
            SizeClass::new(17),
            SizeClass::new(18),
            SizeClass::new(19),
            SizeClass::new(20),
            SizeClass::new(21),
            SizeClass::new(22),
            SizeClass::new(23),
            SizeClass::new(24),
            SizeClass::new(25),
            SizeClass::new(26),
            SizeClass::new(27),
        ];
        let r = Heap {
            classes,
            store: RecordStore::new(),
            pb: PageBuddy::new(spares),
            large: LargeMap::new(),
            parts: Ghost(Map::empty()),
        };
        proof {
            assert forall|i: int| 0 <= i < CLASSES implies {
                &&& (#[trigger] r.classes@[i]).class() == i
                &&& r.classes@[i].slabs() == Map::<int, crate::slab::Slab>::empty()
                &&& r.classes@[i].heads() == ISet::<int>::empty()
                &&& r.classes@[i].live() == ISet::<int>::empty()
                &&& forall|store: RecordStore, pb: PageBuddy, src: SourceView| #[trigger]
                    r.classes@[i].wf(store, pb, src)
            } by {
                assert(r.classes@ == classes@);
            }
            assert forall|i: int, j: int|
                0 <= i < CLASSES && 0 <= j < CLASSES && i != j implies #[trigger] apart(
                r.classes@[i],
                r.classes@[j],
            ) by {
                assert(r.classes@[i].slabs().dom() =~= Set::<int>::empty());
            }
            assert forall|src: SourceView| #[trigger] src.wf() implies r.wf(src) by {
                assert forall|i: int| 0 <= i < CLASSES implies (#[trigger] r.classes@[i]).wf(
                    r.store,
                    r.pb,
                    src,
                ) by {
                    assert(r.classes@[i].class() == i);
                }
                assert(r.large.wf(src));
                assert(r.parts@ == Map::<int, nat>::empty());
            }
            assert(r.live() =~= ISet::<int>::empty());
        }
        r
    }

    /// An object of `size` bytes aligned to `align`: a slot of `class_for(size, align)` for a small
    /// layout (`slot_alloc`), a buddy-run object of `pages_for(size)` pages for a run layout
    /// (`part_alloc`), a large object of `pages_for(size)` pages for a large one (`large_alloc`);
    /// or a refusal, only when the source refused a request in this call.
    pub fn alloc<S: SpanSource>(&mut self, src: &mut S, size: usize, align: usize) -> (r: Option<
        (*mut u8, Tracked<PointsToRaw>),
    >)
        requires
            old(self).wf(old(src)@),
            small_layout(size as nat, align as nat) || run_layout(size as nat, align as nat) || large_layout(
                size as nat,
                align as nat,
            ),
        ensures
            final(self).wf(final(src)@),
            final(self).spares() == old(self).spares(),
            small_layout(size as nat, align as nat) ==> slot_alloc(
                *old(self),
                *final(self),
                old(src)@,
                final(src)@,
                size as nat,
                align as nat,
                r,
            ),
            run_layout(size as nat, align as nat) ==> part_alloc(
                *old(self),
                *final(self),
                old(src)@,
                final(src)@,
                size as nat,
                align as nat,
                r,
            ),
            large_layout(size as nat, align as nat) ==> large_alloc(
                *old(self),
                *final(self),
                old(src)@,
                final(src)@,
                size as nat,
                align as nat,
                r,
            ),
    {
        if size <= PAGE_BYTES {
            self.alloc_slot(src, size, align)
        } else if size <= BLOCK_BYTES {
            self.alloc_part(src, size, align)
        } else {
            self.alloc_object(src, size, align)
        }
    }

    /// The slab arm of `alloc`.
    fn alloc_slot<S: SpanSource>(&mut self, src: &mut S, size: usize, align: usize) -> (r: Option<
        (*mut u8, Tracked<PointsToRaw>),
    >)
        requires
            old(self).wf(old(src)@),
            small_layout(size as nat, align as nat),
        ensures
            final(self).wf(final(src)@),
            final(self).spares() == old(self).spares(),
            slot_alloc(*old(self), *final(self), old(src)@, final(src)@, size as nat, align as nat, r),
    {
        let c = class_index(size, align);
        let ghost ci = c as int;
        let ghost o = *self;
        let ghost oc = self.classes@[ci];
        let ghost s0 = src@;
        let r = self.classes[c].alloc_small(&mut self.store, &mut self.pb, src);
        proof {
            let nc = self.classes@[ci];
            let s1 = src@;
            assert(self.classes@ == o.classes@.update(ci, nc));
            lemma_class(c as nat);
            lemma_heads_grew(oc, nc, o.store, self.store, o.pb, self.pb, s0, s1, r);
            assert(records_grew(oc, nc, o.store)) by {
                match r {
                    None => {},
                    Some(_) => {
                        if !exists|a: int| #[trigger]
                            oc.slabs().contains_key(a) && oc.slabs()[a].free_slots() != Set::<int>::empty() {
                            let a = choose|a: int| #[trigger]
                                nc.slabs().contains_key(a) && {
                                    &&& !oc.slabs().contains_key(a)
                                    &&& nc.slabs() == oc.slabs().insert(a, nc.slabs()[a])
                                    &&& nc.slabs()[a].holds(r->Some_0.0@.addr as int)
                                    &&& nc.heads() == oc.heads().insert(nc.slabs()[a].base()@.addr as int)
                                    &&& forall|y: int, j: nat| #[trigger]
                                        run_held(o.pb, s0, y, j) ==> y != nc.slabs()[a].base()@.addr
                                    &&& new_slab(
                                        o.store,
                                        self.store,
                                        o.pb,
                                        self.pb,
                                        s0,
                                        s1,
                                        a,
                                        nc.slabs()[a].base()@.addr as int,
                                        slab_order(oc.class()),
                                    )
                                };
                            assert forall|x: int| #[trigger] nc.slabs().contains_key(x) implies oc.slabs().contains_key(x)
                                || !o.store.taken().contains(x) by {
                                if x != a {
                                    assert(oc.slabs().contains_key(x));
                                }
                            }
                        }
                    },
                }
            }
            assert forall|i: int| 0 <= i < CLASSES implies (#[trigger] self.classes@[i]).class() == i by {
                assert(o.classes@[i].class() == i);
            }
            assert forall|i: int| 0 <= i < CLASSES implies (#[trigger] self.classes@[i]).wf(self.store, self.pb, s1) by {
                if i != ci {
                    assert(o.classes@[i].wf(o.store, o.pb, s0));
                    o.classes@[i].lemma_frame(o.store, o.pb, s0, self.store, self.pb, s1);
                }
            }
            assert forall|i: int, j: int|
                0 <= i < CLASSES && 0 <= j < CLASSES && i != j implies #[trigger] apart(
                self.classes@[i],
                self.classes@[j],
            ) by {
                assert(apart(o.classes@[i], o.classes@[j]));
                if i == ci || j == ci {
                    let k = if i == ci { j } else { i };
                    let ok = o.classes@[k];
                    assert(apart(oc, ok));
                    assert(ok.wf(o.store, o.pb, s0));
                    lemma_heads_stay_apart(oc, nc, ok, o.store, o.pb, s0);
                    ok.lemma_records_taken(o.store, o.pb, s0);
                    assert(nc.slabs().dom().disjoint(ok.slabs().dom())) by {
                        assert forall|a: int| nc.slabs().dom().contains(a) implies !ok.slabs().dom().contains(a) by {
                            assert(nc.slabs().contains_key(a));
                        }
                    }
                }
            }
            o.large.lemma_view(s0);
            assert forall|b: int| #[trigger] self.large.objects().contains_key(b) implies {
                &&& s1.spans.contains_key(b)
                &&& s1.spans[b] == s0.spans[b]
                &&& !self.pb.spans().contains_key(b)
            } by {
                assert(s0.spans.contains_key(b));
                assert(!o.pb.spans().contains_key(b));
            }
            self.large.lemma_frame(s0, s1);
            assert forall|x: int| #[trigger] self.parts@.contains_key(x) implies self.part_ok(s1, x) by {
                assert(o.part_ok(s0, x));
                let n = o.parts@[x];
                let kx = run_order(n);
                assert(run_part(o.pb, s0, x, kx, n));
                assert forall|i: int| 0 <= i < CLASSES implies !(#[trigger] self.classes@[i]).heads().contains(x) by {
                    assert(!o.classes@[i].heads().contains(x));
                    if i == ci {
                        match r {
                            None => {},
                            Some(_) => {
                                if !exists|a: int| #[trigger]
                                    oc.slabs().contains_key(a) && oc.slabs()[a].free_slots() != Set::<int>::empty() {
                                    let a = choose|a: int| #[trigger]
                                        nc.slabs().contains_key(a) && {
                                            &&& nc.heads() == oc.heads().insert(nc.slabs()[a].base()@.addr as int)
                                            &&& new_slab(
                                                o.store,
                                                self.store,
                                                o.pb,
                                                self.pb,
                                                s0,
                                                s1,
                                                a,
                                                nc.slabs()[a].base()@.addr as int,
                                                slab_order(oc.class()),
                                            )
                                        };
                                    let h = nc.slabs()[a].base()@.addr as int;
                                    let k = slab_order(oc.class());
                                    let (pbm, sm) = choose|pbm: PageBuddy, sm: SourceView| #[trigger]
                                        took_run(o.pb, pbm, s0, sm, h, k);
                                    let c = span_of(h);
                                    let m = if o.pb.spans().contains_key(c) {
                                        s0
                                    } else {
                                        s0.reserved(c, SPAN_BLOCKS as nat).backed_run(c, meta_page(c), 1)
                                    };
                                    assert(cut_run(o.pb, pbm, s0, m, h, k));
                                    lemma_cut_keeps_part(o.pb, pbm, s0, m, h, k, x, kx, n);
                                }
                            },
                        }
                    } else {
                        assert(self.classes@[i] == o.classes@[i]);
                    }
                }
            }
            assert(self.wf(s1));
            match r {
                None => {
                    assert(self.classes@ =~= o.classes@);
                },
                Some((p, _)) => {
                    let y0 = p@.addr as int;
                    let n = class_size(c as nat) as int;
                    assert(nc.live().contains(y0));
                    let b = nc.lemma_live_in_run(self.store, self.pb, s1, y0);
                    lemma_held_bounds(self.pb, s1, b, slab_order(c as nat));
                    lemma_aligned(y0, b, n, align as int);
                    assert forall|i: int, y: int|
                        0 <= i < CLASSES && #[trigger] o.classes@[i].live().contains(y) implies y0 + n <= y || y
                        + class_size(i as nat) <= y0 by {
                        if i != ci {
                            assert(self.classes@[i] == o.classes@[i]);
                            assert(apart(nc, self.classes@[i]));
                            nc.lemma_classes_apart(&self.classes@[i], self.store, self.pb, s1, y0, y);
                        }
                    }
                    assert forall|x: int| #[trigger] o.large().contains_key(x) implies y0 + n <= x || x + o.large()[x]
                        * PAGE_BYTES <= y0 by {
                        self.lemma_large_beside(s1, x);
                        self.lemma_slot_beside(s1, ci, y0, x, blocks_for(self.large()[x]));
                    }
                    assert forall|x: int| #[trigger] o.parts().contains_key(x) implies y0 + n <= x || x + o.parts()[x]
                        * PAGE_BYTES <= y0 by {
                        self.lemma_slot_beside_part(s1, ci, y0, x);
                    }
                    assert(!o.live().contains(y0)) by {
                        if o.parts().contains_key(y0) {
                            self.lemma_slot_beside_part(s1, ci, y0, y0);
                        } else if o.large().contains_key(y0) {
                            self.lemma_large_beside(s1, y0);
                        } else if o.live().contains(y0) {
                            let i = choose|i: int| 0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(y0);
                            lemma_class(i as nat);
                        }
                    }
                    assert(self.live() =~= o.live().insert(y0)) by {
                        assert forall|y: int| #[trigger] self.live().contains(y) == o.live().insert(y0).contains(y) by {
                            if self.live().contains(y) && !self.large().contains_key(y) && !self.parts().contains_key(y) {
                                let i = choose|i: int| 0 <= i < CLASSES && #[trigger] self.classes()[i].live().contains(y);
                                if i != ci {
                                    assert(o.classes()[i].live().contains(y));
                                } else if y != y0 {
                                    assert(o.classes()[ci].live().contains(y));
                                }
                            }
                            if o.live().contains(y) && !o.large().contains_key(y) && !o.parts().contains_key(y) {
                                let i = choose|i: int| 0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(y);
                                if i != ci {
                                    assert(self.classes()[i].live().contains(y));
                                } else {
                                    assert(self.classes()[ci].live().contains(y));
                                }
                            }
                            if y == y0 {
                                assert(self.classes()[ci].live().contains(y));
                            }
                        }
                    }
                },
            }
        }
        r
    }

    /// The buddy-run arm of `alloc`.
    fn alloc_part<S: SpanSource>(&mut self, src: &mut S, size: usize, align: usize) -> (r: Option<
        (*mut u8, Tracked<PointsToRaw>),
    >)
        requires
            old(self).wf(old(src)@),
            run_layout(size as nat, align as nat),
        ensures
            final(self).wf(final(src)@),
            final(self).spares() == old(self).spares(),
            part_alloc(*old(self), *final(self), old(src)@, final(src)@, size as nat, align as nat, r),
    {
        let ghost o = *self;
        let ghost pb0 = self.pb;
        let ghost s0 = src@;
        proof {
            lemma_run_sizes(size as nat);
            pb0.lemma_view(s0);
            o.store.lemma_view(pb0, s0);
        }
        let n = (size - 1) / PAGE_BYTES + 1;
        let k = order_for(n);
        let ghost kk = k as nat;
        let ghost nn = n as nat;
        let q = match self.pb.alloc_run(src, k) {
            Err(_) => {
                proof {
                    let pb1 = self.pb;
                    let s1 = src@;
                    let rf = s1.refusals.last();
                    assert forall|x: int, j: nat| #[trigger] run_held(pb0, s0, x, j) && x != -1 implies run_held(
                        pb1,
                        s1,
                        x,
                        j,
                    ) by {
                        lemma_recorded_keeps_held(pb0, s0, rf, x, j);
                    }
                    assert forall|x: int, j: nat, m: nat| #[trigger] run_part(pb0, s0, x, j, m) && x != -1 implies run_part(
                        pb1,
                        s1,
                        x,
                        j,
                        m,
                    ) by {
                        lemma_recorded_keeps_part(pb0, s0, rf, x, j, m);
                    }
                    assert(s1.spans == s0.spans);
                    lemma_others_same(pb0, pb1, s0, s1);
                    o.lemma_pb_frame(s0, pb1, s1, -1);
                    assert forall|x: int| #[trigger] self.parts@.contains_key(x) implies self.part_ok(s1, x) by {
                        assert(o.part_ok(s0, x));
                    }
                    assert(self.wf(s1));
                    assert(self.live() =~= o.live());
                    assert(part_refused(pb0, pb1, s0, s1, kk, nn));
                }
                return None;
            },
            Ok(q) => q,
        };
        let ghost qi = q as int;
        let ghost pb1 = self.pb;
        let ghost s1 = src@;
        proof {
            assert(cut_run(pb0, pb1, s0, s1, qi, kk));
            assert(s1.refusals == s0.refusals && s1.provenance == s0.provenance);
            assert forall|x: int, j: nat| #[trigger] run_held(pb0, s0, x, j) implies x != qi && run_held(pb1, s1, x, j) by {
                lemma_cut_keeps_held(pb0, pb1, s0, s1, qi, kk, x, j);
            }
            assert forall|x: int, j: nat, m: nat| #[trigger] run_part(pb0, s0, x, j, m) implies x != qi && run_part(
                pb1,
                s1,
                x,
                j,
                m,
            ) by {
                lemma_cut_keeps_part(pb0, pb1, s0, s1, qi, kk, x, j, m);
            }
            assert(pb1.used().contains_key(span_of(qi)));
            assert(pb1.used()[span_of(qi)][page_of(qi)] == kk);
            pb1.lemma_view(s1);
            lemma_fewer_unbacked(s1, pb1.span_base(span_of(qi)), qi, nn, pages(kk) as nat);
            lemma_cut_others(pb0, pb1, s0, s1, qi, kk);
            assert(!o.store.pages().contains(qi)) by {
                if o.store.pages().contains(qi) {
                    assert(run_held(pb0, s0, qi, 0));
                }
            }
            assert forall|i: int| 0 <= i < CLASSES implies !(#[trigger] o.classes@[i]).heads().contains(qi) by {
                let ci = o.classes@[i];
                assert(ci.wf(o.store, pb0, s0));
                ci.lemma_heads_held(o.store, pb0, s0);
                if ci.heads().contains(qi) {
                    assert(run_held(pb0, s0, qi, slab_order(ci.class())));
                }
            }
            assert(!o.parts@.contains_key(qi)) by {
                if o.parts@.contains_key(qi) {
                    assert(o.part_ok(s0, qi));
                    assert(run_part(pb0, s0, qi, run_order(o.parts@[qi]), o.parts@[qi]));
                }
            }
        }
        let (ptr, perm) = match self.pb.back_run(src, q, k, n) {
            None => {
                let ghost pb2 = self.pb;
                let ghost s2 = src@;
                self.pb.free_run(src, q);
                proof {
                    let pb3 = self.pb;
                    let s3 = src@;
                    let rf = s2.refusals.last();
                    assert(freed(pb2, pb3, s2, s3, qi));
                    lemma_runs_restored(pb0, pb1, pb2, pb3, s0, s1, s2, s3, qi, kk);
                    assert(pb2.holds(qi));
                    assert forall|x: int, j: nat| #[trigger] run_held(pb0, s0, x, j) && x != qi implies run_held(
                        pb3,
                        s3,
                        x,
                        j,
                    ) by {
                        assert(run_held(pb1, s1, x, j));
                        lemma_recorded_keeps_held(pb1, s1, rf, x, j);
                        assert(run_held(pb2, s2, x, j));
                        lemma_freed_keeps_held(pb2, pb3, s2, s3, qi, x, j);
                    }
                    assert forall|x: int, j: nat, m: nat| #[trigger] run_part(pb0, s0, x, j, m) && x != qi implies run_part(
                        pb3,
                        s3,
                        x,
                        j,
                        m,
                    ) by {
                        assert(run_part(pb1, s1, x, j, m));
                        lemma_recorded_keeps_part(pb1, s1, rf, x, j, m);
                        assert(run_part(pb2, s2, x, j, m));
                        lemma_freed_keeps_part(pb2, pb3, s2, s3, qi, x, j, m);
                    }
                    lemma_others_same(pb1, pb2, s1, s2);
                    lemma_freed_others(pb2, pb3, s2, s2, s3, qi);
                    lemma_others_trans(pb0, pb1, pb2, s0, s1, s2);
                    lemma_others_trans(pb0, pb2, pb3, s0, s2, s3);
                    o.lemma_pb_frame(s0, pb3, s3, qi);
                    assert forall|x: int| #[trigger] self.parts@.contains_key(x) implies self.part_ok(s3, x) by {
                        assert(o.part_ok(s0, x));
                    }
                    assert(self.wf(s3));
                    assert(self.live() =~= o.live());
                    assert(s3.refusals == s2.refusals);
                    assert(cut_run(pb0, pb1, s0, s1, qi, kk));
                    assert(s2 == s1.recorded(rf));
                    assert(freed(pb1, pb3, s1.recorded(rf), s3, qi));
                    assert(part_refused(pb0, pb3, s0, s3, kk, nn));
                }
                return None;
            },
            Some(got) => got,
        };
        self.parts = Ghost(self.parts@.insert(qi, nn));
        proof {
            let pb2 = self.pb;
            let s2 = src@;
            let base = pb1.span_base(span_of(qi));
            assert(s2 == s1.backed_run(base, qi, nn));
            lemma_span_base(pb1, s1, span_of(qi));
            assert forall|x: int, j: nat| #[trigger] run_held(pb0, s0, x, j) && x != qi implies run_held(
                pb2,
                s2,
                x,
                j,
            ) by {
                assert(run_held(pb1, s1, x, j));
                lemma_backed_keeps_held(pb1, s1, base, qi, nn, x, j);
            }
            assert forall|x: int, j: nat, m: nat| #[trigger] run_part(pb0, s0, x, j, m) && x != qi implies run_part(
                pb2,
                s2,
                x,
                j,
                m,
            ) by {
                assert(run_part(pb1, s1, x, j, m));
                lemma_backed_keeps_part(pb1, s1, base, qi, nn, x, j, m);
            }
            assert forall|b: int| #[trigger] s1.spans.contains_key(b) && b != base implies s2.spans.contains_key(b)
                && s2.spans[b] == s1.spans[b] by {}
            lemma_others_at(pb1, pb2, s1, s2, base);
            lemma_others_trans(pb0, pb1, pb2, s0, s1, s2);
            o.lemma_pb_frame(s0, pb2, s2, qi);
            lemma_backed_part(pb1, s1, qi, kk, nn);
            assert(run_part(pb2, s2, qi, kk, nn));
            assert forall|x: int| #[trigger] self.parts@.contains_key(x) implies self.part_ok(s2, x) by {
                if x != qi {
                    assert(o.part_ok(s0, x));
                }
            }
            assert(self.wf(s2));
            lemma_held_bounds(pb2, s2, qi, kk);
            lemma_aligned(qi, qi, PAGE_BYTES as int, align as int);
            assert forall|i: int, y: int|
                0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(y) implies qi + nn * PAGE_BYTES <= y || y
                + class_size(i as nat) <= qi by {
                self.lemma_slot_beside_part(s2, i, y, qi);
            }
            assert forall|x: int| #[trigger] o.parts().contains_key(x) implies qi + nn * PAGE_BYTES <= x || x
                + o.parts()[x] * PAGE_BYTES <= qi by {
                self.lemma_parts_apart(s2, qi, x);
            }
            assert forall|x: int| #[trigger] o.large().contains_key(x) implies qi + nn * PAGE_BYTES <= x || x
                + o.large()[x] * PAGE_BYTES <= qi by {
                self.lemma_part_beside_large(s2, qi, x);
            }
            assert(!o.live().contains(qi)) by {
                if o.large().contains_key(qi) {
                    self.lemma_part_beside_large(s2, qi, qi);
                } else if o.live().contains(qi) && !o.parts().contains_key(qi) {
                    let i = choose|i: int| 0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(qi);
                    self.lemma_slot_beside_part(s2, i, qi, qi);
                }
            }
            assert(self.live() =~= o.live().insert(qi));
            assert(cut_run(o.pb(), pb1, s0, s1, qi, kk) && s2 == s1.backed_run(pb1.span_base(span_of(qi)), qi, nn));
        }
        Some((ptr, perm))
    }

    /// The buddy-run arm of `free`.
    fn free_part<S: SpanSource>(&mut self, src: &mut S, p: *mut u8, size: usize, perm: Tracked<PointsToRaw>)
        requires
            old(self).wf(old(src)@),
            PAGE_BYTES < size <= BLOCK_BYTES,
            old(self).parts().contains_key(p@.addr as int),
            old(self).parts()[p@.addr as int] == pages_for(size as nat),
            perm@.is_range(p@.addr as int, pages_for(size as nat) * PAGE_BYTES),
            perm@.provenance() == old(src)@.provenance,
        ensures
            final(self).wf(final(src)@),
            final(self).spares() == old(self).spares(),
            final(self).live() == old(self).live().remove(p@.addr as int),
            part_free(*old(self), *final(self), old(src)@, final(src)@, p@.addr as int),
    {
        let ghost o = *self;
        let ghost pb0 = self.pb;
        let ghost s0 = src@;
        let ghost y0 = p@.addr as int;
        proof {
            lemma_run_sizes(size as nat);
            assert(o.part_ok(s0, y0));
            pb0.lemma_view(s0);
        }
        let n = (size - 1) / PAGE_BYTES + 1;
        let k = order_for(n);
        let ghost kk = k as nat;
        let ghost nn = n as nat;
        let q = p.addr();
        proof {
            assert(run_part(pb0, s0, y0, kk, nn));
        }
        self.pb.release_run(src, q, k, n, perm);
        let ghost pb1 = self.pb;
        let ghost s1 = src@;
        let ghost base = pb0.span_base(span_of(y0));
        proof {
            lemma_released_part(pb0, s0, y0, kk, nn);
            assert(s1.unbacked(pb1.span_base(span_of(y0)), y0, pages(pb1.used()[span_of(y0)][page_of(y0)]) as nat));
        }
        self.pb.free_run(src, q);
        self.parts = Ghost(self.parts@.remove(y0));
        proof {
            let pb2 = self.pb;
            let s2 = src@;
            assert(freed(pb1, pb2, s1, s2, y0));
            assert(pb1.holds(y0));
            assert forall|x: int, j: nat, m: nat| #[trigger] run_part(pb0, s0, x, j, m) && x != y0 implies run_part(
                pb2,
                s2,
                x,
                j,
                m,
            ) by {
                lemma_released_keeps_part(pb0, s0, y0, nn, x, j, m);
                assert(run_part(pb1, s1, x, j, m));
                lemma_freed_keeps_part(pb1, pb2, s1, s2, y0, x, j, m);
            }
            assert forall|x: int, j: nat| #[trigger] run_held(pb0, s0, x, j) && x != y0 implies run_held(
                pb2,
                s2,
                x,
                j,
            ) by {
                lemma_held_part(pb0, s0, x, j);
                lemma_released_keeps_part(pb0, s0, y0, nn, x, j, pages(j) as nat);
                assert(run_part(pb1, s1, x, j, pages(j) as nat));
                lemma_held_part(pb1, s1, x, j);
                lemma_freed_keeps_held(pb1, pb2, s1, s2, y0, x, j);
            }
            lemma_span_base(pb0, s0, span_of(y0));
            assert forall|b: int| #[trigger] s0.spans.contains_key(b) && b != base implies s1.spans.contains_key(b)
                && s1.spans[b] == s0.spans[b] by {}
            lemma_others_at(pb0, pb1, s0, s1, base);
            lemma_freed_others(pb1, pb2, s1, s1, s2, y0);
            lemma_others_trans(pb0, pb1, pb2, s0, s1, s2);
            o.lemma_pb_frame(s0, pb2, s2, y0);
            assert forall|x: int| #[trigger] self.parts@.contains_key(x) implies self.part_ok(s2, x) by {
                assert(o.part_ok(s0, x));
            }
            assert(self.wf(s2));
            assert(freed(pb0, pb2, s1, s2, y0));
            assert(self.live() =~= o.live().remove(y0)) by {
                assert forall|y: int| #[trigger] self.live().contains(y) == o.live().remove(y0).contains(y) by {
                    if y == y0 {
                        if exists|i: int| 0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(y) {
                            let i = choose|i: int| 0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(y);
                            o.lemma_slot_beside_part(s0, i, y, y0);
                        }
                        if o.large().contains_key(y) {
                            o.lemma_part_beside_large(s0, y0, y);
                        }
                    }
                }
            }
        }
    }

    /// The large arm of `alloc`.
    fn alloc_object<S: SpanSource>(&mut self, src: &mut S, size: usize, align: usize) -> (r: Option<
        (*mut u8, Tracked<PointsToRaw>),
    >)
        requires
            old(self).wf(old(src)@),
            large_layout(size as nat, align as nat),
        ensures
            final(self).wf(final(src)@),
            final(self).spares() == old(self).spares(),
            large_alloc(*old(self), *final(self), old(src)@, final(src)@, size as nat, align as nat, r),
    {
        let ghost o = *self;
        let ghost s0 = src@;
        proof {
            o.pb.lemma_view(s0);
        }
        let r = self.large.alloc_large(src, size);
        proof {
            let s1 = src@;
            let n = pages_for(size as nat);
            match r {
                None => {
                    assert(s1.spans == s0.spans);
                    o.lemma_small_frame(s0, s1);
                    assert forall|x: int| #[trigger] self.parts@.contains_key(x) implies self.part_ok(s1, x) by {
                        assert(o.part_ok(s0, x));
                    }
                    assert(self.live() =~= o.live());
                },
                Some((p, _)) => {
                    let b = p@.addr as int;
                    let bl = blocks_for(n);
                    lemma_blocks_for(n);
                    assert(span_bytes(bl) >= BLOCK_BYTES) by (nonlinear_arith)
                        requires
                            bl >= 1,
                    ;
                    assert(!s0.spans.contains_key(b)) by {
                        if s0.spans.contains_key(b) {
                            assert(s0.apart(b, bl, b));
                            assert(s0.released_span(b).fits(b, s0.spans[b].blocks));
                            assert(s0.spans[b].blocks >= 1);
                            assert(span_bytes(s0.spans[b].blocks) >= BLOCK_BYTES) by (nonlinear_arith)
                                requires
                                    s0.spans[b].blocks >= 1,
                            ;
                        }
                    }
                    assert forall|x: int| #[trigger]
                        o.pb.spans().contains_key(x) && s0.spans.contains_key(x) implies s1.spans.contains_key(x)
                        && s1.spans[x] == s0.spans[x] by {
                        assert(x != b);
                    }
                    o.lemma_small_frame(s0, s1);
                    assert forall|x: int| #[trigger] self.parts@.contains_key(x) implies self.part_ok(s1, x) by {
                        assert(o.part_ok(s0, x));
                    }
                    assert forall|x: int| #[trigger]
                        o.pb.spans().contains_key(x) && s0.spans.contains_key(x) implies s0.apart(b, bl, x) by {}
                    assert(!o.pb.spans().contains_key(b)) by {
                        if o.pb.spans().contains_key(b) {
                            lemma_beside_span(o.pb, s0, b, b, bl);
                        }
                    }
                    assert(self.wf(s1));
                    assert(b % PAGE_BYTES as int == 0) by {
                        vstd::arithmetic::div_mod::lemma_mod_mod(b, PAGE_BYTES as int, BLOCK_PAGES as int);
                    }
                    lemma_aligned(b, b, PAGE_BYTES as int, align as int);
                    assert forall|i: int, y: int|
                        0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(y) implies b + n * PAGE_BYTES
                        <= y || y + class_size(i as nat) <= b by {
                        o.lemma_slot_beside(s0, i, y, b, bl);
                    }
                    assert forall|x: int| #[trigger] o.large().contains_key(x) implies b + n * PAGE_BYTES <= x || x
                        + o.large()[x] * PAGE_BYTES <= b by {
                        o.lemma_large_beside(s0, x);
                        assert(s0.apart(b, bl, x));
                    }
                    assert forall|x: int| #[trigger] o.parts().contains_key(x) implies b + n * PAGE_BYTES <= x || x
                        + o.parts()[x] * PAGE_BYTES <= b by {
                        self.lemma_part_beside_large(s1, x, b);
                    }
                    assert(!o.live().contains(b)) by {
                        if o.parts().contains_key(b) {
                            self.lemma_part_beside_large(s1, b, b);
                        } else if o.live().contains(b) && !o.large().contains_key(b) {
                            let i = choose|i: int| 0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(b);
                            lemma_class(i as nat);
                        }
                    }
                    assert(self.live() =~= o.live().insert(b));
                },
            }
        }
        r
    }

    /// Takes back what `alloc` returned at `p` for the layout of `size` bytes aligned to `align`,
    /// with the permission to its bytes, and never refuses: a slot for a small layout
    /// (`slot_free`), a buddy-run object for a run layout, its pages released and its run freed
    /// (`part_free`), a large object for a large one, its span given back whole (`large_free`).
    pub fn free<S: SpanSource>(
        &mut self,
        src: &mut S,
        p: *mut u8,
        size: usize,
        align: usize,
        perm: Tracked<PointsToRaw>,
    )
        requires
            old(self).wf(old(src)@),
            small_layout(size as nat, align as nat) || run_layout(size as nat, align as nat) || large_layout(
                size as nat,
                align as nat,
            ),
            small_layout(size as nat, align as nat) ==> {
                &&& old(self).classes()[class_for(size as nat, align as nat) as int].live().contains(p@.addr as int)
                &&& perm@.is_range(p@.addr as int, class_size(class_for(size as nat, align as nat)) as int)
            },
            run_layout(size as nat, align as nat) ==> {
                &&& old(self).parts().contains_key(p@.addr as int)
                &&& old(self).parts()[p@.addr as int] == pages_for(size as nat)
                &&& perm@.is_range(p@.addr as int, pages_for(size as nat) * PAGE_BYTES)
            },
            large_layout(size as nat, align as nat) ==> {
                &&& old(self).large().contains_key(p@.addr as int)
                &&& perm@.is_range(p@.addr as int, old(self).large()[p@.addr as int] * PAGE_BYTES)
            },
            perm@.provenance() == old(src)@.provenance,
        ensures
            final(self).wf(final(src)@),
            final(self).spares() == old(self).spares(),
            final(self).live() == old(self).live().remove(p@.addr as int),
            small_layout(size as nat, align as nat) ==> slot_free(
                *old(self),
                *final(self),
                old(src)@,
                final(src)@,
                p@.addr as int,
                size as nat,
                align as nat,
            ),
            run_layout(size as nat, align as nat) ==> part_free(
                *old(self),
                *final(self),
                old(src)@,
                final(src)@,
                p@.addr as int,
            ),
            large_layout(size as nat, align as nat) ==> large_free(
                *old(self),
                *final(self),
                old(src)@,
                final(src)@,
                p@.addr as int,
            ),
    {
        if size <= PAGE_BYTES {
            self.free_slot(src, p, size, align, perm);
        } else if size <= BLOCK_BYTES {
            self.free_part(src, p, size, perm);
        } else {
            self.free_object(src, p, perm);
        }
    }

    /// The slab arm of `free`.
    fn free_slot<S: SpanSource>(
        &mut self,
        src: &mut S,
        p: *mut u8,
        size: usize,
        align: usize,
        perm: Tracked<PointsToRaw>,
    )
        requires
            old(self).wf(old(src)@),
            small_layout(size as nat, align as nat),
            old(self).classes()[class_for(size as nat, align as nat) as int].live().contains(p@.addr as int),
            perm@.is_range(p@.addr as int, class_size(class_for(size as nat, align as nat)) as int),
            perm@.provenance() == old(src)@.provenance,
        ensures
            final(self).wf(final(src)@),
            final(self).spares() == old(self).spares(),
            final(self).live() == old(self).live().remove(p@.addr as int),
            slot_free(*old(self), *final(self), old(src)@, final(src)@, p@.addr as int, size as nat, align as nat),
    {
        let c = class_index(size, align);
        let ghost ci = c as int;
        let ghost o = *self;
        let ghost oc = self.classes@[ci];
        let ghost s0 = src@;
        let ghost y0 = p@.addr as int;
        let ghost a = oc.slab_of(y0);
        let ghost b = oc.slabs()[a].base()@.addr as int;
        proof {
            assert(oc.wf(o.store, o.pb, s0));
            assert(oc.slabs().contains_key(a) && oc.slabs()[a].holds(y0));
            oc.lemma_head_of(a);
            assert(!o.large().contains_key(y0)) by {
                if o.large().contains_key(y0) {
                    o.lemma_large_beside(s0, y0);
                    o.lemma_slot_beside(s0, ci, y0, y0, blocks_for(o.large()[y0]));
                    lemma_class(c as nat);
                }
            }
            assert(!o.parts().contains_key(y0)) by {
                if o.parts().contains_key(y0) {
                    o.lemma_slot_beside_part(s0, ci, y0, y0);
                }
            }
        }
        self.classes[c].free_small(&mut self.store, &mut self.pb, src, p, perm);
        proof {
            let nc = self.classes@[ci];
            let s1 = src@;
            assert(self.classes@ == o.classes@.update(ci, nc));
            assert forall|i: int| 0 <= i < CLASSES implies (#[trigger] self.classes@[i]).class() == i by {
                assert(o.classes@[i].class() == i);
            }
            assert forall|i: int| 0 <= i < CLASSES implies (#[trigger] self.classes@[i]).wf(self.store, self.pb, s1) by {
                if i != ci {
                    let oi = o.classes@[i];
                    assert(oi.wf(o.store, o.pb, s0));
                    if only_live(oc.slabs()[a], y0) {
                        assert(apart(oc, oi));
                        assert(oc.slabs().dom().contains(a));
                        assert(oc.heads().contains(b));
                        oi.lemma_frame_emptied(o.store, o.pb, s0, self.store, self.pb, s1, a, b);
                    }
                }
            }
            assert forall|i: int, j: int|
                0 <= i < CLASSES && 0 <= j < CLASSES && i != j implies #[trigger] apart(
                self.classes@[i],
                self.classes@[j],
            ) by {
                assert(apart(o.classes@[i], o.classes@[j]));
            }
            o.large.lemma_view(s0);
            assert forall|x: int| #[trigger] self.large.objects().contains_key(x) implies {
                &&& s1.spans.contains_key(x)
                &&& s1.spans[x] == s0.spans[x]
                &&& !self.pb.spans().contains_key(x)
            } by {
                assert(s0.spans.contains_key(x));
                assert(!o.pb.spans().contains_key(x));
            }
            assert(s1.provenance == s0.provenance);
            self.large.lemma_frame(s0, s1);
            assert forall|x: int| #[trigger] self.parts@.contains_key(x) implies self.part_ok(s1, x) by {
                assert(o.part_ok(s0, x));
                let n = o.parts@[x];
                assert(run_part(o.pb, s0, x, run_order(n), n));
                assert(!oc.heads().contains(x));
                assert forall|i: int| 0 <= i < CLASSES implies !(#[trigger] self.classes@[i]).heads().contains(x) by {
                    assert(!o.classes@[i].heads().contains(x));
                }
            }
            assert(self.wf(s1));
            assert(self.live() =~= o.live().remove(y0)) by {
                assert forall|y: int| #[trigger] self.live().contains(y) == o.live().remove(y0).contains(y) by {
                    if self.live().contains(y) && !self.large().contains_key(y) && !self.parts().contains_key(y) {
                        let i = choose|i: int| 0 <= i < CLASSES && #[trigger] self.classes()[i].live().contains(y);
                        assert(o.classes()[i].live().contains(y));
                        if i != ci && y == y0 {
                            o.lemma_live_apart(s0, ci, i, y0, y);
                            lemma_class(ci as nat);
                            lemma_class(i as nat);
                        }
                    }
                    if o.live().contains(y) && y != y0 && !o.large().contains_key(y) && !o.parts().contains_key(y) {
                        let i = choose|i: int| 0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(y);
                        assert(self.classes()[i].live().contains(y));
                    }
                }
            }
        }
    }

    /// The large arm of `free`.
    fn free_object<S: SpanSource>(&mut self, src: &mut S, p: *mut u8, perm: Tracked<PointsToRaw>)
        requires
            old(self).wf(old(src)@),
            old(self).large().contains_key(p@.addr as int),
            perm@.is_range(p@.addr as int, old(self).large()[p@.addr as int] * PAGE_BYTES),
            perm@.provenance() == old(src)@.provenance,
        ensures
            final(self).wf(final(src)@),
            final(self).spares() == old(self).spares(),
            final(self).live() == old(self).live().remove(p@.addr as int),
            large_free(*old(self), *final(self), old(src)@, final(src)@, p@.addr as int),
    {
        let ghost o = *self;
        let ghost s0 = src@;
        let ghost y0 = p@.addr as int;
        proof {
            o.pb.lemma_view(s0);
            o.lemma_large_beside(s0, y0);
        }
        self.large.free_large(src, p.addr(), perm);
        proof {
            let s1 = src@;
            assert forall|x: int| #[trigger]
                o.pb.spans().contains_key(x) && s0.spans.contains_key(x) implies s1.spans.contains_key(x)
                && s1.spans[x] == s0.spans[x] by {
                assert(x != y0);
            }
            o.lemma_small_frame(s0, s1);
            assert forall|x: int| #[trigger] self.parts@.contains_key(x) implies self.part_ok(s1, x) by {
                assert(o.part_ok(s0, x));
            }
            assert(self.wf(s1));
            assert(!o.parts().contains_key(y0)) by {
                if o.parts().contains_key(y0) {
                    o.lemma_part_beside_large(s0, y0, y0);
                }
            }
            assert(self.live() =~= o.live().remove(y0)) by {
                assert forall|y: int| #[trigger] self.live().contains(y) == o.live().remove(y0).contains(y) by {
                    if exists|i: int| 0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(y) {
                        let i = choose|i: int| 0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(y);
                        o.lemma_slot_beside(s0, i, y, y0, blocks_for(o.large()[y0]));
                        lemma_class(i as nat);
                        assert(self.classes()[i].live().contains(y));
                    }
                }
            }
        }
    }
}

} // verus!
