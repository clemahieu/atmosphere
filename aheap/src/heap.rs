// SPDX-License-Identifier: MIT
//! The heap: one size class per class over one record store and one page buddy, and the
//! large-object map, under one invariant.
//!
//! - `wf(src)` is the invariant over the source's view `src`: the page buddy and the store are well
//!   formed over it, class `i` is the `i`-th size class and well formed over them, no two classes
//!   share a head or a record, so a live slot of one shares no byte with a live slot of another,
//!   and the large-object map is well formed over it, each large object's span one the page buddy
//!   does not hold. The page buddy's callers leave every span it does not hold as it was, and the
//!   map leaves every span it does not hold as it was, so each arm keeps the other's invariant.
//! - `live()` is every class's live slots and every large object's base.
//! - `alloc(src, size, align)`, for a layout of at most the page whose alignment divides the page,
//!   takes a slot of `class_for(size, align)`, the first class whose slot holds `size` bytes and is a
//!   multiple of `align`. It refuses exactly as that class's `alloc_small` does: only when none of
//!   its slabs has a free slot and the source refused one request in this call (`slab_refused`).
//!   Otherwise the slot is aligned to `align` and joins the live slots (`slot_alloc`). For a layout
//!   of more than one block whose alignment divides the page, it takes a large object of
//!   `pages_for(size)` pages, a span of its own, and refuses exactly as `alloc_large` does: only
//!   when the source refused the span's reserve or the back of its pages in this call
//!   (`large_refused`), with nothing else changed. Otherwise the object is block-aligned, so aligned
//!   to `align`, and joins the large objects (`large_alloc`). Either way what it returns is apart
//!   from every live slot and every large object, and alloc says nothing of its bytes.
//! - `free(src, p, size, align, perm)` takes back what alloc returned at `p` for that layout and
//!   never refuses. A slab left with no live slot is retired, its run released and freed to the
//!   page buddy, which gives back a span left with no run unless it keeps it as a spare
//!   (`emptied_slab`). A large object's span is given back whole (`large_free`).
use vstd::prelude::*;
use vstd::raw_ptr::*;

use crate::arch::*;
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
/// way. The slot is aligned to `align` and apart from every slot and large object live before.
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
            &&& forall|i: int, y: int|
                0 <= i < CLASSES && #[trigger] h0.classes()[i].live().contains(y) ==> p@.addr + n <= y || y
                    + class_size(i as nat) <= p@.addr
            &&& forall|b: int| #[trigger]
                h0.large().contains_key(b) ==> p@.addr + n <= b || b + h0.large()[b] * PAGE_BYTES <= p@.addr
        },
    }
}

/// `alloc` of a large layout went from `h0` to `h1`, and the source's view from `s0` to `s1`,
/// returning `r`: a large object of `pages_for(size)` pages, or a refusal only when the source
/// refused the reserve of its span or the back of its pages in the call (`large_refused`), with
/// nothing else changed. The classes, the store and the page buddy are as they were either way.
/// The object is a new span reserved and backed, aligned to `align`, and apart from every slot and
/// large object live before.
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
                h0.large().contains_key(x) ==> b + n * PAGE_BYTES <= x || x + h0.large()[x] * PAGE_BYTES <= b
        },
    }
}

/// `free` of the slot at `p` of a small layout went from `h0` to `h1`, and the source's view from
/// `s0` to `s1`: every other class and the large objects are as they were, and a slab left with a
/// live slot keeps the store, the page buddy and the source as they were; a slab left with none is
/// retired (`emptied_slab`).
pub open spec fn slot_free(h0: Heap, h1: Heap, s0: SourceView, s1: SourceView, p: int, size: nat, align: nat) -> bool {
    let c = class_for(size, align) as int;
    let oc = h0.classes()[c];
    let a = oc.slab_of(p);
    let b = oc.slabs()[a].base()@.addr as int;
    &&& h1.large() == h0.large()
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
/// `s1`: the classes, the store and the page buddy are as they were, and the object's span is
/// given back whole.
pub open spec fn large_free(h0: Heap, h1: Heap, s0: SourceView, s1: SourceView, p: int) -> bool {
    &&& h1.classes() == h0.classes()
    &&& h1.store() == h0.store()
    &&& h1.pb() == h0.pb()
    &&& h1.large() == h0.large().remove(p)
    &&& s1 == s0.released_span(p)
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

/// The heap: a size class per class over one record store and one page buddy, and the
/// large-object map.
pub struct Heap {
    /// Class `i` at index `i`.
    classes: [SizeClass; CLASSES],
    /// The records of every class's slabs.
    store: RecordStore,
    /// The runs of every class's slabs and the store's record pages.
    pb: PageBuddy,
    /// The large objects, a span each.
    large: LargeMap,
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

    /// The idle spans the page buddy keeps rather than give back.
    pub closed spec fn spares(&self) -> nat {
        self.pb.spares()
    }

    /// The live slots of every class and the bases of the large objects.
    pub open spec fn live(&self) -> ISet<int> {
        ISet::new(
            |y: int|
                (exists|i: int| 0 <= i < CLASSES && #[trigger] self.classes()[i].live().contains(y))
                    || self.large().contains_key(y),
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

    /// The slab arm's invariant, and the large-object map well formed over `src`, each large
    /// object's span one the page buddy does not hold.
    pub closed spec fn wf(&self, src: SourceView) -> bool {
        &&& self.small_wf(src)
        &&& self.large.wf(src)
        &&& forall|b: int| #[trigger] self.large.objects().contains_key(b) ==> !self.pb.spans().contains_key(b)
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
    {
        let pb = self.pb;
        assert forall|x: int, k: nat| #[trigger] run_held(pb, s, x, k) implies run_held(pb, t, x, k) by {
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
        let r = Heap { classes, store: RecordStore::new(), pb: PageBuddy::new(spares), large: LargeMap::new() };
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
            }
            assert(r.live() =~= ISet::<int>::empty());
        }
        r
    }

    /// An object of `size` bytes aligned to `align`: a slot of `class_for(size, align)` for a small
    /// layout (`slot_alloc`), a large object of `pages_for(size)` pages for a large one
    /// (`large_alloc`); or a refusal, only when the source refused a request in this call.
    pub fn alloc<S: SpanSource>(&mut self, src: &mut S, size: usize, align: usize) -> (r: Option<
        (*mut u8, Tracked<PointsToRaw>),
    >)
        requires
            old(self).wf(old(src)@),
            small_layout(size as nat, align as nat) || large_layout(size as nat, align as nat),
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
                    assert(!o.live().contains(y0)) by {
                        if o.large().contains_key(y0) {
                            self.lemma_large_beside(s1, y0);
                        } else if o.live().contains(y0) {
                            let i = choose|i: int| 0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(y0);
                            lemma_class(i as nat);
                        }
                    }
                    assert(self.live() =~= o.live().insert(y0)) by {
                        assert forall|y: int| #[trigger] self.live().contains(y) == o.live().insert(y0).contains(y) by {
                            if self.live().contains(y) && !self.large().contains_key(y) {
                                let i = choose|i: int| 0 <= i < CLASSES && #[trigger] self.classes()[i].live().contains(y);
                                if i != ci {
                                    assert(o.classes()[i].live().contains(y));
                                } else if y != y0 {
                                    assert(o.classes()[ci].live().contains(y));
                                }
                            }
                            if o.live().contains(y) && !o.large().contains_key(y) {
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
                    assert(!o.live().contains(b)) by {
                        if o.live().contains(b) && !o.large().contains_key(b) {
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
    /// (`slot_free`), a large object for a large one, its span given back whole (`large_free`).
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
            small_layout(size as nat, align as nat) || large_layout(size as nat, align as nat),
            small_layout(size as nat, align as nat) ==> {
                &&& old(self).classes()[class_for(size as nat, align as nat) as int].live().contains(p@.addr as int)
                &&& perm@.is_range(p@.addr as int, class_size(class_for(size as nat, align as nat)) as int)
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
            assert(self.live() =~= o.live().remove(y0)) by {
                assert forall|y: int| #[trigger] self.live().contains(y) == o.live().remove(y0).contains(y) by {
                    if self.live().contains(y) && !self.large().contains_key(y) {
                        let i = choose|i: int| 0 <= i < CLASSES && #[trigger] self.classes()[i].live().contains(y);
                        assert(o.classes()[i].live().contains(y));
                        if i != ci && y == y0 {
                            o.lemma_live_apart(s0, ci, i, y0, y);
                            lemma_class(ci as nat);
                            lemma_class(i as nat);
                        }
                    }
                    if o.live().contains(y) && y != y0 && !o.large().contains_key(y) {
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
            assert(self.wf(s1));
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
