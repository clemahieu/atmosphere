// SPDX-License-Identifier: MIT
//! The heap: one size class per class, over one record store and one page buddy, under one
//! invariant.
//!
//! - `wf(src)` is the invariant over the source's view `src`: the page buddy and the store are well
//!   formed over it, class `i` is the `i`-th size class and well formed over them, and no two
//!   classes share a head or a record, so a live slot of one shares no byte with a live slot of
//!   another.
//! - `live()` is every class's live slots.
//! - `alloc(src, size, align)`, for a layout of at most the page whose alignment divides the page,
//!   takes a slot of `class_for(size, align)`, the first class whose slot holds `size` bytes and is a
//!   multiple of `align`. It refuses exactly as that class's `alloc_small` does: only when none of
//!   its slabs has a free slot and the source refused one request in this call (`slab_refused`).
//!   Otherwise the slot is aligned to `align`, apart from every live slot of every class, and joins
//!   the live slots; alloc says nothing of its bytes.
//! - `free(src, p, size, align, perm)` takes back the live slot at `p` of that layout and never
//!   refuses. A slab left with no live slot is retired, its run released and freed to the page
//!   buddy, which gives back a span left with no run unless it keeps it as a spare
//!   (`emptied_slab`).
use vstd::prelude::*;
use vstd::raw_ptr::*;

use crate::arch::*;
use crate::class::*;
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

/// Two classes share no head and no record.
pub open spec fn apart(a: SizeClass, b: SizeClass) -> bool {
    &&& a.heads().disjoint(b.heads())
    &&& a.slabs().dom().disjoint(b.slabs().dom())
}

/// Every record of `n` was one of `o`'s or was not taken in `store`.
pub open spec fn records_grew(o: SizeClass, n: SizeClass, store: RecordStore) -> bool {
    forall|a: int| #[trigger] n.slabs().contains_key(a) ==> o.slabs().contains_key(a) || !store.taken().contains(a)
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

/// The heap: a size class per class over one record store and one page buddy.
pub struct Heap {
    /// Class `i` at index `i`.
    classes: [SizeClass; CLASSES],
    /// The records of every class's slabs.
    store: RecordStore,
    /// The runs of every class's slabs and the store's record pages.
    pb: PageBuddy,
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

    /// The idle spans the page buddy keeps rather than give back.
    pub closed spec fn spares(&self) -> nat {
        self.pb.spares()
    }

    /// The live slots of every class.
    pub open spec fn live(&self) -> ISet<int> {
        ISet::new(|y: int| exists|i: int| 0 <= i < CLASSES && #[trigger] self.classes()[i].live().contains(y))
    }

    /// The page buddy and the store are well formed over `src`; class `i` is the `i`-th class and
    /// well formed over them; and no two classes share a head or a record.
    pub closed spec fn wf(&self, src: SourceView) -> bool {
        &&& self.classes@.len() == CLASSES
        &&& self.pb.wf(src)
        &&& self.store.wf(self.pb, src)
        &&& forall|i: int| 0 <= i < CLASSES ==> (#[trigger] self.classes@[i]).class() == i
        &&& forall|i: int| 0 <= i < CLASSES ==> (#[trigger] self.classes@[i]).wf(self.store, self.pb, src)
        &&& forall|i: int, j: int|
            0 <= i < CLASSES && 0 <= j < CLASSES && i != j ==> #[trigger] apart(self.classes@[i], self.classes@[j])
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

    /// The heap with no slab, keeping `spares` idle spans, well formed over every well-formed
    /// source's view.
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
        let r = Heap { classes, store: RecordStore::new(), pb: PageBuddy::new(spares) };
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
            }
            assert(r.live() =~= ISet::<int>::empty());
        }
        r
    }

    /// An object of `size` bytes aligned to `align`, a slot of `class_for(size, align)`; or a
    /// refusal, only when none of that class's slabs had a free slot and the source refused one
    /// request in this call (`slab_refused`), which leaves every class as it was. Every other class
    /// is as it was either way. The slot is apart from every slot live before, and alloc says
    /// nothing of its bytes.
    pub fn alloc<S: SpanSource>(&mut self, src: &mut S, size: usize, align: usize) -> (r: Option<
        (*mut u8, Tracked<PointsToRaw>),
    >)
        requires
            old(self).wf(old(src)@),
            small_layout(size as nat, align as nat),
        ensures
            final(self).wf(final(src)@),
            final(self).spares() == old(self).spares(),
            ({
                let c = class_for(size as nat, align as nat) as int;
                let n = class_size(c as nat);
                &&& c < CLASSES
                &&& size <= n
                &&& forall|i: int| #![trigger final(self).classes()[i]]
                    0 <= i < CLASSES && i != c ==> final(self).classes()[i] == old(self).classes()[i]
                &&& match r {
                    None => {
                        &&& forall|a: int| #[trigger]
                            old(self).classes()[c].slabs().contains_key(a) ==> old(self).classes()[c].slabs()[a].free_slots()
                                == Set::<int>::empty()
                        &&& final(self).classes() == old(self).classes()
                        &&& final(self).live() == old(self).live()
                        &&& slab_refused(old(self).store(), old(self).pb(), old(src)@, final(src)@, slab_order(c as nat))
                    },
                    Some((p, perm)) => {
                        &&& perm@.is_range(p@.addr as int, n as int)
                        &&& perm@.provenance() == old(src)@.provenance
                        &&& p@.provenance == old(src)@.provenance
                        &&& p@.addr % align == 0
                        &&& !old(self).live().contains(p@.addr as int)
                        &&& final(self).live() == old(self).live().insert(p@.addr as int)
                        &&& final(self).classes()[c].live() == old(self).classes()[c].live().insert(p@.addr as int)
                        &&& forall|i: int, y: int|
                            0 <= i < CLASSES && #[trigger] old(self).classes()[i].live().contains(y) ==> p@.addr + n <= y
                                || y + class_size(i as nat) <= p@.addr
                    },
                }
            }),
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
                    assert(!o.live().contains(y0)) by {
                        if o.live().contains(y0) {
                            let i = choose|i: int| 0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(y0);
                            lemma_class(i as nat);
                        }
                    }
                    assert(self.live() =~= o.live().insert(y0)) by {
                        assert forall|y: int| #[trigger] self.live().contains(y) == o.live().insert(y0).contains(y) by {
                            if self.live().contains(y) {
                                let i = choose|i: int| 0 <= i < CLASSES && #[trigger] self.classes()[i].live().contains(y);
                                if i != ci {
                                    assert(o.classes()[i].live().contains(y));
                                } else if y != y0 {
                                    assert(o.classes()[ci].live().contains(y));
                                }
                            }
                            if o.live().contains(y) {
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

    /// Takes back the live slot at `p` of a layout `alloc` took it for, with the permission to its
    /// bytes, and never refuses. Every other class is as it was. A slab left with a live slot keeps
    /// the store, the page buddy and the source as they were; a slab left with none is retired:
    /// its run released and freed to the page buddy, which gives back a span left with no run
    /// unless it keeps it as a spare, and its record put back in the store (`emptied_slab`).
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
            small_layout(size as nat, align as nat),
            old(self).classes()[class_for(size as nat, align as nat) as int].live().contains(p@.addr as int),
            perm@.is_range(p@.addr as int, class_size(class_for(size as nat, align as nat)) as int),
            perm@.provenance() == old(src)@.provenance,
        ensures
            final(self).wf(final(src)@),
            final(self).spares() == old(self).spares(),
            final(self).live() == old(self).live().remove(p@.addr as int),
            ({
                let c = class_for(size as nat, align as nat) as int;
                let oc = old(self).classes()[c];
                let a = oc.slab_of(p@.addr as int);
                let b = oc.slabs()[a].base()@.addr as int;
                &&& forall|i: int| #![trigger final(self).classes()[i]]
                    0 <= i < CLASSES && i != c ==> final(self).classes()[i] == old(self).classes()[i]
                &&& final(self).classes()[c].live() == oc.live().remove(p@.addr as int)
                &&& if only_live(oc.slabs()[a], p@.addr as int) {
                    emptied_slab(
                        old(self).store(),
                        final(self).store(),
                        old(self).pb(),
                        final(self).pb(),
                        old(src)@,
                        final(src)@,
                        a,
                        b,
                        slab_order(c as nat),
                    )
                } else {
                    &&& final(self).store() == old(self).store()
                    &&& final(self).pb() == old(self).pb()
                    &&& final(src)@ == old(src)@
                }
            }),
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
            assert(self.live() =~= o.live().remove(y0)) by {
                assert forall|y: int| #[trigger] self.live().contains(y) == o.live().remove(y0).contains(y) by {
                    if self.live().contains(y) {
                        let i = choose|i: int| 0 <= i < CLASSES && #[trigger] self.classes()[i].live().contains(y);
                        assert(o.classes()[i].live().contains(y));
                        if i != ci && y == y0 {
                            o.lemma_live_apart(s0, ci, i, y0, y);
                            lemma_class(ci as nat);
                            lemma_class(i as nat);
                        }
                    }
                    if o.live().contains(y) && y != y0 {
                        let i = choose|i: int| 0 <= i < CLASSES && #[trigger] o.classes()[i].live().contains(y);
                        assert(self.classes()[i].live().contains(y));
                    }
                }
            }
        }
    }
}

} // verus!
