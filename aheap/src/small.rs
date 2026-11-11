// SPDX-License-Identifier: MIT
//! One size class: its slabs on two lists, the slabs with a free slot and the full ones, and the
//! permission to each free slot of them.
//!
//! The class keeps its slabs' records on two class lists, `partial` and `full` (StarMalloc, arXiv
//! 2403.09435, section 2.2), and holds the permission to the free slots of all of them in one map,
//! so each slab's ownership of its slots (`Slab::owns`) is stated over the class's map. The class
//! owns neither the record store, the page buddy nor the source. Its invariant, `wf(store, pb,
//! src)`, is stated over theirs: each slab's record is taken in the store, and each slab's run is a
//! run of the class's slab order that the page buddy holds allocated, every page backed
//! (`run_held`), and is no record page. A change to the three that keeps every record taken, every
//! held run held and none of them a record page, and the provenance (`kept`), keeps the invariant
//! (`lemma_frame`), so several classes can share them.
//!
//! The heads of the slab runs are `heads()`, each a run of the class's slab order that the page
//! buddy holds (`lemma_heads_held`). Each live slot lies inside the run at one of them
//! (`lemma_live_in_run`), so it is apart from every run the page buddy holds at another head
//! (`lemma_live_apart_from_run`), and from every live slot of a second class whose heads are
//! others (`lemma_classes_apart`). A class starts with no head and gains one only with a new slab,
//! whose run the page buddy held as no run before, so two classes over one page buddy keep their
//! heads apart.
//!
//! - `new(c)` is class `c` with no slab and no head.
//! - `alloc_small(store, pb, src)` takes a slot from the first slab with a free one, which goes to
//!   the full list when it fills, and changes neither the store, the page buddy nor the source.
//!   With no such slab it cuts a run of the slab order, backs it, makes it a slab and takes a
//!   record for it from the store, last, so a refusal gives back only the run. It refuses exactly
//!   when no slab has a free slot and the source refused, in this call, one request
//!   (`slab_refused`): for the slab's run, a run span only when no held span had a free block of
//!   the slab order, then the back of the run; for its record, only when the store was full, a run
//!   span only when no held span had a free page once the slab's run was cut, or the back of the
//!   record page (`run_refused`); then the class, the store's records and the page buddy's runs are as they
//!   were. Otherwise it returns a slot of the class's size, aligned to SLOT_MIN, with the
//!   permission to its bytes, apart from every slot live before. Either way it keeps what every
//!   class over the same store, page buddy and source stands on (`kept`).
//! - `free_small(store, pb, src, p, perm)` takes back the live slot at `p` and never refuses. Its
//!   slab (`slab_of`) goes to the partial list while a slot of it is live, keeping its base and
//!   holding what it held but `p`, and every other slab, the heads, the store, the page buddy and
//!   the source are as they were. A slab whose only live slot was `p` (`only_live`) is
//!   retired: its run released and freed, so the page buddy no longer holds it, and its record put
//!   back in the store, its record page given back when no other record lies on it, and its base
//!   leaves the heads; the page
//!   buddy's runs and the source change by those alone (`emptied_slab`), so `new_slab` then
//!   `emptied_slab` leaves the page buddy's runs as they were. Every other record stays taken and
//!   every other run held that is no record page stays held (`kept_but`), so a second class with
//!   neither that record (`records_apart`) nor that head keeps its invariant
//!   (`lemma_frame_emptied`).
use vstd::prelude::*;
use vstd::raw_ptr::*;

use crate::arch::*;
use crate::buddy::*;
use crate::class::*;
use crate::list::*;
use crate::page::*;
use crate::record::*;
use crate::slab::*;
use crate::source::*;

verus! {

broadcast use {group_raw_ptr_axioms, vstd::set_lib::range_set_properties};

/// `after` is `before` with one refusal recorded, of a request `alloc_small` makes for a new slab
/// whose run is of order `k`, from the record store `store` and the page buddy `pb`: for the slab's
/// run, the reserve of a run span or the back of its metadata page, only when `pb` had no free block
/// of order `k`; or a request made after `pb` cut that run (`run_refused`).
pub open spec fn slab_refused(store: RecordStore, pb: PageBuddy, before: SourceView, after: SourceView, k: nat) -> bool {
    let r = after.refusals.last();
    &&& after.provenance == before.provenance
    &&& after.refusals == before.refusals.push(r)
    &&& {
        ||| !pb.fits(k) && span_refusal(before, r)
        ||| exists|mid: PageBuddy, s: SourceView, q: int| #[trigger]
            cut_run(pb, mid, before, s, q, k) && run_refused(store, mid, s, r, q, k)
    }
}

/// The refusal `r` is of a request `alloc_small` makes once the page buddy, then `pb`, has cut the
/// slab's run of order `k` at `q` and the source's view is `s`: the back of the run's pages, while
/// the source held the spans `s` holds; or, only when the store `store` was full, a request for a
/// record page once the run was backed: the reserve of a run span or the back of its metadata page,
/// only when `pb` had no free block of order 0, or the back of one page.
pub open spec fn run_refused(store: RecordStore, pb: PageBuddy, s: SourceView, r: Refusal, q: int, k: nat) -> bool {
    let b = pb.span_base(span_of(q));
    ||| r.request == (Request::Back { span: b, start: q, pages: pages(k) as nat }) && r.spans == s.spans
    ||| store.full() && !pb.fits(0) && span_refusal(s.backed_run(b, q, pages(k) as nat), r)
    ||| store.full() && match r.request {
        Request::Back { pages: n, .. } => n == 1,
        Request::Reserve { .. } => false,
    }
}

/// The store, the page buddy and the source's view went from `store`, `pb` and `src` to `store2`,
/// `pb2` and `src2` keeping what a size class stands on: the provenance, every record taken, and
/// every run held, none of them made a record page.
pub open spec fn kept(
    store: RecordStore,
    pb: PageBuddy,
    src: SourceView,
    store2: RecordStore,
    pb2: PageBuddy,
    src2: SourceView,
) -> bool {
    &&& src2.provenance == src.provenance
    &&& forall|a: int| #[trigger] store.taken().contains(a) ==> store2.taken().contains(a)
    &&& forall|x: int, k: nat| #[trigger]
        run_held(pb, src, x, k) ==> {
            &&& run_held(pb2, src2, x, k)
            &&& store2.pages().contains(x) ==> store.pages().contains(x)
        }
}

/// The store, the page buddy and the source's view went from `store`, `pb` and `src` to `store2`,
/// `pb2` and `src2` keeping what a size class stands on, but for the record `a` and the run at `b`:
/// the provenance, every other record taken, and every other run held that is no record page, none
/// of them made one. A class that holds neither `a` nor a slab run at `b` keeps its invariant
/// across it (`lemma_frame_emptied`), as across `free_small` retiring another class's slab.
pub open spec fn kept_but(
    store: RecordStore,
    pb: PageBuddy,
    src: SourceView,
    store2: RecordStore,
    pb2: PageBuddy,
    src2: SourceView,
    a: int,
    b: int,
) -> bool {
    &&& src2.provenance == src.provenance
    &&& forall|r: int| #[trigger] store.taken().contains(r) && r != a ==> store2.taken().contains(r)
    &&& forall|x: int, k: nat| #[trigger]
        run_held(pb, src, x, k) && x != b && !store.pages().contains(x) ==> {
            &&& run_held(pb2, src2, x, k)
            &&& !store2.pages().contains(x)
        }
}

/// The page buddy went from `before` to `after`, and the source from `s` to `t`, by cutting the run
/// of order `k` at `q`, from a held span or a new one, and backing its pages.
pub open spec fn took_run(before: PageBuddy, after: PageBuddy, s: SourceView, t: SourceView, q: int, k: nat) -> bool {
    let c = span_of(q);
    let m = if before.spans().contains_key(c) {
        s
    } else {
        s.reserved(c, SPAN_BLOCKS as nat).backed_run(c, meta_page(c), 1)
    };
    &&& cut_run(before, after, s, m, q, k)
    &&& t == m.backed_run(after.span_base(c), q, pages(k) as nat)
}

/// The store went from `st0` to `st1`, the page buddy from `pb0` to `pb1` and the source from `s0`
/// to `s1` by `alloc_small` making a new slab whose record is `a` and whose run is the run of order
/// `k` at `x`: the run cut and backed, then the record taken, from a new record page cut and backed
/// when every record was in use. The store's records gain `a`, the page buddy's runs gain the slab's
/// run and that record page's, and the source changes by those cuts and backs alone.
pub open spec fn new_slab(
    st0: RecordStore,
    st1: RecordStore,
    pb0: PageBuddy,
    pb1: PageBuddy,
    s0: SourceView,
    s1: SourceView,
    a: int,
    x: int,
    k: nat,
) -> bool {
    &&& !st0.taken().contains(a)
    &&& st1.taken() == st0.taken().insert(a)
    &&& if st0.full() {
        &&& !st0.pages().contains(record_page(a))
        &&& st1.pages() == st0.pages().insert(record_page(a))
        &&& runs(pb1.used()) == runs(with_run(with_run(pb0.used(), x, k), record_page(a), 0))
    } else {
        &&& st1.pages() == st0.pages()
        &&& runs(pb1.used()) == runs(with_run(pb0.used(), x, k))
    }
    &&& exists|pbm: PageBuddy, sm: SourceView| #[trigger]
        took_run(pb0, pbm, s0, sm, x, k) && if st0.full() {
            took_page(pbm, pb1, sm, s1, record_page(a))
        } else {
            pb1 == pbm && s1 == sm
        }
}

/// Another record than `a` that the store `st` has taken lies on `a`'s record page.
pub open spec fn page_shared(st: RecordStore, a: int) -> bool {
    exists|y: int| #[trigger] st.taken().contains(y) && y != a && record_page(y) == record_page(a)
}

/// The store went from `st0` to `st1`, the page buddy from `pb0` to `pb1` and the source from `s0`
/// to `s1` by `free_small` retiring the slab whose record is `a` and whose run is the run of order
/// `k` at `x`: the run released and freed, then the record put back, its record page released and
/// freed too when no other record taken lies on it. The store's records lose `a`, the page buddy's
/// runs lose the slab's run and that record page's, and the source changes by those releases and
/// frees alone. `alloc_small`'s `new_slab` followed by this is the page buddy's runs as they were.
pub open spec fn emptied_slab(
    st0: RecordStore,
    st1: RecordStore,
    pb0: PageBuddy,
    pb1: PageBuddy,
    s0: SourceView,
    s1: SourceView,
    a: int,
    x: int,
    k: nat,
) -> bool {
    &&& st0.taken().contains(a)
    &&& st1.taken() == st0.taken().remove(a)
    &&& if page_shared(st0, a) {
        &&& st1.pages() == st0.pages()
        &&& runs(pb1.used()) == runs(without_run(pb0.used(), x))
    } else {
        &&& st1.pages() == st0.pages().remove(record_page(a))
        &&& runs(pb1.used()) == runs(without_run(without_run(pb0.used(), x), record_page(a)))
    }
    &&& exists|pbm: PageBuddy, sm: SourceView| #[trigger]
        freed(pb0, pbm, s0.released_run(pb0.span_base(span_of(x)), x, pages(k) as nat), sm, x) && if page_shared(
            st0,
            a,
        ) {
            pb1 == pbm && s1 == sm
        } else {
            gave_back(pbm, pb1, sm, s1, record_page(a))
        }
}

/// The live slots of the slabs of `m`.
pub open spec fn live_of(m: Map<int, Slab>) -> ISet<int> {
    ISet::new(|x: int| exists|a: int| #[trigger] m.contains_key(a) && m[a].holds(x))
}

/// The slab `s`, whose record is at `a`, is one of class `c`: its record taken in the store, its
/// slots of the class's size, its run a run of the class's slab order the page buddy holds, every
/// page backed, and no record page; and it owns its slots' permissions in `perms`.
spec fn slab_ok(
    c: nat,
    perms: Map<int, PointsToRaw>,
    s: Slab,
    a: int,
    store: RecordStore,
    pb: PageBuddy,
    src: SourceView,
) -> bool {
    let b = s.base()@.addr as int;
    &&& store.taken().contains(a)
    &&& s.wf()
    &&& s.slot() == class_size(c)
    &&& s.bytes() == run_bytes(slab_order(c))
    &&& s.base()@.provenance == src.provenance
    &&& run_held(pb, src, b, slab_order(c))
    &&& !store.pages().contains(b)
    &&& s.owns(perms)
}

/// Each slab of `m` is one of class `c`, no two at different records share a run, and `perms` holds
/// nothing outside their runs.
spec fn slabs_wf(
    c: nat,
    perms: Map<int, PointsToRaw>,
    m: Map<int, Slab>,
    store: RecordStore,
    pb: PageBuddy,
    src: SourceView,
) -> bool {
    &&& forall|a: int| #[trigger] m.contains_key(a) ==> slab_ok(c, perms, m[a], a, store, pb, src)
    &&& forall|a: int, b: int|
        #![trigger m.contains_key(a), m.contains_key(b)]
        m.contains_key(a) && m.contains_key(b) && a != b ==> m[a].base()@.addr != m[b].base()@.addr
    &&& forall|x: int| #[trigger]
        perms.contains_key(x) ==> exists|a: int| #[trigger] m.contains_key(a) && m[a].within(x)
}

/// A live slot of a slab lies inside its run, at the address of its index.
proof fn lemma_in_run(s: Slab, y: int)
    requires
        s.wf(),
        s.holds(y),
    ensures
        0 <= s.index(y) < s.count(),
        y == s.addr(s.index(y)),
        s.base()@.addr <= y,
        y + s.slot() <= s.base()@.addr + s.bytes(),
{
    s.lemma_slots();
    let i = s.index(y);
    assert(s.live().contains(i));
    assert(0 <= i < s.count());
    assert(s.within(s.addr(i)) || i == s.count());
}

/// Two different slots of one slab share no byte.
proof fn lemma_slots_apart(s: Slab, i: int, j: int)
    requires
        0 <= i,
        0 <= j,
        i != j,
    ensures
        s.addr(i) + s.slot() <= s.addr(j) || s.addr(j) + s.slot() <= s.addr(i),
{
    let n = s.slot() as int;
    if i < j {
        assert(i * n + n <= j * n) by (nonlinear_arith)
            requires
                i < j,
                n >= 0,
        ;
    } else {
        assert(j * n + n <= i * n) by (nonlinear_arith)
            requires
                j < i,
                n >= 0,
        ;
    }
}

/// A slab after `alloc` gave the free slot at `p` holds what it held and `p`; a slab with every slot
/// free held nothing before.
proof fn lemma_alloc_holds(s0: Slab, s1: Slab, p: int)
    requires
        s0.wf(),
        s1.base() == s0.base(),
        s1.bytes() == s0.bytes(),
        s1.slot() == s0.slot(),
        s1.count() == s0.count(),
        s0.free_slots().contains(s0.index(p)),
        p == s0.addr(s0.index(p)),
        s1.free_slots() == s0.free_slots().remove(s0.index(p)),
    ensures
        s0.within(p),
        !s0.holds(p),
        forall|x: int| #[trigger] s1.holds(x) <==> (x == p || s0.holds(x)),
        s0.free_slots() == Set::range(0, s0.count() as int) ==> forall|x: int| !#[trigger] s0.holds(x),
{
    s0.lemma_slots();
    let i = s0.index(p);
    assert(Set::range(0, s0.count() as int).contains(i));
    assert(s0.within(s0.addr(i)) || i == s0.count());
    assert(s1.live() =~= s0.live().insert(i));
    assert forall|x: int| #[trigger] s1.holds(x) <==> (x == p || s0.holds(x)) by {
        if s1.holds(x) && x != p {
            assert(s0.index(x) != i);
        }
    }
    if s0.free_slots() == Set::range(0, s0.count() as int) {
        assert(s0.live() =~= Set::<int>::empty());
    }
}

/// The live slots of `m` with the slab at `a` made `s1`, which holds the slots the slab it replaces
/// held, if any, and `p`.
proof fn lemma_live_insert(m: Map<int, Slab>, a: int, s1: Slab, p: int)
    requires
        forall|x: int| #[trigger] s1.holds(x) <==> (x == p || (m.contains_key(a) && m[a].holds(x))),
    ensures
        live_of(m.insert(a, s1)) == live_of(m).insert(p),
{
    let n = m.insert(a, s1);
    assert forall|x: int| live_of(n).contains(x) <==> #[trigger] live_of(m).insert(p).contains(x) by {
        if live_of(n).contains(x) {
            let b = choose|b: int| #[trigger] n.contains_key(b) && n[b].holds(x);
            if b != a {
                assert(m.contains_key(b) && m[b].holds(x));
            } else if x != p {
                assert(m.contains_key(a) && m[a].holds(x));
            }
        }
        if live_of(m).insert(p).contains(x) {
            if x == p {
                assert(n.contains_key(a) && n[a].holds(x));
            } else {
                let b = choose|b: int| #[trigger] m.contains_key(b) && m[b].holds(x);
                assert(n.contains_key(b) && n[b].holds(x));
            }
        }
    }
    assert(live_of(n) =~= live_of(m).insert(p));
}

/// `p` is the only live slot of the slab `s`.
pub open spec fn only_live(s: Slab, p: int) -> bool {
    forall|x: int| #[trigger] s.holds(x) ==> x == p
}

/// A slab after `free` took back its live slot at `p` holds what it held but `p`, has a free slot,
/// and has every slot free exactly when `p` was its only live slot.
proof fn lemma_free_holds(s0: Slab, s1: Slab, p: int)
    requires
        s0.wf(),
        s1.wf(),
        s1.base() == s0.base(),
        s1.bytes() == s0.bytes(),
        s1.slot() == s0.slot(),
        s1.count() == s0.count(),
        s0.holds(p),
        s1.free_slots() == s0.free_slots().insert(s0.index(p)),
    ensures
        forall|x: int| #[trigger] s1.holds(x) <==> (s0.holds(x) && x != p),
        s1.free_slots() != Set::<int>::empty(),
        (s1.free_slots() == Set::range(0, s1.count() as int)) <==> only_live(s0, p),
{
    s0.lemma_slots();
    let i = s0.index(p);
    assert(s1.free_slots().contains(i));
    assert(s1.live() =~= s0.live().remove(i));
    assert forall|x: int| #[trigger] s1.holds(x) <==> (s0.holds(x) && x != p) by {
        if s0.holds(x) && s0.index(x) == i {
            assert(x == p);
        }
    }
    if s1.free_slots() == Set::range(0, s1.count() as int) {
        assert forall|x: int| #[trigger] s0.holds(x) implies x == p by {
            assert(s0.live().contains(s0.index(x)));
            assert(s1.free_slots().contains(s0.index(x)));
        }
    }
    if only_live(s0, p) {
        assert forall|j: int| #[trigger] Set::range(0, s1.count() as int).contains(j) implies s1.free_slots().contains(j) by {
            if !s0.free_slots().contains(j) {
                assert(s0.within(s0.addr(j)));
                assert(s0.holds(s0.addr(j)));
            }
        }
        assert(s1.free_slots() =~= Set::range(0, s1.count() as int));
    }
}

/// The live slots of `m` with the slab at `a` made `s1`, which holds what it held but `p`, a slot no
/// other slab holds.
proof fn lemma_live_freed(m: Map<int, Slab>, a: int, s1: Slab, p: int)
    requires
        m.contains_key(a),
        forall|x: int| #[trigger] s1.holds(x) <==> (m[a].holds(x) && x != p),
        forall|b: int| #[trigger] m.contains_key(b) && b != a ==> !m[b].holds(p),
    ensures
        live_of(m.insert(a, s1)) == live_of(m).remove(p),
{
    let n = m.insert(a, s1);
    assert forall|x: int| live_of(n).contains(x) <==> #[trigger] live_of(m).remove(p).contains(x) by {
        if live_of(n).contains(x) {
            let b = choose|b: int| #[trigger] n.contains_key(b) && n[b].holds(x);
            assert(m.contains_key(b) && m[b].holds(x));
        }
        if live_of(m).remove(p).contains(x) {
            let b = choose|b: int| #[trigger] m.contains_key(b) && m[b].holds(x);
            assert(n.contains_key(b) && n[b].holds(x));
        }
    }
    assert(live_of(n) =~= live_of(m).remove(p));
}

/// The live slots of `m` without the slab at `a`, whose only live slot is `p`, a slot no other slab
/// holds.
proof fn lemma_live_removed(m: Map<int, Slab>, a: int, p: int)
    requires
        m.contains_key(a),
        only_live(m[a], p),
        forall|b: int| #[trigger] m.contains_key(b) && b != a ==> !m[b].holds(p),
    ensures
        live_of(m.remove(a)) == live_of(m).remove(p),
{
    let n = m.remove(a);
    assert forall|x: int| live_of(n).contains(x) <==> #[trigger] live_of(m).remove(p).contains(x) by {
        if live_of(n).contains(x) {
            let b = choose|b: int| #[trigger] n.contains_key(b) && n[b].holds(x);
            assert(m.contains_key(b) && m[b].holds(x));
        }
        if live_of(m).remove(p).contains(x) {
            let b = choose|b: int| #[trigger] m.contains_key(b) && m[b].holds(x);
            assert(b != a);
            assert(n.contains_key(b) && n[b].holds(x));
        }
    }
    assert(live_of(n) =~= live_of(m).remove(p));
}

/// A run cut by `alloc_run` leaves the source's refusals and provenance as they were.
proof fn lemma_cut_source(pb0: PageBuddy, pb1: PageBuddy, s0: SourceView, s1: SourceView, q: int, k: nat)
    requires
        cut_run(pb0, pb1, s0, s1, q, k),
    ensures
        s1.refusals == s0.refusals,
        s1.provenance == s0.provenance,
{
}

/// A record taken from a new record page keeps every held run held, and the page's run is none of
/// them.
proof fn lemma_took_keeps_held(pb2: PageBuddy, pb3: PageBuddy, s2: SourceView, s3: SourceView, r: int, x: int, j: nat)
    requires
        pb2.wf(s2),
        took_page(pb2, pb3, s2, s3, r),
        run_held(pb2, s2, x, j),
    ensures
        x != r,
        run_held(pb3, s3, x, j),
        s3.refusals == s2.refusals,
        s3.provenance == s2.provenance,
{
    let c = span_of(r);
    let m = if pb2.spans().contains_key(c) {
        s2
    } else {
        s2.reserved(c, SPAN_BLOCKS as nat).backed_run(c, meta_page(c), 1)
    };
    lemma_cut_keeps_held(pb2, pb3, s2, m, r, 0, x, j);
    lemma_backed_keeps_held(pb3, m, pb3.span_base(c), r, 1, x, j);
}

/// Cutting the run of order `k` at `q` adds it to the page buddy's runs and changes them no more.
proof fn lemma_cut_runs(pb0: PageBuddy, pb1: PageBuddy, s0: SourceView, s1: SourceView, q: int, k: nat)
    requires
        pb0.wf(s0),
        cut_run(pb0, pb1, s0, s1, q, k),
    ensures
        runs(pb1.used()) == runs(with_run(pb0.used(), q, k)),
{
    let c = span_of(q);
    let h = page_of(q);
    let u0 = pb0.used();
    let u1 = pb1.used();
    pb0.lemma_view(s0);
    if pb0.spans().contains_key(c) {
        assert(u1 =~= with_run(u0, q, k));
    } else {
        let w = with_run(u0, q, k);
        let m = meta_page(c);
        assert(!u0.contains_key(c));
        assert(!u0.contains_key(m));
        assert(m != c);
        assert(u1 =~= w.insert(m, Map::<int, nat>::empty()));
        assert(w[c].contains_key(h));
        assert(runs(u1).dom() =~= runs(w).dom());
        assert(runs(u1) =~= runs(w));
    }
}

/// Freeing the run at `q` takes it out of the page buddy's runs and changes them no further: a span
/// it gives back holds no run.
proof fn lemma_freed_runs(before: PageBuddy, after: PageBuddy, s: SourceView, t: SourceView, q: int)
    requires
        freed(before, after, s, t, q),
    ensures
        runs(after.used()) == runs(without_run(before.used(), q)),
{
    let c = span_of(q);
    let b = before.span_base(c);
    let m = meta_page(b);
    let u = before.used();
    let rest = without_run(u, q);
    assert(c == b || c == m);
    if rest[b].dom() != Set::<int>::empty() || rest[m].dom() != Set::<int>::empty() || before.idle_spans().len()
        < before.spares() {
        assert(after.used() == rest);
    } else {
        let w = after.used();
        assert(w == u.remove(b).remove(m));
        assert forall|x: int| #[trigger] runs(w).contains_key(x) <==> runs(rest).contains_key(x) by {
            if x != b && x != m {
                assert(x != c);
                assert(w.contains_key(x) == u.contains_key(x));
                assert(rest.contains_key(x) == u.contains_key(x));
            }
        }
        assert forall|x: int| #[trigger] runs(w).contains_key(x) implies runs(w)[x] == runs(rest)[x] by {
            assert(x != b && x != m);
        }
        assert(runs(w) =~= runs(rest));
    }
}

/// One size class: its partial and full slabs and the permission to each free slot of them.
pub struct SizeClass {
    /// The class's index.
    class: usize,
    /// The slabs with a free slot.
    partial: ClassList,
    /// The slabs with no free slot.
    full: ClassList,
    /// The permission to each free slot of the class's slabs, by address, and to each slab's tail.
    /// Only proofs read it, and a cargo build erases them.
    #[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
    perms: Tracked<Map<int, PointsToRaw>>,
}

impl SizeClass {
    /// The class's index.
    pub closed spec fn class(&self) -> nat {
        self.class as nat
    }

    /// The slab of each record on either list, by address.
    pub closed spec fn slabs(&self) -> Map<int, Slab> {
        self.partial.slabs().union_prefer_right(self.full.slabs())
    }

    /// The live slots of the class's slabs.
    pub open spec fn live(&self) -> ISet<int> {
        live_of(self.slabs())
    }

    /// The head of each slab's run.
    pub closed spec fn heads(&self) -> ISet<int> {
        ISet::new(|b: int| exists|a: int| #[trigger] self.slabs().contains_key(a) && self.slabs()[a].base()@.addr == b)
    }

    /// The class is one of the size classes; both lists are well formed with the source's
    /// provenance and share no record; the partial list holds exactly the slabs with a free slot;
    /// and the slabs are the class's, over the store, the page buddy and the source's view `src`.
    pub closed spec fn wf(&self, store: RecordStore, pb: PageBuddy, src: SourceView) -> bool {
        let ps = self.partial.slabs();
        let fs = self.full.slabs();
        &&& self.class < CLASSES
        &&& self.partial.wf(src.provenance)
        &&& self.full.wf(src.provenance)
        &&& ps.dom().disjoint(fs.dom())
        &&& forall|a: int| #[trigger] ps.contains_key(a) ==> ps[a].free_slots() != Set::<int>::empty()
        &&& forall|a: int| #[trigger] fs.contains_key(a) ==> fs[a].free_slots() == Set::<int>::empty()
        &&& slabs_wf(self.class as nat, self.perms@, self.slabs(), store, pb, src)
    }

    /// The runs of two slabs at different records share no address.
    proof fn lemma_apart(&self, store: RecordStore, pb: PageBuddy, src: SourceView, a: int, b: int)
        requires
            self.wf(store, pb, src),
            pb.wf(src),
            self.slabs().contains_key(a),
            self.slabs().contains_key(b),
            a != b,
        ensures
            self.slabs()[a].base()@.addr + self.slabs()[a].bytes() <= self.slabs()[b].base()@.addr
                || self.slabs()[b].base()@.addr + self.slabs()[b].bytes() <= self.slabs()[a].base()@.addr,
    {
        let m = self.slabs();
        let c = self.class as nat;
        assert(slab_ok(c, self.perms@, m[a], a, store, pb, src));
        assert(slab_ok(c, self.perms@, m[b], b, store, pb, src));
        assert(m[a].base()@.addr != m[b].base()@.addr);
        lemma_held_apart(pb, src, m[a].base()@.addr as int, slab_order(c), m[b].base()@.addr as int, slab_order(c));
    }

    /// A change to the store, the page buddy and the source that keeps what a class stands on keeps
    /// the invariant, whichever class or other user of the three made it.
    pub proof fn lemma_frame(
        &self,
        store: RecordStore,
        pb: PageBuddy,
        src: SourceView,
        store2: RecordStore,
        pb2: PageBuddy,
        src2: SourceView,
    )
        requires
            self.wf(store, pb, src),
            kept(store, pb, src, store2, pb2, src2),
        ensures
            self.wf(store2, pb2, src2),
    {
        let m = self.slabs();
        assert forall|a: int| #[trigger] m.contains_key(a) implies slab_ok(
            self.class as nat,
            self.perms@,
            m[a],
            a,
            store2,
            pb2,
            src2,
        ) by {
            assert(slab_ok(self.class as nat, self.perms@, m[a], a, store, pb, src));
        }
    }

    /// A change to the store, the page buddy and the source that keeps what a class stands on but
    /// for the record `a` and the run at `b` keeps the invariant of a class that has no slab at `a`
    /// and no head at `b`: another class across `free_small` retiring its slab at `a`, whose run is
    /// at `b`. `records_apart` and disjoint heads give a client the first two.
    pub proof fn lemma_frame_emptied(
        &self,
        store: RecordStore,
        pb: PageBuddy,
        src: SourceView,
        store2: RecordStore,
        pb2: PageBuddy,
        src2: SourceView,
        a: int,
        b: int,
    )
        requires
            self.wf(store, pb, src),
            kept_but(store, pb, src, store2, pb2, src2, a, b),
            !self.slabs().contains_key(a),
            !self.heads().contains(b),
        ensures
            self.wf(store2, pb2, src2),
    {
        let m = self.slabs();
        let c = self.class as nat;
        assert forall|r: int| #[trigger] m.contains_key(r) implies slab_ok(c, self.perms@, m[r], r, store2, pb2, src2) by {
            assert(slab_ok(c, self.perms@, m[r], r, store, pb, src));
            let x = m[r].base()@.addr as int;
            assert(m.contains_key(r) && m[r].base()@.addr == x);
            assert(self.heads().contains(x));
            assert(run_held(pb, src, x, slab_order(c)));
        }
    }

    /// No slab record of this class is one of `other`'s: each class holds its records'
    /// permissions. It changes nothing.
    pub fn records_apart(
        &mut self,
        other: &SizeClass,
        Ghost(store): Ghost<RecordStore>,
        Ghost(pb): Ghost<PageBuddy>,
        Ghost(src): Ghost<SourceView>,
    )
        requires
            old(self).wf(store, pb, src),
            other.wf(store, pb, src),
        ensures
            *final(self) == *old(self),
            old(self).slabs().dom().disjoint(other.slabs().dom()),
    {
        let ghost o = *self;
        let ghost prov = src.provenance;
        self.partial.apart(&other.partial, Ghost(prov), Ghost(prov));
        self.partial.apart(&other.full, Ghost(prov), Ghost(prov));
        self.full.apart(&other.partial, Ghost(prov), Ghost(prov));
        self.full.apart(&other.full, Ghost(prov), Ghost(prov));
        proof {
            assert(o.slabs().dom() =~= o.partial.slabs().dom().union(o.full.slabs().dom()));
            assert(other.slabs().dom() =~= other.partial.slabs().dom().union(other.full.slabs().dom()));
        }
    }

    /// The record of a slab that holds the slot `y`.
    pub open spec fn slab_of(&self, y: int) -> int {
        choose|a: int| #[trigger] self.slabs().contains_key(a) && self.slabs()[a].holds(y)
    }

    /// The live slot `y` is held by the slab at `slab_of(y)`, whose run is the only one of the
    /// class's that holds `y`.
    proof fn lemma_slab_of(&self, store: RecordStore, pb: PageBuddy, src: SourceView, y: int)
        requires
            self.wf(store, pb, src),
            pb.wf(src),
            self.live().contains(y),
        ensures
            self.slabs().contains_key(self.slab_of(y)),
            self.slabs()[self.slab_of(y)].holds(y),
            forall|b: int| #[trigger]
                self.slabs().contains_key(b) && self.slabs()[b].within(y) ==> b == self.slab_of(y),
    {
        let a = self.slab_of(y);
        assert(self.slabs().contains_key(a) && self.slabs()[a].holds(y));
        assert forall|b: int| #[trigger] self.slabs().contains_key(b) && self.slabs()[b].within(y) implies b == a by {
            if b != a {
                self.lemma_apart(store, pb, src, a, b);
            }
        }
    }

    /// Each head is a run of the class's slab order the page buddy holds, every page backed, and no
    /// record page.
    pub proof fn lemma_heads_held(&self, store: RecordStore, pb: PageBuddy, src: SourceView)
        requires
            self.wf(store, pb, src),
        ensures
            forall|b: int| #[trigger]
                self.heads().contains(b) ==> run_held(pb, src, b, slab_order(self.class())) && !store.pages().contains(
                    b,
                ),
    {
        let m = self.slabs();
        assert forall|b: int| #[trigger] self.heads().contains(b) implies run_held(
            pb,
            src,
            b,
            slab_order(self.class()),
        ) && !store.pages().contains(b) by {
            let a = choose|a: int| #[trigger] m.contains_key(a) && m[a].base()@.addr == b;
            assert(slab_ok(self.class as nat, self.perms@, m[a], a, store, pb, src));
        }
    }

    /// The live slot `y` lies inside the run at the head `b` this returns: a head of the class, a
    /// run of the class's slab order the page buddy holds, every page backed, and no record page.
    pub proof fn lemma_live_in_run(&self, store: RecordStore, pb: PageBuddy, src: SourceView, y: int) -> (b: int)
        requires
            self.wf(store, pb, src),
            self.live().contains(y),
        ensures
            self.heads().contains(b),
            run_held(pb, src, b, slab_order(self.class())),
            !store.pages().contains(b),
            b <= y,
            y + class_size(self.class()) <= b + run_bytes(slab_order(self.class())),
    {
        let m = self.slabs();
        let a = choose|a: int| #[trigger] m.contains_key(a) && m[a].holds(y);
        assert(slab_ok(self.class as nat, self.perms@, m[a], a, store, pb, src));
        lemma_in_run(m[a], y);
        let b = m[a].base()@.addr as int;
        assert(m.contains_key(a) && m[a].base()@.addr == b);
        b
    }

    /// A live slot shares no byte with a run the page buddy holds at a head that is not the class's,
    /// such as another class's slab run or a large object's run.
    pub proof fn lemma_live_apart_from_run(
        &self,
        store: RecordStore,
        pb: PageBuddy,
        src: SourceView,
        y: int,
        x: int,
        k: nat,
    )
        requires
            self.wf(store, pb, src),
            pb.wf(src),
            self.live().contains(y),
            run_held(pb, src, x, k),
            !self.heads().contains(x),
        ensures
            y + class_size(self.class()) <= x || x + run_bytes(k) <= y,
    {
        let b = self.lemma_live_in_run(store, pb, src, y);
        lemma_held_apart(pb, src, b, slab_order(self.class()), x, k);
    }

    /// A live slot of one class shares no byte with a live slot of a second class over the same
    /// store, page buddy and source, when no run is a slab run of both.
    pub proof fn lemma_classes_apart(
        &self,
        other: &SizeClass,
        store: RecordStore,
        pb: PageBuddy,
        src: SourceView,
        y: int,
        z: int,
    )
        requires
            self.wf(store, pb, src),
            other.wf(store, pb, src),
            pb.wf(src),
            self.heads().disjoint(other.heads()),
            self.live().contains(y),
            other.live().contains(z),
        ensures
            y + class_size(self.class()) <= z || z + class_size(other.class()) <= y,
    {
        let b = other.lemma_live_in_run(store, pb, src, z);
        assert(!self.heads().contains(b));
        self.lemma_live_apart_from_run(store, pb, src, y, b, slab_order(other.class()));
    }

    /// A slab of the class whose live slots are at most `y` has a free slot, when two slots of the
    /// class fit its run.
    pub proof fn lemma_one_live_free(&self, store: RecordStore, pb: PageBuddy, src: SourceView, a: int, y: int)
        requires
            self.wf(store, pb, src),
            self.slabs().contains_key(a),
            2 * class_size(self.class()) <= run_bytes(slab_order(self.class())),
            forall|x: int| #[trigger] self.slabs()[a].holds(x) ==> x == y,
        ensures
            self.slabs()[a].free_slots() != Set::<int>::empty(),
    {
        let s = self.slabs()[a];
        assert(slab_ok(self.class as nat, self.perms@, s, a, store, pb, src));
        s.lemma_slots();
        let n = s.bytes() as int;
        let d = s.slot() as int;
        assert(n / d >= 2) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(2 * d, n, d);
            vstd::arithmetic::div_mod::lemma_div_multiples_vanish(2, d);
            assert(d * 2 == 2 * d);
        }
        if s.free_slots() == Set::<int>::empty() {
            assert(s.live().contains(0));
            assert(s.live().contains(1));
            assert(s.holds(s.addr(0)));
            assert(s.holds(s.addr(1)));
            assert(s.addr(0) != s.addr(1));
        }
    }

    /// A class whose slab at `a` was replaced by one with the same base has the heads it had.
    proof fn lemma_heads_replaced(o: SizeClass, n: SizeClass, a: int)
        requires
            o.slabs().contains_key(a),
            n.slabs() == o.slabs().insert(a, n.slabs()[a]),
            n.slabs()[a].base() == o.slabs()[a].base(),
        ensures
            n.heads() == o.heads(),
    {
        let m = o.slabs();
        let nm = n.slabs();
        assert forall|b: int| n.heads().contains(b) <==> o.heads().contains(b) by {
            if n.heads().contains(b) {
                let d = choose|d: int| #[trigger] nm.contains_key(d) && nm[d].base()@.addr == b;
                assert(m.contains_key(d) && m[d].base()@.addr == b);
            }
            if o.heads().contains(b) {
                let d = choose|d: int| #[trigger] m.contains_key(d) && m[d].base()@.addr == b;
                assert(nm.contains_key(d) && nm[d].base()@.addr == b);
            }
        }
        assert(n.heads() =~= o.heads());
    }

    /// A class that gained the slab at `a` has the heads it had and that slab's base.
    proof fn lemma_heads_added(o: SizeClass, n: SizeClass, a: int)
        requires
            !o.slabs().contains_key(a),
            n.slabs() == o.slabs().insert(a, n.slabs()[a]),
        ensures
            n.heads() == o.heads().insert(n.slabs()[a].base()@.addr as int),
    {
        let m = o.slabs();
        let nm = n.slabs();
        let h = nm[a].base()@.addr as int;
        assert(nm.contains_key(a));
        assert forall|b: int| n.heads().contains(b) <==> #[trigger] o.heads().insert(h).contains(b) by {
            if n.heads().contains(b) && b != h {
                let d = choose|d: int| #[trigger] nm.contains_key(d) && nm[d].base()@.addr == b;
                assert(m.contains_key(d) && m[d].base()@.addr == b);
            }
            if o.heads().contains(b) {
                let d = choose|d: int| #[trigger] m.contains_key(d) && m[d].base()@.addr == b;
                assert(nm.contains_key(d) && nm[d].base()@.addr == b);
            }
            if b == h {
                assert(nm.contains_key(a) && nm[a].base()@.addr == b);
            }
        }
        assert(n.heads() =~= o.heads().insert(h));
    }

    /// The slab at `a` of the partial list, after `alloc` gave its free slot at `p`, as `s1` on the
    /// list its free slots name: the class is well formed, the slab replaced, `p` live, and `p`
    /// apart from every slot live before.
    proof fn lemma_took_slot(
        o: SizeClass,
        n: SizeClass,
        store: RecordStore,
        pb: PageBuddy,
        src: SourceView,
        a: int,
        s1: Slab,
        p: int,
    )
        requires
            o.wf(store, pb, src),
            pb.wf(src),
            o.partial.slabs().contains_key(a),
            n.class == o.class,
            n.partial.wf(src.provenance),
            n.full.wf(src.provenance),
            if s1.free_slots() == Set::<int>::empty() {
                &&& n.partial.slabs() == o.partial.slabs().remove(a)
                &&& n.full.slabs() == o.full.slabs().insert(a, s1)
            } else {
                &&& n.partial.slabs() == o.partial.slabs().remove(a).insert(a, s1)
                &&& n.full.slabs() == o.full.slabs()
            },
            s1.wf(),
            s1.base() == o.partial.slabs()[a].base(),
            s1.bytes() == o.partial.slabs()[a].bytes(),
            s1.slot() == o.partial.slabs()[a].slot(),
            s1.count() == o.partial.slabs()[a].count(),
            o.partial.slabs()[a].free_slots().contains(o.partial.slabs()[a].index(p)),
            p == o.partial.slabs()[a].addr(o.partial.slabs()[a].index(p)),
            s1.free_slots() == o.partial.slabs()[a].free_slots().remove(o.partial.slabs()[a].index(p)),
            s1.owns(n.perms@),
            n.perms@ == o.perms@.remove(p),
        ensures
            n.wf(store, pb, src),
            n.slabs() == o.slabs().insert(a, s1),
            n.live() == o.live().insert(p),
            forall|y: int| #[trigger]
                o.live().contains(y) ==> p + class_size(o.class()) <= y || y + class_size(o.class()) <= p,
    {
        let m = o.slabs();
        let c = o.class as nat;
        let s0 = m[a];
        assert(!o.full.slabs().contains_key(a));
        assert(m.contains_key(a));
        assert(s0 == o.partial.slabs()[a]);
        assert(slab_ok(c, o.perms@, s0, a, store, pb, src));
        lemma_alloc_holds(s0, s1, p);
        let i = s0.index(p);
        assert(n.slabs() =~= m.insert(a, s1));
        lemma_live_insert(m, a, s1, p);
        assert forall|y: int| #[trigger]
            o.live().contains(y) implies p + class_size(c) <= y || y + class_size(c) <= p by {
            let b = choose|b: int| #[trigger] m.contains_key(b) && m[b].holds(y);
            assert(slab_ok(c, o.perms@, m[b], b, store, pb, src));
            lemma_in_run(m[b], y);
            if b == a {
                assert(s0.live().contains(s0.index(y)));
                lemma_slots_apart(s0, i, s0.index(y));
            } else {
                o.lemma_apart(store, pb, src, a, b);
                s0.lemma_slots();
                assert(s0.addr(i) + s0.slot() <= s0.base()@.addr + s0.bytes() || i == s0.count());
            }
        }
        let nm = n.slabs();
        assert forall|b: int| #[trigger] nm.contains_key(b) implies slab_ok(c, n.perms@, nm[b], b, store, pb, src) by {
            if b != a {
                assert(slab_ok(c, o.perms@, m[b], b, store, pb, src));
                o.lemma_apart(store, pb, src, a, b);
                m[b].lemma_owns_frame(o.perms@, n.perms@);
            }
        }
        assert forall|x: int| #[trigger] n.perms@.contains_key(x) implies exists|b: int| #[trigger]
            nm.contains_key(b) && nm[b].within(x) by {
            assert(o.perms@.contains_key(x));
            let b = choose|b: int| #[trigger] m.contains_key(b) && m[b].within(x);
            assert(nm.contains_key(b) && nm[b].within(x));
        }
        assert forall|b: int, d: int|
            #![trigger nm.contains_key(b), nm.contains_key(d)]
            nm.contains_key(b) && nm.contains_key(d) && b != d implies nm[b].base()@.addr != nm[d].base()@.addr by {
            assert(m.contains_key(b) && m.contains_key(d));
        }
        assert(slabs_wf(c, n.perms@, nm, store, pb, src));
    }

    /// A new slab `s1` at the record `a`, which no slab of the class has, after `alloc` gave its
    /// slot at `p`, on the list its free slots name, with the permissions `fresh` it owns joined to
    /// the class's: the class is well formed, the slab added, `p` live, and `p` apart from every slot
    /// live before.
    proof fn lemma_added_slab(
        o: SizeClass,
        n: SizeClass,
        store: RecordStore,
        pb: PageBuddy,
        src: SourceView,
        a: int,
        s1: Slab,
        p: int,
        fresh: Map<int, PointsToRaw>,
    )
        requires
            o.wf(store, pb, src),
            pb.wf(src),
            !o.slabs().contains_key(a),
            n.class == o.class,
            n.partial.wf(src.provenance),
            n.full.wf(src.provenance),
            if s1.free_slots() == Set::<int>::empty() {
                &&& n.partial.slabs() == o.partial.slabs()
                &&& n.full.slabs() == o.full.slabs().insert(a, s1)
            } else {
                &&& n.partial.slabs() == o.partial.slabs().insert(a, s1)
                &&& n.full.slabs() == o.full.slabs()
            },
            slab_ok(o.class as nat, fresh, s1, a, store, pb, src),
            forall|b: int| #[trigger]
                o.slabs().contains_key(b) ==> o.slabs()[b].base()@.addr != s1.base()@.addr,
            forall|x: int| #[trigger] fresh.contains_key(x) ==> s1.within(x),
            forall|x: int| #[trigger] s1.holds(x) <==> x == p,
            n.perms@ == o.perms@.union_prefer_right(fresh),
        ensures
            n.wf(store, pb, src),
            n.slabs() == o.slabs().insert(a, s1),
            n.live() == o.live().insert(p),
            forall|y: int| #[trigger]
                o.live().contains(y) ==> p + class_size(o.class()) <= y || y + class_size(o.class()) <= p,
    {
        let m = o.slabs();
        let c = o.class as nat;
        let k = slab_order(c);
        let x1 = s1.base()@.addr as int;
        assert(n.slabs() =~= m.insert(a, s1));
        lemma_live_insert(m, a, s1, p);
        lemma_in_run(s1, p);
        assert forall|b: int| #[trigger] m.contains_key(b) implies m[b].base()@.addr + m[b].bytes() <= x1 || x1
            + s1.bytes() <= m[b].base()@.addr by {
            assert(slab_ok(c, o.perms@, m[b], b, store, pb, src));
            lemma_held_apart(pb, src, x1, k, m[b].base()@.addr as int, k);
        }
        assert forall|y: int| #[trigger]
            o.live().contains(y) implies p + class_size(c) <= y || y + class_size(c) <= p by {
            let b = choose|b: int| #[trigger] m.contains_key(b) && m[b].holds(y);
            assert(slab_ok(c, o.perms@, m[b], b, store, pb, src));
            lemma_in_run(m[b], y);
        }
        let nm = n.slabs();
        assert forall|b: int| #[trigger] nm.contains_key(b) implies slab_ok(c, n.perms@, nm[b], b, store, pb, src) by {
            if b != a {
                assert(slab_ok(c, o.perms@, m[b], b, store, pb, src));
                assert(m.contains_key(b));
                m[b].lemma_owns_frame(o.perms@, n.perms@);
            } else {
                assert forall|x: int|
                    #![trigger n.perms@.contains_key(x)]
                    #![trigger fresh.contains_key(x)]
                    s1.within(x) implies (n.perms@.contains_key(x) <==> fresh.contains_key(x)) && (fresh.contains_key(x)
                    ==> n.perms@[x] == fresh[x]) by {
                    if o.perms@.contains_key(x) && !fresh.contains_key(x) {
                        let d = choose|d: int| #[trigger] m.contains_key(d) && m[d].within(x);
                        assert(m.contains_key(d));
                    }
                }
                s1.lemma_owns_frame(fresh, n.perms@);
            }
        }
        assert forall|x: int| #[trigger] n.perms@.contains_key(x) implies exists|b: int| #[trigger]
            nm.contains_key(b) && nm[b].within(x) by {
            if fresh.contains_key(x) {
                assert(nm.contains_key(a) && nm[a].within(x));
            } else {
                assert(o.perms@.contains_key(x));
                let b = choose|b: int| #[trigger] m.contains_key(b) && m[b].within(x);
                assert(nm.contains_key(b) && nm[b].within(x));
            }
        }
        assert forall|b: int, d: int|
            #![trigger nm.contains_key(b), nm.contains_key(d)]
            nm.contains_key(b) && nm.contains_key(d) && b != d implies nm[b].base()@.addr != nm[d].base()@.addr by {
            if b != a && d != a {
                assert(m.contains_key(b) && m.contains_key(d));
            } else if b == a {
                assert(m.contains_key(d));
            } else {
                assert(m.contains_key(b));
            }
        }
        assert(slabs_wf(c, n.perms@, nm, store, pb, src));
    }

    /// The slab at `a`, after `free` took back its live slot at `y` and left a slot of it live, as
    /// `s1` on the partial list: the class is well formed, the slab replaced and `y` no longer live.
    proof fn lemma_freed_slot(
        o: SizeClass,
        n: SizeClass,
        store: RecordStore,
        pb: PageBuddy,
        src: SourceView,
        a: int,
        s1: Slab,
        y: int,
        slot: PointsToRaw,
    )
        requires
            o.wf(store, pb, src),
            pb.wf(src),
            o.slabs().contains_key(a),
            o.slabs()[a].holds(y),
            forall|b: int| #[trigger] o.slabs().contains_key(b) && o.slabs()[b].within(y) ==> b == a,
            n.class == o.class,
            n.partial.wf(src.provenance),
            n.full.wf(src.provenance),
            n.partial.slabs() == o.partial.slabs().remove(a).insert(a, s1),
            n.full.slabs() == o.full.slabs().remove(a),
            s1.wf(),
            s1.base() == o.slabs()[a].base(),
            s1.bytes() == o.slabs()[a].bytes(),
            s1.slot() == o.slabs()[a].slot(),
            s1.count() == o.slabs()[a].count(),
            s1.free_slots() == o.slabs()[a].free_slots().insert(o.slabs()[a].index(y)),
            s1.owns(n.perms@),
            n.perms@ == o.perms@.insert(y, slot),
        ensures
            n.wf(store, pb, src),
            n.slabs() == o.slabs().insert(a, s1),
            n.live() == o.live().remove(y),
            n.heads() == o.heads(),
    {
        let m = o.slabs();
        let c = o.class as nat;
        let s0 = m[a];
        assert(slab_ok(c, o.perms@, s0, a, store, pb, src));
        lemma_free_holds(s0, s1, y);
        assert(n.slabs() =~= m.insert(a, s1));
        assert forall|b: int| #[trigger] m.contains_key(b) && b != a implies !m[b].holds(y) by {}
        lemma_live_freed(m, a, s1, y);
        let nm = n.slabs();
        assert forall|b: int| #[trigger] nm.contains_key(b) implies slab_ok(c, n.perms@, nm[b], b, store, pb, src) by {
            if b != a {
                assert(slab_ok(c, o.perms@, m[b], b, store, pb, src));
                assert(!m[b].within(y));
                m[b].lemma_owns_frame(o.perms@, n.perms@);
            }
        }
        assert forall|x: int| #[trigger] n.perms@.contains_key(x) implies exists|b: int| #[trigger]
            nm.contains_key(b) && nm[b].within(x) by {
            if x == y {
                assert(nm.contains_key(a) && nm[a].within(x));
            } else {
                assert(o.perms@.contains_key(x));
                let b = choose|b: int| #[trigger] m.contains_key(b) && m[b].within(x);
                assert(nm.contains_key(b) && nm[b].within(x));
            }
        }
        assert forall|b: int, d: int|
            #![trigger nm.contains_key(b), nm.contains_key(d)]
            nm.contains_key(b) && nm.contains_key(d) && b != d implies nm[b].base()@.addr != nm[d].base()@.addr by {
            assert(m.contains_key(b) && m.contains_key(d));
        }
        assert(slabs_wf(c, n.perms@, nm, store, pb, src));
        assert(n.partial.slabs().dom().disjoint(n.full.slabs().dom()));
        SizeClass::lemma_heads_replaced(o, n, a);
    }

    /// The slab at `a`, whose only live slot `y` was taken back, retired and off both lists, with the
    /// permissions of its run gone from the class's: over a store, page buddy and source that keep
    /// every other slab's record taken and its run held, the class is well formed, the slab gone and
    /// `y` no longer live.
    proof fn lemma_removed_slab(
        o: SizeClass,
        n: SizeClass,
        store: RecordStore,
        pb: PageBuddy,
        src: SourceView,
        store2: RecordStore,
        pb2: PageBuddy,
        src2: SourceView,
        a: int,
        y: int,
    )
        requires
            o.wf(store, pb, src),
            pb.wf(src),
            o.slabs().contains_key(a),
            o.slabs()[a].holds(y),
            only_live(o.slabs()[a], y),
            forall|b: int| #[trigger] o.slabs().contains_key(b) && o.slabs()[b].within(y) ==> b == a,
            n.class == o.class,
            n.partial.wf(src2.provenance),
            n.full.wf(src2.provenance),
            n.partial.slabs() == o.partial.slabs().remove(a),
            n.full.slabs() == o.full.slabs().remove(a),
            o.slabs()[a].outside(o.perms@, n.perms@),
            forall|x: int| #[trigger] n.perms@.contains_key(x) ==> !o.slabs()[a].within(x),
            src2.provenance == src.provenance,
            forall|b: int| #[trigger]
                o.slabs().contains_key(b) && b != a ==> {
                    &&& store2.taken().contains(b)
                    &&& !store2.pages().contains(o.slabs()[b].base()@.addr as int)
                    &&& run_held(pb2, src2, o.slabs()[b].base()@.addr as int, slab_order(o.class()))
                },
        ensures
            n.wf(store2, pb2, src2),
            n.slabs() == o.slabs().remove(a),
            n.live() == o.live().remove(y),
            n.heads() == o.heads().remove(o.slabs()[a].base()@.addr as int),
    {
        let m = o.slabs();
        let c = o.class as nat;
        let s0 = m[a];
        assert(n.slabs() =~= m.remove(a));
        assert forall|b: int| #[trigger] m.contains_key(b) && b != a implies !m[b].holds(y) by {}
        lemma_live_removed(m, a, y);
        let nm = n.slabs();
        assert forall|b: int| #[trigger] nm.contains_key(b) implies slab_ok(c, n.perms@, nm[b], b, store2, pb2, src2) by {
            assert(m.contains_key(b) && b != a);
            assert(slab_ok(c, o.perms@, m[b], b, store, pb, src));
            o.lemma_apart(store, pb, src, a, b);
            m[b].lemma_owns_frame(o.perms@, n.perms@);
        }
        assert forall|x: int| #[trigger] n.perms@.contains_key(x) implies exists|b: int| #[trigger]
            nm.contains_key(b) && nm[b].within(x) by {
            assert(o.perms@.contains_key(x));
            let b = choose|b: int| #[trigger] m.contains_key(b) && m[b].within(x);
            assert(nm.contains_key(b) && nm[b].within(x));
        }
        assert forall|b: int, d: int|
            #![trigger nm.contains_key(b), nm.contains_key(d)]
            nm.contains_key(b) && nm.contains_key(d) && b != d implies nm[b].base()@.addr != nm[d].base()@.addr by {
            assert(m.contains_key(b) && m.contains_key(d));
        }
        assert(slabs_wf(c, n.perms@, nm, store2, pb2, src2));
        assert(n.partial.slabs().dom().disjoint(n.full.slabs().dom()));
        let h = s0.base()@.addr as int;
        assert forall|x: int| n.heads().contains(x) <==> #[trigger] o.heads().remove(h).contains(x) by {
            if n.heads().contains(x) {
                let b = choose|b: int| #[trigger] nm.contains_key(b) && nm[b].base()@.addr == x;
                assert(m.contains_key(b) && m.contains_key(a));
            }
            if o.heads().contains(x) && x != h {
                let b = choose|b: int| #[trigger] m.contains_key(b) && m[b].base()@.addr == x;
                assert(nm.contains_key(b) && nm[b].base()@.addr == x);
            }
        }
        assert(n.heads() =~= o.heads().remove(h));
    }

    /// Size class `c` with no slab, well formed over every store, page buddy and source.
    pub fn new(c: usize) -> (r: Self)
        requires
            c < CLASSES,
        ensures
            r.class() == c,
            r.slabs() == Map::<int, Slab>::empty(),
            r.live() == ISet::<int>::empty(),
            r.heads() == ISet::<int>::empty(),
            forall|store: RecordStore, pb: PageBuddy, src: SourceView| #[trigger] r.wf(store, pb, src),
    {
        let r = SizeClass {
            class: c,
            partial: ClassList::new(),
            full: ClassList::new(),
            perms: Tracked(Map::tracked_empty()),
        };
        proof {
            assert(r.slabs() =~= Map::<int, Slab>::empty());
            assert(r.live() =~= ISet::<int>::empty());
            assert(r.heads() =~= ISet::<int>::empty());
        }
        r
    }

    /// A slot of the class's size: from the first slab with a free one, which keeps its base, changing
    /// no other slab, nor the store, the page buddy or the source; or, when no slab has one, from a new slab, whose run is cut
    /// and backed and whose record is taken from the store. Refuses only when no slab has a free
    /// slot and the source refused one request in this call, a run span only when no held span had a
    /// free block of the order asked and a record page only when the store was full, and then gives
    /// back what the call took.
    /// Either way it keeps what every class over the same three stands on.
    #[verifier::spinoff_prover]
    pub fn alloc_small<S: SpanSource>(&mut self, store: &mut RecordStore, pb: &mut PageBuddy, src: &mut S) -> (r:
        Option<(*mut u8, Tracked<PointsToRaw>)>)
        requires
            old(self).wf(*old(store), *old(pb), old(src)@),
            old(store).wf(*old(pb), old(src)@),
            old(pb).wf(old(src)@),
        ensures
            final(pb).wf(final(src)@),
            final(store).wf(*final(pb), final(src)@),
            final(self).wf(*final(store), *final(pb), final(src)@),
            final(self).class() == old(self).class(),
            final(pb).spares() == old(pb).spares(),
            kept(*old(store), *old(pb), old(src)@, *final(store), *final(pb), final(src)@),
            match r {
                None => {
                    &&& forall|a: int| #[trigger]
                        old(self).slabs().contains_key(a) ==> old(self).slabs()[a].free_slots()
                            == Set::<int>::empty()
                    &&& *final(self) == *old(self)
                    &&& final(store).pages() == old(store).pages()
                    &&& final(store).taken() == old(store).taken()
                    &&& runs(final(pb).used()) == runs(old(pb).used())
                    &&& forall|x: int, k: nat| #[trigger]
                        run_held(*old(pb), old(src)@, x, k) ==> run_held(*final(pb), final(src)@, x, k)
                    &&& slab_refused(*old(store), *old(pb), old(src)@, final(src)@, slab_order(old(self).class()))
                },
                Some((p, perm)) => {
                    let n = class_size(old(self).class());
                    &&& perm@.is_range(p@.addr as int, n as int)
                    &&& perm@.provenance() == old(src)@.provenance
                    &&& p@.provenance == old(src)@.provenance
                    &&& p@.addr % SLOT_MIN == 0
                    &&& !old(self).live().contains(p@.addr as int)
                    &&& final(self).live() == old(self).live().insert(p@.addr as int)
                    &&& forall|y: int| #[trigger]
                        old(self).live().contains(y) ==> p@.addr + n <= y || y + n <= p@.addr
                    &&& if exists|a: int| #[trigger]
                        old(self).slabs().contains_key(a) && old(self).slabs()[a].free_slots()
                            != Set::<int>::empty() {
                        &&& exists|a: int| #[trigger]
                            old(self).slabs().contains_key(a) && {
                                &&& final(self).slabs() == old(self).slabs().insert(a, final(self).slabs()[a])
                                &&& final(self).slabs()[a].base() == old(self).slabs()[a].base()
                                &&& forall|x: int| #[trigger]
                                    final(self).slabs()[a].holds(x) <==> (x == p@.addr as int
                                        || old(self).slabs()[a].holds(x))
                            }
                        &&& final(self).slabs().dom() == old(self).slabs().dom()
                        &&& final(self).heads() == old(self).heads()
                        &&& *final(store) == *old(store)
                        &&& *final(pb) == *old(pb)
                        &&& final(src)@ == old(src)@
                    } else {
                        exists|a: int| #[trigger]
                            final(self).slabs().contains_key(a) && {
                                &&& !old(self).slabs().contains_key(a)
                                &&& final(self).slabs() == old(self).slabs().insert(a, final(self).slabs()[a])
                                &&& final(self).slabs()[a].holds(p@.addr as int)
                                &&& final(self).heads() == old(self).heads().insert(
                                    final(self).slabs()[a].base()@.addr as int,
                                )
                                &&& forall|y: int, j: nat| #[trigger]
                                    run_held(*old(pb), old(src)@, y, j) ==> y != final(self).slabs()[a].base()@.addr
                                &&& new_slab(
                                    *old(store),
                                    *final(store),
                                    *old(pb),
                                    *final(pb),
                                    old(src)@,
                                    final(src)@,
                                    a,
                                    final(self).slabs()[a].base()@.addr as int,
                                    slab_order(old(self).class()),
                                )
                            }
                    }
                },
            },
    {
        let ghost prov = src@.provenance;
        let ghost o = *self;
        let ghost cl = self.class as nat;
        let ghost kk = slab_order(cl);
        proof {
            self.partial.lemma_view(prov);
            self.full.lemma_view(prov);
        }
        if let Some(rp) = self.partial.first(Ghost(prov)) {
            let ghost a = rp@.addr as int;
            proof {
                assert(self.partial.seq().contains(self.partial.seq()[0]));
                assert(a == self.partial.seq()[0]);
                assert(o.partial.slabs().contains_key(a));
                assert(!o.full.slabs().contains_key(a));
                assert(o.slabs()[a] == o.partial.slabs()[a]);
                assert(o.slabs().contains_key(a));
                assert(slab_ok(cl, o.perms@, o.slabs()[a], a, *store, *pb, src@));
            }
            let Tracked(mut perm) = self.partial.remove(rp, Ghost(prov));
            let mut rec = ptr_mut_read(rp, Tracked(&mut perm));
            let ghost s0 = rec.slab;
            let got = rec.slab.alloc(Tracked(self.perms.borrow_mut()));
            let (p, slot) = match got {
                Some(x) => x,
                None => {
                    proof {
                        assert(false);
                    }
                    return None;
                },
            };
            let ghost s1 = rec.slab;
            let full = rec.slab.is_full();
            ptr_mut_write(rp, Tracked(&mut perm), rec);
            proof {
                self.partial.lemma_view(prov);
                assert(!self.partial.slabs().contains_key(a));
            }
            if full {
                self.full.push(rp, Tracked(perm), Ghost(prov));
            } else {
                self.partial.push(rp, Tracked(perm), Ghost(prov));
            }
            proof {
                SizeClass::lemma_took_slot(o, *self, *store, *pb, src@, a, s1, p@.addr as int);
                assert forall|y: int| #[trigger] o.live().contains(y) implies y != p@.addr as int by {}
                assert(self.slabs().dom() =~= o.slabs().dom());
                SizeClass::lemma_heads_replaced(o, *self, a);
            }
            return Some((p, slot));
        }
        // No slab has a free slot: a new slab.
        let ghost pb0 = *pb;
        let ghost s0 = src@;
        let ghost st0 = *store;
        proof {
            assert(o.partial.slabs() =~= Map::<int, Slab>::empty());
            assert forall|a: int| #[trigger] o.slabs().contains_key(a) implies o.slabs()[a].free_slots()
                == Set::<int>::empty() by {
                assert(o.full.slabs().contains_key(a));
            }
            store.lemma_view(pb0, s0);
            pb0.lemma_view(s0);
        }
        let k = order(self.class);
        let slot = size(self.class);
        proof {
            lemma_class(cl);
            lemma_block_pages();
            lemma_pages(k as nat, BLOCK_ORDER as nat);
        }
        let bytes = order_pages(k) * PAGE_BYTES;
        let q = match pb.alloc_run(src, k) {
            Err(_) => {
                proof {
                    let pb1 = *pb;
                    let s1 = src@;
                    assert forall|x: int, j: nat| #[trigger] run_held(pb0, s0, x, j) implies run_held(pb1, s1, x, j) by {
                        lemma_recorded_keeps_held(pb0, s0, s1.refusals.last(), x, j);
                    }
                    store.lemma_frame(pb0, s0, pb1, s1);
                    o.lemma_frame(st0, pb0, s0, st0, pb1, s1);
                    assert(runs(pb1.used()) == runs(pb0.used()));
                    assert(slab_refused(st0, pb0, s0, s1, kk));
                }
                return None;
            },
            Ok(q) => q,
        };
        let ghost qi = q as int;
        let ghost c = span_of(qi);
        let ghost pb1 = *pb;
        let ghost s1 = src@;
        proof {
            assert(cut_run(pb0, pb1, s0, s1, qi, kk));
            lemma_cut_source(pb0, pb1, s0, s1, qi, kk);
            assert forall|x: int, j: nat| #[trigger] run_held(pb0, s0, x, j) implies x != qi && run_held(pb1, s1, x, j) by {
                lemma_cut_keeps_held(pb0, pb1, s0, s1, qi, kk, x, j);
            }
            assert(pb1.used().contains_key(c));
            assert(pb1.used()[c][page_of(qi)] == kk);
            pb1.lemma_view(s1);
        }
        let (base, run) = match pb.back_run(src, q, k) {
            None => {
                let ghost pb2 = *pb;
                let ghost s2 = src@;
                pb.free_run(src, q);
                proof {
                    let pb3 = *pb;
                    let s3 = src@;
                    assert(freed(pb2, pb3, s2, s3, qi));
                    lemma_runs_restored(pb0, pb1, pb2, pb3, s0, s1, s2, s3, qi, kk);
                    assert(pb2.holds(qi));
                    assert forall|x: int, j: nat| #[trigger] run_held(pb0, s0, x, j) implies run_held(pb3, s3, x, j) by {
                        assert(x != qi && run_held(pb1, s1, x, j));
                        lemma_recorded_keeps_held(pb1, s1, s2.refusals.last(), x, j);
                        assert(run_held(pb2, s2, x, j));
                        lemma_freed_keeps_held(pb2, pb3, s2, s3, qi, x, j);
                    }
                    store.lemma_frame(pb0, s0, pb3, s3);
                    o.lemma_frame(st0, pb0, s0, st0, pb3, s3);
                    assert(s3.refusals == s0.refusals.push(s2.refusals.last()));
                    assert(cut_run(pb0, pb1, s0, s1, qi, kk));
                    assert(run_refused(st0, pb1, s1, s3.refusals.last(), qi, kk));
                    assert(slab_refused(st0, pb0, s0, s3, kk));
                }
                return None;
            },
            Some(x) => x,
        };
        let ghost pb2 = *pb;
        let ghost s2 = src@;
        proof {
            assert forall|x: int, j: nat| #[trigger] run_held(pb0, s0, x, j) implies x != qi && run_held(pb2, s2, x, j) by {
                assert(run_held(pb1, s1, x, j));
                lemma_backed_keeps_held(pb1, s1, pb1.span_base(c), qi, pages(kk) as nat, x, j);
            }
            assert(run_held(pb2, s2, qi, kk));
            lemma_held_bounds(pb2, s2, qi, kk);
            vstd::arithmetic::div_mod::lemma_mod_mod(qi, SLOT_MIN as int, (PAGE_BYTES / SLOT_MIN) as int);
            assert(qi % SLOT_MIN as int == 0);
            assert(s2.provenance == s0.provenance);
            store.lemma_frame(pb0, s0, pb2, s2);
        }
        let mut fresh: Tracked<Map<int, PointsToRaw>> = Tracked(Map::tracked_empty());
        let mut slab = Slab::new(base, bytes, slot, run, Tracked(fresh.borrow_mut()));
        let ghost n0 = slab;
        let ghost f0 = fresh@;
        proof {
            assert forall|x: int| #[trigger] f0.contains_key(x) implies n0.within(x) by {}
        }
        let taken = store.take(pb, src);
        let ghost pb3 = *pb;
        let ghost s3 = src@;
        let (rp, rperm) = match taken {
            None => {
                proof {
                    assert(run_held(pb3, s3, qi, kk));
                    assert(n0.free_slots() == Set::range(0, n0.count() as int));
                }
                let whole = slab.retire(Tracked(fresh.borrow_mut()));
                pb.release_run(src, q, k, whole);
                let ghost pb4 = *pb;
                let ghost s4 = src@;
                pb.free_run(src, q);
                proof {
                    let pb5 = *pb;
                    let s5 = src@;
                    assert(freed(pb4, pb5, s4, s5, qi));
                    assert(runs(pb4.used()) == runs(pb1.used()));
                    lemma_runs_restored(pb0, pb1, pb4, pb5, s0, s1, s4, s5, qi, kk);
                    assert forall|x: int, j: nat| #[trigger] run_held(pb0, s0, x, j) implies run_held(pb5, s5, x, j) by {
                        assert(x != qi && run_held(pb2, s2, x, j));
                        assert(run_held(pb3, s3, x, j));
                        lemma_released_keeps_held(pb3, s3, qi, kk, x, j);
                        assert(run_held(pb4, s4, x, j));
                        lemma_freed_keeps_held(pb4, pb5, s4, s5, qi, x, j);
                    }
                    assert forall|b: int| #[trigger] store.pages().contains(b) implies run_held(pb5, s5, b, 0) by {
                        assert(st0.pages().contains(b));
                        assert(run_held(pb0, s0, b, 0));
                    }
                    store.lemma_frame(pb3, s3, pb5, s5);
                    o.lemma_frame(st0, pb0, s0, *store, pb5, s5);
                    assert(s5.refusals == s3.refusals);
                    assert(pb2.spans() == pb1.spans());
                    assert(pb2.fits(0) == pb1.fits(0));
                    assert(s2 == s1.backed_run(pb1.span_base(c), qi, pages(kk) as nat));
                    assert(cut_run(pb0, pb1, s0, s1, qi, kk));
                    assert(run_refused(st0, pb1, s1, s3.refusals.last(), qi, kk));
                    assert(slab_refused(st0, pb0, s0, s5, kk));
                }
                return None;
            },
            Some(x) => x,
        };
        let ghost a = rp@.addr as int;
        proof {
            store.lemma_view(pb3, s3);
            assert(store.taken().contains(a));
            assert(store.pages().contains(record_page(a)));
            pb3.lemma_view(s3);
            lemma_held_bounds(pb3, s3, record_page(a), 0);
            assert(a > 0);
            if st0.full() {
                assert(took_page(pb2, pb3, s2, s3, record_page(a)));
                assert forall|x: int, j: nat| #[trigger] run_held(pb0, s0, x, j) implies x != qi && run_held(pb3, s3, x, j) by {
                    assert(run_held(pb2, s2, x, j));
                    lemma_took_keeps_held(pb2, pb3, s2, s3, record_page(a), x, j);
                }
                lemma_took_keeps_held(pb2, pb3, s2, s3, record_page(a), qi, kk);
            }
            assert(run_held(pb3, s3, qi, kk));
            assert(!store.pages().contains(qi)) by {
                if st0.pages().contains(qi) {
                    assert(run_held(pb0, s0, qi, 0));
                }
            }
            assert forall|x: int, j: nat| #[trigger] run_held(pb0, s0, x, j) implies {
                &&& run_held(pb3, s3, x, j)
                &&& store.pages().contains(x) ==> st0.pages().contains(x)
            } by {
                assert(run_held(pb2, s2, x, j));
                if st0.full() {
                    lemma_took_keeps_held(pb2, pb3, s2, s3, record_page(a), x, j);
                }
            }
            assert(kept(st0, pb0, s0, *store, pb3, s3));
            assert forall|b: int| #[trigger] o.slabs().contains_key(b) implies o.slabs()[b].base()@.addr != qi by {
                assert(slab_ok(cl, o.perms@, o.slabs()[b], b, st0, pb0, s0));
            }
            o.lemma_frame(st0, pb0, s0, *store, pb3, s3);
            assert(!o.slabs().contains_key(a)) by {
                if o.slabs().contains_key(a) {
                    assert(slab_ok(cl, o.perms@, o.slabs()[a], a, st0, pb0, s0));
                }
            }
            assert(!self.full.slabs().contains_key(a));
            assert(!self.partial.slabs().contains_key(a));
        }
        let got = slab.alloc(Tracked(fresh.borrow_mut()));
        let (p, sperm) = match got {
            Some(x) => x,
            None => {
                proof {
                    n0.lemma_slots();
                    assert(n0.free_slots().contains(0));
                    assert(false);
                }
                return None;
            },
        };
        let ghost s1n = slab;
        proof {
            lemma_alloc_holds(n0, s1n, p@.addr as int);
        }
        let full = slab.is_full();
        let Tracked(mut rperm) = rperm;
        ptr_mut_write(rp, Tracked(&mut rperm), Record { slab, prev: 0, next: 0 });
        if full {
            self.full.push(rp, Tracked(rperm), Ghost(prov));
        } else {
            self.partial.push(rp, Tracked(rperm), Ghost(prov));
        }
        let Tracked(f1) = fresh;
        let ghost fm = f1;
        proof {
            self.perms.borrow_mut().tracked_union_prefer_right(f1);
            assert forall|x: int| #[trigger] fm.contains_key(x) implies s1n.within(x) by {
                assert(f0.contains_key(x));
            }
            assert(slab_ok(cl, fm, s1n, a, *store, pb3, s3));
            SizeClass::lemma_added_slab(o, *self, *store, pb3, s3, a, s1n, p@.addr as int, fm);
            assert forall|y: int| #[trigger] o.live().contains(y) implies y != p@.addr as int by {}
            // What the call changed: the slab's run cut and backed, then its record taken.
            assert(s1n.base()@.addr == qi);
            assert(self.slabs()[a] == s1n);
            SizeClass::lemma_heads_added(o, *self, a);
            assert forall|y: int, j: nat| #[trigger] run_held(pb0, s0, y, j) implies y != qi by {
                lemma_cut_keeps_held(pb0, pb1, s0, s1, qi, kk, y, j);
            }
            assert(cut_run(pb0, pb2, s0, s1, qi, kk));
            assert(took_run(pb0, pb2, s0, s2, qi, kk));
            lemma_cut_runs(pb0, pb1, s0, s1, qi, kk);
            if st0.full() {
                let r = record_page(a);
                let cr = span_of(r);
                let m = if pb2.spans().contains_key(cr) {
                    s2
                } else {
                    s2.reserved(cr, SPAN_BLOCKS as nat).backed_run(cr, meta_page(cr), 1)
                };
                assert(took_page(pb2, pb3, s2, s3, r));
                lemma_cut_runs(pb2, pb3, s2, m, r, 0);
                lemma_with_run_runs(pb2.used(), with_run(pb0.used(), qi, kk), r, 0);
            }
            assert(new_slab(st0, *store, pb0, pb3, s0, s3, a, qi, kk));
            assert(self.slabs().contains_key(a) && {
                &&& !o.slabs().contains_key(a)
                &&& self.slabs() == o.slabs().insert(a, self.slabs()[a])
                &&& self.slabs()[a].holds(p@.addr as int)
                &&& self.heads() == o.heads().insert(self.slabs()[a].base()@.addr as int)
                &&& forall|y: int, j: nat| #[trigger] run_held(pb0, s0, y, j) ==> y != self.slabs()[a].base()@.addr
                &&& new_slab(st0, *store, pb0, *pb, s0, src@, a, self.slabs()[a].base()@.addr as int, kk)
            });
        }
        Some((p, sperm))
    }

    /// Takes back the live slot at `p` with the permission to its bytes, and never refuses. A slab
    /// left with a live slot goes to the partial list, keeping its base and every other slab, the
    /// heads, the store, the page buddy and the source; a slab left with every slot free is retired,
    /// its run released and freed to the page buddy, its record put back in the store, and its base
    /// gone from the heads.
    pub fn free_small<S: SpanSource>(
        &mut self,
        store: &mut RecordStore,
        pb: &mut PageBuddy,
        src: &mut S,
        p: *mut u8,
        perm: Tracked<PointsToRaw>,
    )
        requires
            old(self).wf(*old(store), *old(pb), old(src)@),
            old(store).wf(*old(pb), old(src)@),
            old(pb).wf(old(src)@),
            old(self).live().contains(p@.addr as int),
            perm@.is_range(p@.addr as int, class_size(old(self).class()) as int),
            perm@.provenance() == old(src)@.provenance,
        ensures
            final(pb).wf(final(src)@),
            final(store).wf(*final(pb), final(src)@),
            final(self).wf(*final(store), *final(pb), final(src)@),
            final(self).class() == old(self).class(),
            final(pb).spares() == old(pb).spares(),
            final(self).live() == old(self).live().remove(p@.addr as int),
            ({
                let a = old(self).slab_of(p@.addr as int);
                let b = old(self).slabs()[a].base()@.addr as int;
                if only_live(old(self).slabs()[a], p@.addr as int) {
                    &&& final(self).slabs() == old(self).slabs().remove(a)
                    &&& final(self).heads() == old(self).heads().remove(b)
                    &&& !final(pb).holds(b)
                    &&& emptied_slab(
                        *old(store),
                        *final(store),
                        *old(pb),
                        *final(pb),
                        old(src)@,
                        final(src)@,
                        a,
                        b,
                        slab_order(old(self).class()),
                    )
                    &&& kept_but(*old(store), *old(pb), old(src)@, *final(store), *final(pb), final(src)@, a, b)
                } else {
                    &&& final(self).slabs() == old(self).slabs().insert(a, final(self).slabs()[a])
                    &&& final(self).slabs()[a].base() == old(self).slabs()[a].base()
                    &&& forall|x: int| #[trigger]
                        final(self).slabs()[a].holds(x) <==> (old(self).slabs()[a].holds(x) && x != p@.addr as int)
                    &&& final(self).heads() == old(self).heads()
                    &&& final(self).slabs().dom() == old(self).slabs().dom()
                    &&& *final(store) == *old(store)
                    &&& *final(pb) == *old(pb)
                    &&& final(src)@ == old(src)@
                }
            }),
    {
        let ghost prov = src@.provenance;
        let ghost o = *self;
        let ghost cl = self.class as nat;
        let ghost y = p@.addr as int;
        let ghost a0 = o.slab_of(y);
        let ghost st0 = *store;
        let ghost pb0 = *pb;
        let ghost s0 = src@;
        proof {
            o.lemma_slab_of(st0, pb0, s0, y);
            self.partial.lemma_view(prov);
            self.full.lemma_view(prov);
            assert(slab_ok(cl, o.perms@, o.slabs()[a0], a0, st0, pb0, s0));
        }
        let addr = p.addr();
        let (rp, was_full) = match self.partial.find(addr, Ghost(prov)) {
            Some(rp) => (rp, false),
            None => match self.full.find(addr, Ghost(prov)) {
                Some(rp) => (rp, true),
                None => {
                    proof {
                        if o.full.slabs().contains_key(a0) {
                            assert(o.full.seq().contains(a0));
                        } else {
                            assert(o.partial.seq().contains(a0));
                        }
                        assert(false);
                    }
                    return ;
                },
            },
        };
        let ghost a = rp@.addr as int;
        proof {
            if was_full {
                assert(o.full.slabs().contains_key(a));
            } else {
                assert(o.partial.slabs().contains_key(a));
                assert(!o.full.slabs().contains_key(a));
            }
            assert(o.slabs().contains_key(a) && o.slabs()[a].within(y));
            assert(a == a0);
        }
        let Tracked(mut rperm) = if was_full {
            self.full.remove(rp, Ghost(prov))
        } else {
            self.partial.remove(rp, Ghost(prov))
        };
        let mut rec = ptr_mut_read(rp, Tracked(&mut rperm));
        let ghost sl0 = rec.slab;
        let ghost p0 = self.perms@;
        proof {
            assert(sl0 == o.slabs()[a]);
        }
        rec.slab.free(addr, perm, Tracked(self.perms.borrow_mut()));
        let ghost sl1 = rec.slab;
        let ghost p1 = self.perms@;
        proof {
            lemma_free_holds(sl0, sl1, y);
            self.partial.lemma_view(prov);
            self.full.lemma_view(prov);
        }
        if rec.slab.is_empty() {
            let whole = rec.slab.retire(Tracked(self.perms.borrow_mut()));
            let q = rec.slab.start().addr();
            let k = order(self.class);
            let ghost qi = q as int;
            let ghost kk = k as nat;
            proof {
                assert(run_held(pb0, s0, qi, kk));
            }
            pb.release_run(src, q, k, whole);
            let ghost pb1 = *pb;
            let ghost s1 = src@;
            pb.free_run(src, q);
            let ghost pb2 = *pb;
            let ghost s2 = src@;
            proof {
                assert(freed(pb1, pb2, s1, s2, qi));
                assert(!pb2.holds(qi));
                assert forall|x: int, j: nat| #[trigger]
                    run_held(pb0, s0, x, j) && x != qi implies run_held(pb2, s2, x, j) by {
                    lemma_released_keeps_held(pb0, s0, qi, kk, x, j);
                    assert(run_held(pb1, s1, x, j));
                    lemma_freed_keeps_held(pb1, pb2, s1, s2, qi, x, j);
                }
                assert forall|b: int| #[trigger] store.pages().contains(b) implies run_held(pb2, s2, b, 0) by {
                    store.lemma_view(pb0, s0);
                    assert(run_held(pb0, s0, b, 0));
                }
                store.lemma_frame(pb0, s0, pb2, s2);
            }
            store.put(pb, src, rp, Tracked(rperm));
            proof {
                let pb3 = *pb;
                let s3 = src@;
                assert(!pb3.holds(qi)) by {
                    let r = record_page(a);
                    if !(exists|x: int| #[trigger] st0.taken().contains(x) && x != a && record_page(x) == r) {
                        let cr = span_of(r);
                        let cq = span_of(qi);
                        assert(gave_back(pb2, pb3, s2, s3, r));
                        st0.lemma_view(pb2, s2);
                        assert(st0.taken().contains(a));
                        assert(run_held(pb2, s2, r, 0));
                        if pb3.holds(qi) {
                            assert(pb2.used().contains_key(cq));
                            if cq == cr {
                                assert(pb2.used()[cq].contains_key(page_of(qi)));
                            } else {
                                assert(pb3.used()[cq] == pb2.used()[cq]);
                            }
                        }
                    }
                }
                assert forall|x: int, j: nat| #[trigger]
                    run_held(pb0, s0, x, j) && x != qi && !st0.pages().contains(x) implies run_held(pb3, s3, x, j) by {
                    assert(run_held(pb2, s2, x, j));
                }
                assert forall|b: int| #[trigger]
                    o.slabs().contains_key(b) && b != a implies {
                    &&& store.taken().contains(b)
                    &&& !store.pages().contains(o.slabs()[b].base()@.addr as int)
                    &&& run_held(pb3, s3, o.slabs()[b].base()@.addr as int, slab_order(o.class()))
                } by {
                    assert(slab_ok(cl, o.perms@, o.slabs()[b], b, st0, pb0, s0));
                    assert(o.slabs()[b].base()@.addr != qi);
                }
                assert(sl0.outside(o.perms@, self.perms@)) by {
                    assert forall|x: int|
                        #![trigger self.perms@.contains_key(x)]
                        #![trigger o.perms@.contains_key(x)]
                        !sl0.within(x) implies (self.perms@.contains_key(x) <==> o.perms@.contains_key(x)) && (
                        o.perms@.contains_key(x) ==> self.perms@[x] == o.perms@[x]) by {
                        assert(p1.contains_key(x) <==> p0.contains_key(x));
                    }
                }
                assert(emptied_slab(st0, *store, pb0, pb3, s0, s3, a, qi, kk)) by {
                    let r = record_page(a);
                    assert(pb1.used() == pb0.used());
                    assert(pb1.idle_spans() == pb0.idle_spans());
                    assert(freed(pb0, pb2, s1, s2, qi));
                    lemma_freed_runs(pb1, pb2, s1, s2, qi);
                    assert(st0.taken().contains(a));
                    if !page_shared(st0, a) {
                        assert(gave_back(pb2, pb3, s2, s3, r));
                        st0.lemma_view(pb2, s2);
                        assert(run_held(pb2, s2, r, 0));
                        lemma_freed_runs(pb2, pb3, s2.released_run(pb2.span_base(span_of(r)), r, 1), s3, r);
                        lemma_without_run_runs(pb2.used(), without_run(pb0.used(), qi), r);
                    }
                }
                assert(self.partial.slabs() =~= o.partial.slabs().remove(a));
                assert(self.full.slabs() =~= o.full.slabs().remove(a));
                SizeClass::lemma_removed_slab(o, *self, st0, pb0, s0, *store, pb3, s3, a, y);
            }
            return ;
        }
        ptr_mut_write(rp, Tracked(&mut rperm), rec);
        self.partial.push(rp, Tracked(rperm), Ghost(prov));
        proof {
            assert(self.partial.slabs() =~= o.partial.slabs().remove(a).insert(a, sl1));
            assert(self.full.slabs() =~= o.full.slabs().remove(a));
            SizeClass::lemma_freed_slot(o, *self, st0, pb0, s0, a, sl1, y, perm@);
            assert(self.slabs().dom() =~= o.slabs().dom());
        }
    }
}

} // verus!
