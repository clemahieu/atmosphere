// SPDX-License-Identifier: MIT
//! Slab records: the record of each slab, kept in record pages the heap backs itself.
//!
//! A record page is a run of order 0 the page buddy cuts with `alloc_run` and backs with
//! `back_run`. It holds a header at its start, the next record page and a bitmap of its records in
//! use, and PAGE_RECORDS records after it, each a slab and the two links of its class's list. The
//! headers link every record page into one list from `head`. The store holds the permission to each
//! header, and to the bytes of each page that no record in use covers; a record in use is its
//! taker's, with the permission to its bytes. The store reads and writes headers only, never a
//! record and never a slab's slots.
//!
//! The store owns neither the page buddy nor the source. Each operation takes both, and the
//! store's invariant, `wf(pb, src)`, is stated over the page buddy's view and the source's: each
//! record page is an allocated run of order 0 of the page buddy, its page backed (`run_held`). A
//! change that keeps every record page so keeps the invariant (`lemma_frame`).
//!
//! - `take(pb, src)` returns an unused record of a page that has one, changing neither the page
//!   buddy nor the source. When every page is full it cuts a new page, backs it and returns the
//!   page's first record (`took_page`). It refuses exactly when every page is full and either the
//!   page buddy refused the run, which it does only when no held span has a free page
//!   (`span_refused`), or the source refused to back the page the page buddy cut (`back_refused`);
//!   then it frees the run again, so the page buddy holds the runs it held (`runs`), and each run
//!   its caller held stays allocated with every page backed (`run_held`). Whatever it returns, a
//!   run allocated with only its first pages backed stays so (`run_part`).
//! - `put(pb, src, p, perm)` takes back the record at `p` with the permission to its bytes and
//!   never refuses. A page left with no record in use is given back: its page released and its run
//!   freed (`gave_back`). Each run its caller held at a head that is no record page stays allocated
//!   with every page backed, and one with only its first pages backed stays so (`run_part`).
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::layout::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;

use crate::arch::*;
#[cfg(verus_keep_ghost)]
use crate::buddy::*;
use crate::page::*;
use crate::slab::Slab;
use crate::source::*;

verus! {

broadcast use {group_raw_ptr_axioms, vstd::set_lib::range_set_properties};

/// One slab's record: the slab, and the links of the list its class keeps of its slabs.
pub struct Record {
    pub slab: Slab,
    pub prev: usize,
    pub next: usize,
}

/// A record page's header: the next record page, or 0 at the end of the list, and bit i set
/// exactly when record i of the page is in use.
#[repr(C)]
pub struct PageHeader {
    next: usize,
    used: u64,
}

/// Bit `i` of the word `w` is set.
spec fn in_use(w: u64, i: int) -> bool {
    0 <= i < 64 && (w >> (i as u64)) & 1u64 == 1u64
}

/// The address of record `i` of the record page at `b`.
pub open spec fn record_addr(b: int, i: int) -> int {
    b + HEADER_BYTES as int + i * RECORD_BYTES as int
}

/// The record page that holds address `a`.
pub open spec fn record_page(a: int) -> int {
    a - a % PAGE_BYTES as int
}

/// The bytes of the record page at `b` after its header that no record in use by the bitmap `w`
/// covers.
spec fn spare_bytes(b: int, w: u64) -> Set<int> {
    Set::range(b + HEADER_BYTES as int, b + PAGE_BYTES as int).filter(
        |x: int|
            forall|i: int|
                0 <= i < PAGE_RECORDS as int && #[trigger] in_use(w, i) ==> !(record_addr(b, i) <= x
                    < record_addr(b, i) + RECORD_BYTES as int),
    )
}

/// The pointer to the header of the record page at `b`.
spec fn header_ptr(b: int, provenance: Provenance) -> *mut PageHeader {
    ptr_mut_from_data(PtrData { addr: b as usize, provenance, metadata: () })
}

/// The page buddy went from `before` to `after`, and the source from `s` to `t`, by cutting the run
/// of order 0 at `q`, from a held span or a new one, and backing its page.
pub open spec fn took_page(before: PageBuddy, after: PageBuddy, s: SourceView, t: SourceView, q: int) -> bool {
    let c = span_of(q);
    let m = if before.spans().contains_key(c) {
        s
    } else {
        s.reserved(c, SPAN_BLOCKS as nat).backed_run(c, meta_page(c), 1)
    };
    &&& cut_run(before, after, s, m, q, 0)
    &&& t == m.backed_run(after.span_base(c), q, 1)
}

/// The page buddy went from `before` to `after`, and the source from `s` to `t`, by releasing the
/// page of the run of order 0 at `q` and freeing the run.
pub open spec fn gave_back(before: PageBuddy, after: PageBuddy, s: SourceView, t: SourceView, q: int) -> bool {
    freed(before, after, s.released_run(before.span_base(span_of(q)), q, 1), t, q)
}

/// The source went from `s` to `t`, and the page buddy from `pb` to `fin`, by the refusal of the
/// back of a record page's page and the freeing of its run: the page buddy, then `mid`, cut a run of
/// order 0 at `q`, the source's view going from `s` to `m`; the source refused the back of that page
/// in the span `mid` holds it in, while it held the spans `m` holds; and freeing the run left `fin`
/// and `t` (`freed`).
pub open spec fn back_refused(pb: PageBuddy, fin: PageBuddy, s: SourceView, t: SourceView) -> bool {
    let r = t.refusals.last();
    &&& t.provenance == s.provenance
    &&& t.refusals == s.refusals.push(r)
    &&& exists|mid: PageBuddy, m: SourceView, q: int| #[trigger]
        cut_run(pb, mid, s, m, q, 0) && r == (Refusal {
            request: Request::Back { span: mid.span_base(span_of(q)), start: q, pages: 1 },
            spans: m.spans,
        }) && freed(mid, fin, m.recorded(r), t, q)
}

/// The source went from `s` to `t`, and the page buddy from `pb` to `fin`, by `take` refusing a
/// record page: the reserve of a run span or the back of its metadata page, only when `pb` had no
/// free page (`run_span_refused`); or the back of the page it cut (`back_refused`).
pub open spec fn page_refused(pb: PageBuddy, fin: PageBuddy, s: SourceView, t: SourceView) -> bool {
    ||| run_span_refused(pb, fin, s, t, 0)
    ||| back_refused(pb, fin, s, t)
}

/// The pointer to the header of the record page at `b`.
fn header_at(hp: *mut u8, b: usize) -> (p: *mut PageHeader)
    ensures
        p == header_ptr(b as int, hp@.provenance),
{
    hp.with_addr(b) as *mut PageHeader
}

/// The pointer to the record at `a`.
fn record_at(hp: *mut u8, a: usize) -> (p: *mut Record)
    ensures
        p == ptr_mut_from_data::<Record>(PtrData { addr: a, provenance: hp@.provenance, metadata: () }),
{
    hp.with_addr(a) as *mut Record
}

/// The first bit below PAGE_RECORDS of `w` that is `set`, or PAGE_RECORDS when none is.
fn find(w: u64, set: bool) -> (r: usize)
    ensures
        r <= PAGE_RECORDS,
        r < PAGE_RECORDS ==> in_use(w, r as int) == set,
        r == PAGE_RECORDS ==> forall|j: int| 0 <= j < PAGE_RECORDS ==> #[trigger] in_use(w, j) != set,
{
    let mut i: usize = 0;
    while i < PAGE_RECORDS
        invariant
            i <= PAGE_RECORDS,
            forall|j: int| 0 <= j < i ==> #[trigger] in_use(w, j) != set,
        decreases PAGE_RECORDS - i,
    {
        if ((w >> (i as u64)) & 1u64 == 1u64) == set {
            return i;
        }
        i = i + 1;
    }
    i
}

/// Setting and clearing bit `i` of `w` changes bit `i` alone, and only bit 0 of 1 is set.
proof fn lemma_bit(w: u64, i: u64, j: u64)
    requires
        i < 64,
        j < 64,
    ensures
        ((w | (1u64 << i)) >> j) & 1u64 == 1u64 <==> (j == i || (w >> j) & 1u64 == 1u64),
        ((w & !(1u64 << i)) >> j) & 1u64 == 1u64 <==> (j != i && (w >> j) & 1u64 == 1u64),
        (1u64 >> j) & 1u64 == 1u64 <==> j == 0,
        (0u64 >> j) & 1u64 != 1u64,
{
    assert(i < 64 && j < 64 ==> (((w | (1u64 << i)) >> j) & 1u64 == 1u64 <==> (j == i || (w >> j) & 1u64
        == 1u64))) by (bit_vector);
    assert(i < 64 && j < 64 ==> (((w & !(1u64 << i)) >> j) & 1u64 == 1u64 <==> (j != i || false) && (w >> j)
        & 1u64 == 1u64)) by (bit_vector);
    assert(j < 64 ==> ((1u64 >> j) & 1u64 == 1u64 <==> j == 0)) by (bit_vector);
    assert((0u64 >> j) & 1u64 != 1u64) by (bit_vector);
}

/// The bits in use of `w` with bit `i` set, and with it cleared; and of the word 1.
proof fn lemma_word(w: u64, i: u64)
    requires
        i < 64,
    ensures
        forall|j: int| #[trigger] in_use(w | (1u64 << i), j) <==> (j == i as int || in_use(w, j)),
        forall|j: int| #[trigger] in_use(w & !(1u64 << i), j) <==> (j != i as int && in_use(w, j)),
        forall|j: int| #[trigger] in_use(1u64, j) <==> j == 0,
        forall|j: int| !#[trigger] in_use(0u64, j),
{
    assert forall|j: int| #[trigger] in_use(w | (1u64 << i), j) <==> (j == i as int || in_use(w, j)) by {
        if 0 <= j < 64 {
            lemma_bit(w, i, j as u64);
        }
    }
    assert forall|j: int| #[trigger] in_use(w & !(1u64 << i), j) <==> (j != i as int && in_use(w, j)) by {
        if 0 <= j < 64 {
            lemma_bit(w, i, j as u64);
        }
    }
    assert forall|j: int| #[trigger] in_use(1u64, j) <==> j == 0 by {
        if 0 <= j < 64 {
            lemma_bit(w, i, j as u64);
        }
    }
    assert forall|j: int| !#[trigger] in_use(0u64, j) by {
        if 0 <= j < 64 {
            lemma_bit(w, i, j as u64);
        }
    }
}

/// Record `i` of the record page at `b` lies in the page after its header, word-aligned, and its
/// address names the page and the index again.
proof fn lemma_addr(b: int, i: int)
    requires
        0 <= b,
        b % PAGE_BYTES as int == 0,
        0 <= i < PAGE_RECORDS,
    ensures
        record_page(record_addr(b, i)) == b,
        record_addr(b, i) % PAGE_BYTES as int == HEADER_BYTES + i * RECORD_BYTES,
        (record_addr(b, i) - b - HEADER_BYTES as int) / RECORD_BYTES as int == i,
        record_addr(b, i) % 8 == 0,
        b % 8 == 0,
        b + HEADER_BYTES <= record_addr(b, i),
        record_addr(b, i) + RECORD_BYTES <= b + PAGE_BYTES,
{
    lemma_record_layout();
    let a = record_addr(b, i);
    let r = HEADER_BYTES as int + i * RECORD_BYTES as int;
    let k = b / PAGE_BYTES as int;
    lemma_fundamental_div_mod(b, PAGE_BYTES as int);
    assert(b == PAGE_BYTES as int * k);
    lemma_mod_multiples_vanish(k, r, PAGE_BYTES as int);
    lemma_small_mod(r as nat, PAGE_BYTES as nat);
    assert(a % PAGE_BYTES as int == r);
    lemma_div_multiples_vanish(i, RECORD_BYTES as int);
    assert(a - b - HEADER_BYTES as int == RECORD_BYTES as int * i);
    let p = PAGE_BYTES as int;
    let d = PAGE_BYTES as int / 8;
    assert(p == 8 * d);
    assert(a == 8 * (k * d + 2 + 11 * i) && b == 8 * (k * d)) by (nonlinear_arith)
        requires
            b == p * k,
            p == 8 * d,
            a == b + 16 + 88 * i,
    ;
    lemma_mod_multiples_basic(k * d + 2 + 11 * i, 8);
    lemma_mod_multiples_basic(k * d, 8);
}

/// Taking record `i` of the page at `b` out of the spare bytes: the record's bytes are spare while
/// it is unused, and the spare bytes once it is in use are the others.
proof fn lemma_spare(b: int, lo: u64, hi: u64, i: int)
    requires
        0 <= i < PAGE_RECORDS,
        !in_use(lo, i),
        forall|j: int|
            #![trigger in_use(hi, j)]
            #![trigger in_use(lo, j)]
            in_use(hi, j) <==> (j == i || in_use(lo, j)),
    ensures
        Set::range(record_addr(b, i), record_addr(b, i) + RECORD_BYTES as int).subset_of(spare_bytes(b, lo)),
        spare_bytes(b, hi) == spare_bytes(b, lo).difference(
            Set::range(record_addr(b, i), record_addr(b, i) + RECORD_BYTES as int),
        ),
        spare_bytes(b, lo) == spare_bytes(b, hi) + Set::range(record_addr(b, i), record_addr(b, i) + RECORD_BYTES as int),
{
    lemma_record_layout();
    let r = Set::range(record_addr(b, i), record_addr(b, i) + RECORD_BYTES as int);
    assert(in_use(hi, i));
    assert forall|x: int| r.contains(x) implies #[trigger] spare_bytes(b, lo).contains(x) by {
        assert forall|j: int|
            0 <= j < PAGE_RECORDS as int && #[trigger] in_use(lo, j) implies !(record_addr(b, j) <= x
                < record_addr(b, j) + RECORD_BYTES as int) by {
            assert(j != i);
        }
    }
    assert forall|x: int| #[trigger]
        spare_bytes(b, hi).contains(x) <==> spare_bytes(b, lo).difference(r).contains(x) by {
        if spare_bytes(b, hi).contains(x) {
            assert forall|j: int|
                0 <= j < PAGE_RECORDS as int && #[trigger] in_use(lo, j) implies !(record_addr(b, j) <= x
                    < record_addr(b, j) + RECORD_BYTES as int) by {
                assert(in_use(hi, j));
            }
            assert(!r.contains(x));
        }
        if spare_bytes(b, lo).difference(r).contains(x) {
            assert forall|j: int|
                0 <= j < PAGE_RECORDS as int && #[trigger] in_use(hi, j) implies !(record_addr(b, j) <= x
                    < record_addr(b, j) + RECORD_BYTES as int) by {
                if j != i {
                    assert(in_use(lo, j));
                }
            }
        }
    }
    assert(spare_bytes(b, hi) =~= spare_bytes(b, lo).difference(r));
    assert(spare_bytes(b, lo) =~= spare_bytes(b, hi) + r);
}

/// With no record in use, the spare bytes are the whole page after its header.
proof fn lemma_spare_none(b: int, w: u64)
    requires
        forall|j: int| 0 <= j < PAGE_RECORDS ==> !#[trigger] in_use(w, j),
    ensures
        spare_bytes(b, w) == Set::range(b + HEADER_BYTES as int, b + PAGE_BYTES as int),
{
    assert(spare_bytes(b, w) =~= Set::range(b + HEADER_BYTES as int, b + PAGE_BYTES as int));
}

/// A page of a block the page buddy holds lies above address 0 and its page in the address space.
proof fn lemma_bounds(pb: PageBuddy, s: SourceView, q: int)
    requires
        pb.wf(s),
        0 <= q,
        q % PAGE_BYTES as int == 0,
        pb.used().contains_key(span_of(q)),
    ensures
        0 < q,
        q + PAGE_BYTES <= usize::MAX as int + 1,
        pb.spans().contains_key(span_of(q)),
{
    pb.lemma_view(s);
    lemma_head(q);
    let c = span_of(q);
    assert(pb.spans().contains_key(c));
    let b = pb.span_base(c);
    assert(s.spans.contains_key(b));
    assert(s.released_span(b).fits(b, s.spans[b].blocks));
    assert(page_of(q) * PAGE_BYTES + PAGE_BYTES <= BLOCK_BYTES);
}

/// Releasing the page at `q` keeps every other record page held.
proof fn lemma_released_held(pb: PageBuddy, s: SourceView, x: int, q: int, b: int)
    requires
        run_held(pb, s, b, 0),
        b != q,
        q % PAGE_BYTES as int == 0,
    ensures
        run_held(pb, s.released_run(x, q, 1), b, 0),
{
    assert(pages(0) == 1);
    lemma_one_page(q);
    lemma_one_page(b);
}

/// The record pages, linked from `head`, with the permission to each page's header and to the
/// bytes of it no record in use covers.
pub struct RecordStore {
    /// The first record page, while one is held; it carries the source's provenance.
    head: Option<*mut u8>,
    /// The record pages, in the order their headers link them.
    chain: Ghost<Seq<int>>,
    /// The index of each record in use, by address.
    owner: Ghost<Map<int, int>>,
    // Only proofs read the headers and the rests, and a cargo build erases them.
    /// The permission to each record page's header, by page.
    #[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
    headers: Tracked<Map<int, PointsTo<PageHeader>>>,
    /// The permission to the spare bytes of each record page, by page.
    #[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
    rests: Tracked<Map<int, PointsToRaw>>,
}

impl RecordStore {
    /// The header of the record page at `b`.
    spec fn header(&self, b: int) -> PageHeader {
        self.headers@[b].value()
    }

    /// The bitmap of the record page at `b`.
    spec fn word(&self, b: int) -> u64 {
        self.header(b).used
    }

    /// The record pages.
    pub closed spec fn pages(&self) -> Set<int> {
        self.headers@.dom()
    }

    /// The records in use, by address.
    pub closed spec fn taken(&self) -> Set<int> {
        self.owner@.dom()
    }

    /// Every record of every record page is in use.
    pub closed spec fn full(&self) -> bool {
        forall|b: int, i: int|
            self.headers@.contains_key(b) && 0 <= i < PAGE_RECORDS ==> #[trigger] in_use(self.word(b), i)
    }

    /// The header of the record page at `b` is at its start, the page lies above address 0 in the
    /// address space, and the store holds the page's spare bytes.
    spec fn page_wf(&self, b: int, prov: Provenance) -> bool {
        &&& self.headers@[b].ptr() == header_ptr(b, prov)
        &&& self.headers@[b].is_init()
        &&& 0 < b
        &&& b % PAGE_BYTES as int == 0
        &&& b + PAGE_BYTES <= usize::MAX as int + 1
        &&& self.rests@.contains_key(b)
        &&& self.rests@[b].dom() == spare_bytes(b, self.word(b))
        &&& self.rests@[b].provenance() == prov
    }

    /// The header at position `i` of the chain links the page after it, or ends the list.
    spec fn linked(&self, i: int) -> bool {
        self.header(self.chain@[i]).next as int == if i + 1 < self.chain@.len() {
            self.chain@[i + 1]
        } else {
            0
        }
    }

    /// The list from `head` links exactly the record pages, each well formed with the provenance
    /// `prov`, and the records in use are exactly those the bitmaps mark.
    spec fn inv(&self, prov: Provenance) -> bool {
        &&& self.chain@.no_duplicates()
        &&& forall|b: int|
            #![trigger self.headers@.contains_key(b)]
            #![trigger self.chain@.contains(b)]
            self.headers@.contains_key(b) <==> self.chain@.contains(b)
        &&& forall|b: int| #[trigger] self.headers@.contains_key(b) ==> self.page_wf(b, prov)
        &&& forall|i: int| 0 <= i < self.chain@.len() ==> #[trigger] self.linked(i)
        &&& match self.head {
            None => self.chain@.len() == 0,
            Some(h) => {
                &&& self.chain@.len() > 0
                &&& h@.addr as int == self.chain@[0]
                &&& h@.provenance == prov
            },
        }
        &&& forall|a: int| #[trigger]
            self.owner@.contains_key(a) ==> {
                &&& self.headers@.contains_key(record_page(a))
                &&& 0 <= self.owner@[a] < PAGE_RECORDS
                &&& a == record_addr(record_page(a), self.owner@[a])
                &&& in_use(self.word(record_page(a)), self.owner@[a])
            }
        &&& forall|b: int, i: int|
            self.headers@.contains_key(b) && 0 <= i < PAGE_RECORDS && #[trigger] in_use(self.word(b), i)
                ==> self.owner@.contains_key(record_addr(b, i))
    }

    /// The invariant over the page buddy and the source's view `src`: the store keeps neither, so
    /// its caller holds them and passes them to each operation, and may share them.
    pub closed spec fn wf(&self, pb: PageBuddy, src: SourceView) -> bool {
        &&& self.inv(src.provenance)
        &&& forall|b: int| #[trigger] self.headers@.contains_key(b) ==> run_held(pb, src, b, 0)
    }

    /// A record page is in the chain, its header well formed, and the list not empty.
    proof fn lemma_page(&self, b: int, prov: Provenance)
        requires
            self.inv(prov),
            self.headers@.contains_key(b),
        ensures
            self.page_wf(b, prov),
            self.chain@.contains(b),
            self.chain@.len() > 0,
            self.head is Some,
    {
    }

    /// The page at position `i` of the chain is held, its header well formed and linked.
    proof fn lemma_at(&self, i: int, prov: Provenance)
        requires
            self.inv(prov),
            0 <= i < self.chain@.len(),
        ensures
            self.headers@.contains_key(self.chain@[i]),
            self.page_wf(self.chain@[i], prov),
            self.linked(i),
            self.chain@[i] > 0,
    {
        assert(self.chain@.contains(self.chain@[i]));
    }

    /// The invariant on the view: each record page is held, and each record in use is on one.
    pub proof fn lemma_view(&self, pb: PageBuddy, src: SourceView)
        requires
            self.wf(pb, src),
        ensures
            forall|b: int| #[trigger] self.pages().contains(b) ==> run_held(pb, src, b, 0),
            forall|a: int| #[trigger] self.taken().contains(a) ==> self.pages().contains(record_page(a)),
    {
    }

    /// A change to the page buddy or the source that keeps every record page held, and the
    /// provenance, keeps the invariant.
    pub proof fn lemma_frame(&self, pb: PageBuddy, s: SourceView, pb2: PageBuddy, t: SourceView)
        requires
            self.wf(pb, s),
            t.provenance == s.provenance,
            forall|b: int| #[trigger] self.pages().contains(b) ==> run_held(pb2, t, b, 0),
        ensures
            self.wf(pb2, t),
    {
        assert forall|b: int| #[trigger] self.headers@.contains_key(b) implies run_held(pb2, t, b, 0) by {
            assert(self.pages().contains(b));
        }
    }

    /// A store with no record page, over any page buddy and source.
    pub fn new() -> (r: Self)
        ensures
            r.pages() == Set::<int>::empty(),
            r.taken() == Set::<int>::empty(),
            r.full(),
            forall|pb: PageBuddy, s: SourceView| #[trigger] r.wf(pb, s),
    {
        let r = RecordStore {
            head: None,
            chain: Ghost(Seq::empty()),
            owner: Ghost(Map::empty()),
            headers: Tracked(Map::tracked_empty()),
            rests: Tracked(Map::tracked_empty()),
        };
        proof {
            assert(r.pages() =~= Set::<int>::empty());
            assert(r.taken() =~= Set::<int>::empty());
        }
        r
    }

    /// A record page with an unused record, and the record's index, or none when every record is
    /// in use.
    fn find_page(&self, Ghost(prov): Ghost<Provenance>) -> (r: Option<(usize, usize)>)
        requires
            self.inv(prov),
        ensures
            match r {
                None => self.full(),
                Some((b, i)) => {
                    &&& self.headers@.contains_key(b as int)
                    &&& i < PAGE_RECORDS
                    &&& !in_use(self.word(b as int), i as int)
                },
            },
    {
        let hp = match self.head {
            None => {
                return None;
            },
            Some(h) => h,
        };
        let mut cur: usize = hp.addr();
        let ghost mut j: int = 0;
        while cur != 0
            invariant
                self.inv(prov),
                self.head == Some(hp),
                0 <= j <= self.chain@.len(),
                cur as int == if j < self.chain@.len() {
                    self.chain@[j]
                } else {
                    0
                },
                forall|k: int, i: int|
                    0 <= k < j && 0 <= i < PAGE_RECORDS ==> #[trigger] in_use(self.word(self.chain@[k]), i),
            decreases self.chain@.len() - j,
        {
            proof {
                self.lemma_at(j, prov);
            }
            let ghost b = self.chain@[j];
            let tracked perm = self.headers.borrow().tracked_borrow(b);
            let h = ptr_ref(header_at(hp, cur), Tracked(perm));
            let i = find(h.used, false);
            if i < PAGE_RECORDS {
                return Some((cur, i));
            }
            cur = h.next;
            proof {
                j = j + 1;
            }
        }
        proof {
            if j < self.chain@.len() {
                self.lemma_at(j, prov);
            }
            assert forall|b: int, i: int|
                self.headers@.contains_key(b) && 0 <= i < PAGE_RECORDS implies #[trigger] in_use(self.word(b), i) by {
                assert(self.chain@.contains(b));
                let k = choose|k: int| 0 <= k < self.chain@.len() && self.chain@[k] == b;
                assert(in_use(self.word(self.chain@[k]), i));
            }
        }
        None
    }

    /// The page before the record page at `b` in the list, or 0 when it is the first, and its
    /// position.
    fn locate(&self, b: usize, Ghost(prov): Ghost<Provenance>) -> (r: (usize, Ghost<int>))
        requires
            self.inv(prov),
            self.headers@.contains_key(b as int),
        ensures
            0 <= r.1@ < self.chain@.len(),
            self.chain@[r.1@] == b as int,
            r.0 as int == if r.1@ == 0 {
                0
            } else {
                self.chain@[r.1@ - 1]
            },
    {
        proof {
            self.lemma_page(b as int, prov);
        }
        let hp = self.head.unwrap();
        let ghost k = choose|k: int| 0 <= k < self.chain@.len() && self.chain@[k] == b as int;
        let mut prev: usize = 0;
        let mut cur: usize = hp.addr();
        let ghost mut j: int = 0;
        while cur != b
            invariant
                self.inv(prov),
                self.head == Some(hp),
                0 <= j <= k,
                k < self.chain@.len(),
                self.chain@[k] == b as int,
                cur as int == self.chain@[j],
                prev as int == if j == 0 {
                    0
                } else {
                    self.chain@[j - 1]
                },
            decreases k - j,
        {
            proof {
                self.lemma_at(j, prov);
            }
            let tracked perm = self.headers.borrow().tracked_borrow(self.chain@[j]);
            let h = ptr_ref(header_at(hp, cur), Tracked(perm));
            prev = cur;
            cur = h.next;
            proof {
                j = j + 1;
            }
        }
        (prev, Ghost(j))
    }

    /// Marks the unused record `i` of the record page at `b` in use, and returns a pointer to it
    /// with the permission to its bytes.
    fn take_in(&mut self, b: usize, i: usize, Ghost(prov): Ghost<Provenance>) -> (r: (*mut Record, Tracked<PointsTo<Record>>))
        requires
            old(self).inv(prov),
            old(self).headers@.contains_key(b as int),
            i < PAGE_RECORDS,
            !in_use(old(self).word(b as int), i as int),
        ensures
            final(self).inv(prov),
            final(self).pages() == old(self).pages(),
            !old(self).taken().contains(r.0@.addr as int),
            final(self).taken() == old(self).taken().insert(r.0@.addr as int),
            record_page(r.0@.addr as int) == b as int,
            r.1@.ptr() == r.0,
            r.1@.is_uninit(),
            r.0@.provenance == prov,
    {
        let ghost bi = b as int;
        let ghost ii = i as int;
        proof {
            old(self).lemma_page(bi, prov);
            lemma_record_layout();
            lemma_addr(bi, ii);
        }
        let hp = self.head.unwrap();
        let ptr = header_at(hp, b);
        let tracked mut hperm = self.headers.borrow_mut().tracked_remove(bi);
        let mut h = ptr_mut_read(ptr, Tracked(&mut hperm));
        let ghost lo = h.used;
        let sh = i as u64;
        h.used = h.used | (1u64 << sh);
        let ghost hi = h.used;
        ptr_mut_write(ptr, Tracked(&mut hperm), h);
        proof {
            self.headers.borrow_mut().tracked_insert(bi, hperm);
            lemma_word(lo, sh);
            lemma_spare(bi, lo, hi, ii);
        }
        let a = b + HEADER_BYTES + i * RECORD_BYTES;
        let ghost ai = a as int;
        let ghost range = Set::range(ai, ai + RECORD_BYTES as int);
        let tracked rest = self.rests.borrow_mut().tracked_remove(bi);
        let tracked (raw, spare) = rest.split(range);
        let tracked typed = raw.into_typed::<Record>(a);
        proof {
            self.rests.borrow_mut().tracked_insert(bi, spare);
        }
        self.owner = Ghost(self.owner@.insert(ai, ii));
        proof {
            let o = old(self);
            assert(ai == record_addr(bi, ii));
            assert(self.word(bi) == hi);
            assert(self.headers@.dom() =~= o.headers@.dom());
            assert forall|c: int| #[trigger] self.headers@.contains_key(c) implies self.page_wf(c, prov) by {
                assert(o.page_wf(c, prov));
            }
            assert forall|k: int| 0 <= k < self.chain@.len() implies #[trigger] self.linked(k) by {
                assert(o.linked(k));
            }
            if o.owner@.contains_key(ai) {
                assert(o.owner@[ai] == ii);
                assert(in_use(lo, ii));
            }
            assert forall|x: int| #[trigger] self.owner@.contains_key(x) implies {
                &&& self.headers@.contains_key(record_page(x))
                &&& 0 <= self.owner@[x] < PAGE_RECORDS
                &&& x == record_addr(record_page(x), self.owner@[x])
                &&& in_use(self.word(record_page(x)), self.owner@[x])
            } by {
                if x != ai {
                    assert(o.owner@.contains_key(x));
                    if record_page(x) == bi {
                        assert(in_use(lo, o.owner@[x]));
                    } else {
                        assert(self.word(record_page(x)) == o.word(record_page(x)));
                    }
                }
            }
            assert forall|c: int, k: int|
                self.headers@.contains_key(c) && 0 <= k < PAGE_RECORDS && #[trigger] in_use(self.word(c), k)
                    implies self.owner@.contains_key(record_addr(c, k)) by {
                if c == bi {
                    if k != ii {
                        assert(in_use(lo, k));
                        assert(o.owner@.contains_key(record_addr(c, k)));
                    }
                } else {
                    assert(self.word(c) == o.word(c));
                    assert(o.owner@.contains_key(record_addr(c, k)));
                }
            }
        }
        (record_at(hp, a), Tracked(typed))
    }

    /// Adds the backed page at `q`, the permission to all of it `raw`, as a record page with its
    /// first record in use, and returns a pointer to that record with the permission to its bytes.
    fn add_page(&mut self, q: usize, ptr: *mut u8, Tracked(raw): Tracked<PointsToRaw>, Ghost(prov): Ghost<Provenance>) -> (r: (
        *mut Record,
        Tracked<PointsTo<Record>>,
    ))
        requires
            old(self).inv(prov),
            !old(self).headers@.contains_key(q as int),
            0 < q,
            q as int % PAGE_BYTES as int == 0,
            q + PAGE_BYTES <= usize::MAX as int + 1,
            raw.is_range(q as int, PAGE_BYTES as int),
            raw.provenance() == prov,
            ptr@.addr == q,
            ptr@.provenance == prov,
        ensures
            final(self).inv(prov),
            final(self).pages() == old(self).pages().insert(q as int),
            !old(self).taken().contains(r.0@.addr as int),
            final(self).taken() == old(self).taken().insert(r.0@.addr as int),
            record_page(r.0@.addr as int) == q as int,
            r.1@.ptr() == r.0,
            r.1@.is_uninit(),
            r.0@.provenance == prov,
    {
        let ghost qi = q as int;
        let ghost ai = qi + HEADER_BYTES as int;
        proof {
            lemma_record_layout();
            lemma_addr(qi, 0);
            lemma_word(0u64, 0u64);
        }
        assert(Set::range(qi, ai).subset_of(raw.dom()));
        let tracked (hraw, rest) = raw.split(Set::range(qi, ai));
        assert(Set::range(ai, ai + RECORD_BYTES as int).subset_of(rest.dom()));
        let tracked (rraw, spare) = rest.split(Set::range(ai, ai + RECORD_BYTES as int));
        let tracked mut hperm = hraw.into_typed::<PageHeader>(q);
        let next = match self.head {
            None => 0,
            Some(h) => h.addr(),
        };
        ptr_mut_write(header_at(ptr, q), Tracked(&mut hperm), PageHeader { next, used: 1 });
        let a = q + HEADER_BYTES;
        let tracked rec = rraw.into_typed::<Record>(a);
        proof {
            lemma_spare(qi, 0u64, 1u64, 0);
            lemma_spare_none(qi, 0u64);
            assert(spare.dom() =~= spare_bytes(qi, 1u64));
            self.headers.borrow_mut().tracked_insert(qi, hperm);
            self.rests.borrow_mut().tracked_insert(qi, spare);
        }
        let ghost old_chain = self.chain@;
        self.chain = Ghost(seq![qi] + old_chain);
        self.owner = Ghost(self.owner@.insert(ai, 0));
        self.head = Some(ptr);
        proof {
            let o = old(self);
            let chain = self.chain@;
            assert(ai == record_addr(qi, 0));
            assert(self.word(qi) == 1u64);
            assert(self.pages() =~= o.pages().insert(qi));
            assert forall|i: int| 0 <= i < old_chain.len() implies old_chain[i] != qi by {
                o.lemma_at(i, prov);
            }
            assert forall|i: int| 0 <= i < old_chain.len() implies #[trigger] chain[i + 1] == old_chain[i] by {}
            assert(chain[0] == qi);
            assert(chain.no_duplicates()) by {
                assert forall|i: int, i2: int|
                    0 <= i < chain.len() && 0 <= i2 < chain.len() && i != i2 implies chain[i] != chain[i2] by {
                    if i > 0 && i2 > 0 {
                        assert(chain[i] == old_chain[i - 1]);
                        assert(chain[i2] == old_chain[i2 - 1]);
                    } else if i > 0 {
                        assert(chain[i] == old_chain[i - 1]);
                    } else {
                        assert(chain[i2] == old_chain[i2 - 1]);
                    }
                }
            }
            assert forall|c: int|
                #![trigger self.headers@.contains_key(c)]
                #![trigger self.chain@.contains(c)]
                self.headers@.contains_key(c) <==> self.chain@.contains(c) by {
                if self.chain@.contains(c) {
                    let i = choose|i: int| 0 <= i < chain.len() && chain[i] == c;
                    if i > 0 {
                        assert(chain[i] == old_chain[i - 1]);
                        assert(old_chain.contains(c));
                        assert(o.headers@.contains_key(c));
                    }
                }
                if self.headers@.contains_key(c) && c != qi {
                    assert(o.headers@.contains_key(c));
                    assert(old_chain.contains(c));
                    let i = choose|i: int| 0 <= i < old_chain.len() && old_chain[i] == c;
                    assert(chain[i + 1] == c);
                }
            }
            assert forall|c: int| #[trigger] self.headers@.contains_key(c) implies self.page_wf(c, prov) by {
                if c != qi {
                    assert(o.page_wf(c, prov));
                }
            }
            assert forall|i: int| 0 <= i < self.chain@.len() implies #[trigger] self.linked(i) by {
                if i > 0 {
                    assert(o.linked(i - 1));
                    assert(chain[i] == old_chain[i - 1]);
                    o.lemma_at(i - 1, prov);
                    if i + 1 < chain.len() {
                        assert(chain[i + 1] == old_chain[i]);
                    }
                } else if old_chain.len() > 0 {
                    assert(chain[1] == old_chain[0]);
                }
            }
            if o.owner@.contains_key(ai) {
                assert(o.headers@.contains_key(record_page(ai)));
            }
            assert forall|x: int| #[trigger] self.owner@.contains_key(x) implies {
                &&& self.headers@.contains_key(record_page(x))
                &&& 0 <= self.owner@[x] < PAGE_RECORDS
                &&& x == record_addr(record_page(x), self.owner@[x])
                &&& in_use(self.word(record_page(x)), self.owner@[x])
            } by {
                if x != ai {
                    assert(o.owner@.contains_key(x));
                    assert(o.headers@.contains_key(record_page(x)));
                    assert(record_page(x) != qi);
                    assert(self.word(record_page(x)) == o.word(record_page(x)));
                }
            }
            assert forall|c: int, k: int|
                self.headers@.contains_key(c) && 0 <= k < PAGE_RECORDS && #[trigger] in_use(self.word(c), k)
                    implies self.owner@.contains_key(record_addr(c, k)) by {
                if c != qi {
                    assert(self.word(c) == o.word(c));
                    assert(o.owner@.contains_key(record_addr(c, k)));
                }
            }
        }
        (record_at(ptr, a), Tracked(rec))
    }

    /// Takes back the record at `p` with the permission to its bytes, and returns its record page
    /// and whether no record of that page is in use now.
    #[verifier::spinoff_prover]
    fn give(&mut self, p: *mut Record, perm: Tracked<PointsTo<Record>>, Ghost(prov): Ghost<Provenance>) -> (r: (usize, bool))
        requires
            old(self).inv(prov),
            old(self).owner@.contains_key(p@.addr as int),
            perm@.ptr() == p,
            p@.provenance == prov,
        ensures
            final(self).inv(prov),
            final(self).pages() == old(self).pages(),
            final(self).head == old(self).head,
            final(self).chain == old(self).chain,
            final(self).taken() == old(self).taken().remove(p@.addr as int),
            r.0 as int == record_page(p@.addr as int),
            r.1 <==> !exists|x: int| #[trigger] final(self).taken().contains(x) && record_page(x) == r.0 as int,
            r.1 ==> forall|j: int| 0 <= j < PAGE_RECORDS ==> !#[trigger] in_use(final(self).word(r.0 as int), j),
    {
        let a = p.addr();
        let ghost ai = a as int;
        let ghost bi = record_page(ai);
        let ghost ii = self.owner@[ai];
        proof {
            old(self).lemma_page(bi, prov);
            lemma_record_layout();
            lemma_addr(bi, ii);
        }
        let b = a - a % PAGE_BYTES;
        let i = (a - b - HEADER_BYTES) / RECORD_BYTES;
        let hp = self.head.unwrap();
        let ptr = header_at(hp, b);
        let tracked mut hperm = self.headers.borrow_mut().tracked_remove(bi);
        let mut h = ptr_mut_read(ptr, Tracked(&mut hperm));
        let ghost hi = h.used;
        let sh = i as u64;
        h.used = h.used & !(1u64 << sh);
        let ghost lo = h.used;
        let used = h.used;
        ptr_mut_write(ptr, Tracked(&mut hperm), h);
        proof {
            self.headers.borrow_mut().tracked_insert(bi, hperm);
            lemma_word(hi, sh);
            lemma_spare(bi, lo, hi, ii);
        }
        let tracked mut typed = perm.get();
        proof {
            typed.leak_contents();
        }
        let tracked raw = typed.into_raw();
        let tracked rest = self.rests.borrow_mut().tracked_remove(bi);
        let tracked joined = rest.join(raw);
        proof {
            assert(joined.dom() =~= spare_bytes(bi, lo));
            self.rests.borrow_mut().tracked_insert(bi, joined);
        }
        self.owner = Ghost(self.owner@.remove(ai));
        let k = find(used, true);
        let empty = k == PAGE_RECORDS;
        proof {
            let o = old(self);
            assert(self.word(bi) == lo);
            assert(self.headers@.dom() =~= o.headers@.dom());
            assert forall|c: int| #[trigger] self.headers@.contains_key(c) implies self.page_wf(c, prov) by {
                assert(o.page_wf(c, prov));
            }
            assert forall|k: int| 0 <= k < self.chain@.len() implies #[trigger] self.linked(k) by {
                assert(o.linked(k));
            }
            assert forall|x: int| #[trigger] self.owner@.contains_key(x) implies {
                &&& self.headers@.contains_key(record_page(x))
                &&& 0 <= self.owner@[x] < PAGE_RECORDS
                &&& x == record_addr(record_page(x), self.owner@[x])
                &&& in_use(self.word(record_page(x)), self.owner@[x])
            } by {
                assert(o.owner@.contains_key(x));
                if record_page(x) == bi {
                    assert(o.owner@[x] != ii);
                    assert(in_use(hi, o.owner@[x]));
                } else {
                    assert(self.word(record_page(x)) == o.word(record_page(x)));
                }
            }
            assert forall|c: int, k: int|
                self.headers@.contains_key(c) && 0 <= k < PAGE_RECORDS && #[trigger] in_use(self.word(c), k)
                    implies self.owner@.contains_key(record_addr(c, k)) by {
                if c == bi {
                    assert(in_use(hi, k));
                    assert(o.owner@.contains_key(record_addr(c, k)));
                    assert(k != ii);
                    assert(record_addr(c, k) != ai);
                } else {
                    assert(self.word(c) == o.word(c));
                    assert(o.owner@.contains_key(record_addr(c, k)));
                }
            }
            if empty {
                assert forall|x: int| #[trigger] self.taken().contains(x) implies record_page(x) != bi by {
                    if record_page(x) == bi {
                        assert(in_use(lo, self.owner@[x]));
                    }
                }
            } else {
                lemma_addr(bi, k as int);
                assert(self.owner@.contains_key(record_addr(bi, k as int)));
                assert(self.taken().contains(record_addr(bi, k as int)));
            }
        }
        (b, empty)
    }

    /// Unlinks the record page at `b`, no record of which is in use, and returns the permission to
    /// all of it.
    fn remove_page(&mut self, b: usize, Ghost(prov): Ghost<Provenance>) -> (r: Tracked<PointsToRaw>)
        requires
            old(self).inv(prov),
            old(self).headers@.contains_key(b as int),
            forall|j: int| 0 <= j < PAGE_RECORDS ==> !#[trigger] in_use(old(self).word(b as int), j),
        ensures
            final(self).inv(prov),
            final(self).pages() == old(self).pages().remove(b as int),
            final(self).taken() == old(self).taken(),
            r@.is_range(b as int, PAGE_BYTES as int),
            r@.provenance() == prov,
    {
        let ghost bi = b as int;
        let ghost old_chain = self.chain@;
        let ghost len = old_chain.len();
        let (prev, Ghost(j)) = self.locate(b, Ghost(prov));
        proof {
            lemma_record_layout();
            self.lemma_at(j, prov);
            if j > 0 {
                self.lemma_at(j - 1, prov);
            }
            if j + 1 < len {
                self.lemma_at(j + 1, prov);
            }
        }
        let hp = self.head.unwrap();
        let ptr = header_at(hp, b);
        let tracked mut hperm = self.headers.borrow_mut().tracked_remove(bi);
        let h = ptr_mut_read(ptr, Tracked(&mut hperm));
        let next = h.next;
        if prev == 0 {
            proof {
                assert(j == 0);
            }
            if next == 0 {
                self.head = None;
            } else {
                self.head = Some(hp.with_addr(next));
            }
        } else {
            let ghost q = old_chain[j - 1];
            proof {
                assert(q != bi);
            }
            let pptr = header_at(hp, prev);
            let tracked mut pperm = self.headers.borrow_mut().tracked_remove(q);
            let mut ph = ptr_mut_read(pptr, Tracked(&mut pperm));
            ph.next = next;
            ptr_mut_write(pptr, Tracked(&mut pperm), ph);
            proof {
                self.headers.borrow_mut().tracked_insert(q, pperm);
            }
        }
        self.chain = Ghost(old_chain.remove(j));
        let tracked rest = self.rests.borrow_mut().tracked_remove(bi);
        let tracked hraw = hperm.into_raw();
        let tracked whole = hraw.join(rest);
        proof {
            let o = old(self);
            lemma_spare_none(bi, o.word(bi));
            assert(whole.dom() =~= Set::range(bi, bi + PAGE_BYTES as int));
            let chain = self.chain@;
            assert(self.pages() =~= o.pages().remove(bi));
            assert(chain.len() == len - 1);
            assert forall|i: int| 0 <= i < len - 1 implies #[trigger] chain[i] == if i < j {
                old_chain[i]
            } else {
                old_chain[i + 1]
            } by {}
            assert(chain.no_duplicates()) by {
                assert forall|i: int, i2: int|
                    0 <= i < chain.len() && 0 <= i2 < chain.len() && i != i2 implies chain[i] != chain[i2] by {
                    let oi = if i < j { i } else { i + 1 };
                    let oi2 = if i2 < j { i2 } else { i2 + 1 };
                    assert(chain[i] == old_chain[oi]);
                    assert(chain[i2] == old_chain[oi2]);
                }
            }
            assert forall|x: int|
                #![trigger self.headers@.contains_key(x)]
                #![trigger self.chain@.contains(x)]
                self.headers@.contains_key(x) <==> self.chain@.contains(x) by {
                if self.chain@.contains(x) {
                    let i = choose|i: int| 0 <= i < chain.len() && chain[i] == x;
                    let oi = if i < j { i } else { i + 1 };
                    assert(old_chain[oi] == x);
                    assert(oi != j);
                    assert(old_chain.contains(x));
                    assert(o.headers@.contains_key(x));
                }
                if self.headers@.contains_key(x) {
                    assert(o.headers@.contains_key(x));
                    assert(old_chain.contains(x));
                    let oi = choose|oi: int| 0 <= oi < len && old_chain[oi] == x;
                    assert(oi != j);
                    let i = if oi < j { oi } else { oi - 1 };
                    assert(chain[i] == x);
                }
            }
            assert forall|x: int| #[trigger] self.headers@.contains_key(x) implies self.page_wf(x, prov) by {
                assert(o.page_wf(x, prov));
                assert(self.word(x) == o.word(x));
            }
            assert forall|i: int| 0 <= i < chain.len() implies #[trigger] self.linked(i) by {
                if i + 1 == j {
                    assert(o.linked(j - 1));
                    if j + 1 < len {
                        assert(chain[j] == old_chain[j + 1]);
                    }
                } else if i < j {
                    assert(o.linked(i));
                    assert(old_chain[i] != old_chain[j - 1]);
                    o.lemma_at(i, prov);
                } else {
                    assert(o.linked(i + 1));
                    assert(old_chain[i + 1] != bi);
                    if j > 0 {
                        assert(old_chain[i + 1] != old_chain[j - 1]);
                    }
                    o.lemma_at(i + 1, prov);
                    if i + 1 < chain.len() {
                        assert(chain[i + 1] == old_chain[i + 2]);
                    }
                }
            }
            if j == 0 {
                assert(o.linked(0));
                if len > 1 {
                    assert(chain[0] == old_chain[1]);
                }
            }
            assert forall|x: int| #[trigger] self.owner@.contains_key(x) implies {
                &&& self.headers@.contains_key(record_page(x))
                &&& 0 <= self.owner@[x] < PAGE_RECORDS
                &&& x == record_addr(record_page(x), self.owner@[x])
                &&& in_use(self.word(record_page(x)), self.owner@[x])
            } by {
                assert(in_use(o.word(record_page(x)), o.owner@[x]));
                assert(record_page(x) != bi);
                assert(self.word(record_page(x)) == o.word(record_page(x)));
            }
            assert forall|c: int, k: int|
                self.headers@.contains_key(c) && 0 <= k < PAGE_RECORDS && #[trigger] in_use(self.word(c), k)
                    implies self.owner@.contains_key(record_addr(c, k)) by {
                assert(self.word(c) == o.word(c));
                assert(o.owner@.contains_key(record_addr(c, k)));
            }
        }
        Tracked(whole)
    }

    /// Returns an unused record of a record page that has one, changing neither the page buddy nor
    /// the source; when every record is in use, cuts a run of order 0, backs it, makes it a record
    /// page and returns its first record. Refuses only when every record is in use and the page
    /// buddy, with no free page in a held span, refused the run, or the source refused to back it,
    /// and then frees the run again.
    pub fn take<S: SpanSource>(&mut self, pb: &mut PageBuddy, src: &mut S, token: &mut Tracked<S::Token>) -> (r: Option<
        (*mut Record, Tracked<PointsTo<Record>>),
    >)
        requires
            old(src).serves(old(token)@),
            old(self).wf(*old(pb), old(src)@),
            old(pb).wf(old(src)@),
        ensures
            final(src).serves(final(token)@),
            final(pb).wf(final(src)@),
            final(self).wf(*final(pb), final(src)@),
            final(pb).spares() == old(pb).spares(),
            others_kept(*old(pb), *final(pb), old(src)@, final(src)@),
            forall|x: int, k: nat, n: nat| #[trigger]
                run_part(*old(pb), old(src)@, x, k, n) ==> run_part(*final(pb), final(src)@, x, k, n),
            !old(self).full() ==> {
                &&& r is Some
                &&& *final(pb) == *old(pb)
                &&& final(src)@ == old(src)@
                &&& final(self).pages() == old(self).pages()
            },
            match r {
                None => {
                    &&& old(self).full()
                    &&& final(self).pages() == old(self).pages()
                    &&& final(self).taken() == old(self).taken()
                    &&& runs(final(pb).used()) == runs(old(pb).used())
                    &&& forall|x: int, k: nat| #[trigger]
                        run_held(*old(pb), old(src)@, x, k) ==> run_held(*final(pb), final(src)@, x, k)
                    &&& page_refused(*old(pb), *final(pb), old(src)@, final(src)@)
                },
                Some((p, perm)) => {
                    let a = p@.addr as int;
                    &&& perm@.ptr() == p
                    &&& perm@.is_uninit()
                    &&& p@.provenance == old(src)@.provenance
                    &&& !old(self).taken().contains(a)
                    &&& final(self).taken() == old(self).taken().insert(a)
                    &&& old(self).full() ==> {
                        &&& !old(self).pages().contains(record_page(a))
                        &&& final(self).pages() == old(self).pages().insert(record_page(a))
                        &&& took_page(*old(pb), *final(pb), old(src)@, final(src)@, record_page(a))
                    }
                },
            },
    {
        let ghost prov = src@.provenance;
        let ghost s0 = src@;
        let ghost pb0 = *pb;
        if let Some((b, i)) = self.find_page(Ghost(prov)) {
            let (p, perm) = self.take_in(b, i, Ghost(prov));
            proof {
                assert forall|c: int| #[trigger] self.headers@.contains_key(c) implies run_held(pb0, s0, c, 0) by {
                    assert(old(self).headers@.contains_key(c));
                }
            }
            return Some((p, perm));
        }
        let q = match pb.alloc_run(src, token, 0) {
            Err(_) => {
                proof {
                    assert forall|x: int, k: nat| #[trigger] run_held(pb0, s0, x, k) implies run_held(*pb, src@, x, k) by {
                        lemma_recorded_keeps_held(pb0, s0, src@.refusals.last(), x, k);
                    }
                    assert forall|x: int, k: nat, n: nat| #[trigger] run_part(pb0, s0, x, k, n) implies run_part(
                        *pb,
                        src@,
                        x,
                        k,
                        n,
                    ) by {
                        lemma_recorded_keeps_part(pb0, s0, src@.refusals.last(), x, k, n);
                    }
                    assert forall|c: int| #[trigger] self.headers@.contains_key(c) implies run_held(*pb, src@, c, 0) by {
                        assert(run_held(pb0, s0, c, 0));
                    }
                    lemma_others_same(pb0, *pb, s0, src@);
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
            assert(pages(0) == 1);
            assert(cut_run(pb0, pb1, s0, s1, qi, 0));
            assert(pb1.used().contains_key(c));
            lemma_bounds(pb1, s1, qi);
            assert forall|x: int, k: nat| #[trigger] run_held(pb0, s0, x, k) implies x != qi && run_held(pb1, s1, x, k) by {
                lemma_cut_keeps_held(pb0, pb1, s0, s1, qi, 0, x, k);
            }
            assert forall|b: int| #[trigger] self.headers@.contains_key(b) implies b != qi && run_held(pb1, s1, b, 0) by {
                assert(run_held(pb0, s0, b, 0));
            }
        }
        match pb.back_run(src, token, q, 0, 1) {
            None => {
                let ghost pb2 = *pb;
                let ghost s2 = src@;
                pb.free_run(src, token, q);
                proof {
                    let pb3 = *pb;
                    let s3 = src@;
                    assert(freed(pb2, pb3, s2, s3, qi));
                    lemma_runs_restored(pb0, pb1, pb2, pb3, s0, s1, s2, s3, qi, 0);
                    assert(pb2.holds(qi));
                    assert forall|x: int, k: nat| #[trigger] run_held(pb0, s0, x, k) implies run_held(pb3, s3, x, k) by {
                        assert(x != qi && run_held(pb1, s1, x, k));
                        lemma_recorded_keeps_held(pb1, s1, s2.refusals.last(), x, k);
                        assert(run_held(pb2, s2, x, k));
                        lemma_freed_keeps_held(pb2, pb3, s2, s3, qi, x, k);
                    }
                    assert forall|x: int, k: nat, n: nat| #[trigger] run_part(pb0, s0, x, k, n) implies run_part(
                        pb3,
                        s3,
                        x,
                        k,
                        n,
                    ) by {
                        lemma_cut_keeps_part(pb0, pb1, s0, s1, qi, 0, x, k, n);
                        lemma_recorded_keeps_part(pb1, s1, s2.refusals.last(), x, k, n);
                        assert(run_part(pb2, s2, x, k, n));
                        lemma_freed_keeps_part(pb2, pb3, s2, s3, qi, x, k, n);
                    }
                    assert forall|b: int| #[trigger] self.headers@.contains_key(b) implies run_held(pb3, s3, b, 0) by {
                        assert(run_held(pb0, s0, b, 0));
                    }
                    assert(s3.refusals == s0.refusals.push(s2.refusals.last()));
                    let rf = s2.refusals.last();
                    assert(s2 == s1.recorded(rf));
                    assert(freed(pb1, pb3, s1.recorded(rf), s3, qi));
                    assert(back_refused(pb0, pb3, s0, s3));
                    lemma_cut_others(pb0, pb1, s0, s1, qi, 0);
                    lemma_others_same(pb1, pb2, s1, s2);
                    lemma_freed_others(pb2, pb3, s2, s2, s3, qi);
                    lemma_others_trans(pb0, pb1, pb2, s0, s1, s2);
                    lemma_others_trans(pb0, pb2, pb3, s0, s2, s3);
                }
                None
            },
            Some((ptr, raw)) => {
                let ghost s2 = src@;
                proof {
                    assert(!self.headers@.contains_key(qi));
                }
                let (p, perm) = self.add_page(q, ptr, raw, Ghost(prov));
                proof {
                    let pb2 = *pb;
                    assert(run_held(pb2, s2, qi, 0));
                    assert forall|b: int| #[trigger] self.headers@.contains_key(b) implies run_held(pb2, s2, b, 0) by {
                        if b != qi {
                            assert(old(self).headers@.contains_key(b));
                            lemma_backed_keeps_held(pb1, s1, pb1.span_base(c), qi, 1, b, 0);
                        }
                    }
                    assert forall|x: int, k: nat, n: nat| #[trigger] run_part(pb0, s0, x, k, n) implies run_part(
                        pb2,
                        s2,
                        x,
                        k,
                        n,
                    ) by {
                        lemma_cut_keeps_part(pb0, pb1, s0, s1, qi, 0, x, k, n);
                        lemma_backed_keeps_part(pb1, s1, pb1.span_base(c), qi, 1, x, k, n);
                    }
                    assert(took_page(pb0, pb2, s0, s2, qi));
                    lemma_cut_others(pb0, pb1, s0, s1, qi, 0);
                    lemma_span_base(pb1, s1, c);
                    lemma_others_at(pb1, pb2, s1, s2, pb1.span_base(c));
                    lemma_others_trans(pb0, pb1, pb2, s0, s1, s2);
                }
                Some((p, perm))
            },
        }
    }

    /// Takes back the record at `p` with the permission to its bytes; a record page left with no
    /// record in use is given back, its page released and its run freed. Every run held at a head
    /// that is no record page stays held.
    pub fn put<S: SpanSource>(&mut self, pb: &mut PageBuddy, src: &mut S, token: &mut Tracked<S::Token>, p: *mut Record, perm: Tracked<PointsTo<Record>>)
        requires
            old(src).serves(old(token)@),
            old(self).wf(*old(pb), old(src)@),
            old(pb).wf(old(src)@),
            old(self).taken().contains(p@.addr as int),
            perm@.ptr() == p,
            p@.provenance == old(src)@.provenance,
        ensures
            final(src).serves(final(token)@),
            final(pb).wf(final(src)@),
            final(self).wf(*final(pb), final(src)@),
            final(self).taken() == old(self).taken().remove(p@.addr as int),
            others_kept(*old(pb), *final(pb), old(src)@, final(src)@),
            forall|x: int, k: nat| #[trigger]
                run_held(*old(pb), old(src)@, x, k) && !old(self).pages().contains(x) ==> run_held(
                    *final(pb),
                    final(src)@,
                    x,
                    k,
                ),
            forall|x: int, k: nat, n: nat| #[trigger]
                run_part(*old(pb), old(src)@, x, k, n) && !old(self).pages().contains(x) ==> run_part(
                    *final(pb),
                    final(src)@,
                    x,
                    k,
                    n,
                ),
            if exists|x: int|
                #[trigger] old(self).taken().contains(x) && x != p@.addr as int && record_page(x) == record_page(
                    p@.addr as int,
                ) {
                &&& final(self).pages() == old(self).pages()
                &&& *final(pb) == *old(pb)
                &&& final(src)@ == old(src)@
            } else {
                &&& final(self).pages() == old(self).pages().remove(record_page(p@.addr as int))
                &&& gave_back(*old(pb), *final(pb), old(src)@, final(src)@, record_page(p@.addr as int))
            },
    {
        let ghost prov = src@.provenance;
        let ghost s0 = src@;
        let ghost pb0 = *pb;
        let ghost ai = p@.addr as int;
        let (b, empty) = self.give(p, perm, Ghost(prov));
        let ghost bi = b as int;
        proof {
            assert(old(self).owner@.contains_key(ai));
            old(self).lemma_page(bi, prov);
            if empty {
                assert forall|x: int|
                    #[trigger] old(self).taken().contains(x) && x != ai implies record_page(x) != bi by {
                    assert(self.taken().contains(x));
                }
            } else {
                let x = choose|x: int| #[trigger] self.taken().contains(x) && record_page(x) == bi;
                assert(old(self).taken().contains(x) && x != ai);
            }
        }
        if !empty {
            proof {
                assert forall|c: int| #[trigger] self.headers@.contains_key(c) implies run_held(pb0, s0, c, 0) by {
                    assert(old(self).headers@.contains_key(c));
                }
            }
            return;
        }
        proof {
            assert(run_held(pb0, s0, bi, 0));
            assert(pages(0) == 1);
            lemma_one_page(bi);
        }
        let whole = self.remove_page(b, Ghost(prov));
        pb.release_run(src, token, b, 0, 1, whole);
        let ghost pb1 = *pb;
        let ghost s1 = src@;
        proof {
            assert(s1.spans[pb0.span_base(span_of(bi))].backed.disjoint(run_pages(bi, 1)));
        }
        pb.free_run(src, token, b);
        proof {
            let pb2 = *pb;
            let s2 = src@;
            assert(freed(pb1, pb2, s1, s2, bi));
            assert(pb1.idle_spans() == pb0.idle_spans());
            assert(freed(pb0, pb2, s1, s2, bi));
            assert(gave_back(pb0, pb2, s0, s2, bi));
            pb0.lemma_view(s0);
            lemma_span_base(pb0, s0, span_of(bi));
            lemma_others_at(pb0, pb1, s0, s1, pb0.span_base(span_of(bi)));
            lemma_freed_others(pb1, pb2, s1, s1, s2, bi);
            lemma_others_trans(pb0, pb1, pb2, s0, s1, s2);
            assert forall|c: int| #[trigger] self.headers@.contains_key(c) implies run_held(pb2, s2, c, 0) by {
                assert(old(self).headers@.contains_key(c));
                self.lemma_page(c, prov);
                assert(c != bi);
                lemma_released_held(pb0, s0, pb0.span_base(span_of(bi)), bi, c);
                assert(run_held(pb1, s1, c, 0));
                lemma_freed_keeps_held(pb1, pb2, s1, s2, bi, c, 0);
            }
            assert forall|x: int, k: nat| #[trigger]
                run_held(pb0, s0, x, k) && !old(self).pages().contains(x) implies run_held(pb2, s2, x, k) by {
                lemma_released_keeps_held(pb0, s0, bi, 0, x, k);
                assert(run_held(pb1, s1, x, k));
                lemma_freed_keeps_held(pb1, pb2, s1, s2, bi, x, k);
            }
            assert forall|x: int, k: nat, n: nat| #[trigger]
                run_part(pb0, s0, x, k, n) && !old(self).pages().contains(x) implies run_part(pb2, s2, x, k, n) by {
                lemma_released_keeps_part(pb0, s0, bi, 1, x, k, n);
                assert(run_part(pb1, s1, x, k, n));
                lemma_freed_keeps_part(pb1, pb2, s1, s2, bi, x, k, n);
            }
        }
    }
}

} // verus!
