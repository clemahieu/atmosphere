// SPDX-License-Identifier: MIT
//! Large objects: each object over one block is a span of its own, recorded in the large-object map.
//!
//! An object of `size` bytes takes `pages_for(size)` pages from the base of a span of
//! `blocks_for(pages)` blocks, so it is block-aligned, and the page after its last is its record
//! page. The object's pages and the record page are backed as one run, in one call to the source's
//! `back`. The record page holds the object's node at its start: the object's base, its page count
//! and the record page of the next large object, or 0 at the end of the list. The nodes link every
//! large object into one list from `head`, so the map holds as many objects as the source gives;
//! design/page-buddy-metadata-in-the-span/ is the same reasoning for the page buddy's spans.
//!
//! The map does not own the source. Each operation takes it, and the map's invariant, `wf(src)`, is
//! stated over the source's view: each object is a reserved span of `blocks_for(pages)` blocks whose
//! backed pages are exactly the object's pages and its record page (`lemma_view`). A change to the
//! source that keeps every large object's span as it was keeps the invariant (`lemma_frame`), so the
//! page buddy can share the source.
//!
//! - `alloc_large(src, size)` refuses, and changes nothing but the refusal the source records,
//!   exactly when the source refused, in this call, the reserve of the span while holding what it
//!   held, or the back of the object's run while holding that and the new span, which it then gives
//!   back (`large_refused`). Otherwise it returns the base and the permission to the object's pages,
//!   at least `size` bytes, of a span that fits beside every reserved span, and the source's view
//!   is the old one with the span reserved and the run backed.
//! - `free_large(src, p, perm)` takes a large object's base and the permission to its pages, never
//!   refuses, and leaves the source's view the old one without the span.
//! - `contains(p)` says whether `p` is a large object's base.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::layout::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;

use crate::arch::*;
use crate::source::*;

verus! {

broadcast use {group_raw_ptr_axioms, vstd::set_lib::range_set_properties};

/// The pages an object of `size` bytes takes, one or more: `size` rounded up to whole pages.
pub open spec fn pages_for(size: nat) -> nat {
    ((size - 1) / PAGE_BYTES as int + 1) as nat
}

/// The blocks of the span of an object of `pages` pages: enough for its pages and its record page.
pub open spec fn blocks_for(pages: nat) -> nat {
    pages / BLOCK_PAGES as nat + 1
}

/// The record page of the object of `pages` pages at `b`: the page after its last.
pub open spec fn record(b: int, pages: nat) -> int {
    b + pages * PAGE_BYTES as int
}

/// The span of the object of `pages` pages at `b`, as the map holds it: its object's pages and its
/// record page backed, and no other.
pub open spec fn large_span(b: int, pages: nat) -> Span {
    Span { blocks: blocks_for(pages), backed: run_pages(b, pages + 1) }
}

/// The pointer to the node of the object of `pages` pages at `b`.
pub open spec fn record_ptr(b: int, pages: nat, provenance: Provenance) -> *mut LargeNode {
    ptr_mut_from_data(PtrData { addr: record(b, pages) as usize, provenance, metadata: () })
}

/// The refusal `r` is of a request `alloc_large` makes for an object of `pages` pages of a source
/// whose view is `s`: the reserve of its span while the source held the spans `s` holds, or the back
/// of the object's run and record page from the base of a span that fits beside them, while it held
/// them and that span, unbacked.
pub open spec fn large_refusal(s: SourceView, r: Refusal, pages: nat) -> bool {
    match r.request {
        Request::Reserve { blocks } => blocks == blocks_for(pages) && r.spans == s.spans,
        Request::Back { span, start, pages: n } => {
            &&& start == span
            &&& n == pages + 1
            &&& s.fits(span, blocks_for(pages))
            &&& r.spans == s.reserved(span, blocks_for(pages)).spans
        },
    }
}

/// The requests the source grants for an object of `pages` pages whose span is at `b`: the reserve
/// of its span and the back of its run and record page.
pub open spec fn large_grants(b: int, pages: nat) -> Seq<Request> {
    seq![Request::Reserve { blocks: blocks_for(pages) }, Request::Back { span: b, start: b, pages: pages + 1 }]
}

/// `after` is `before` with one refusal recorded, of a request `alloc_large` makes for an object of
/// `pages` pages of a source whose view is `before`, and nothing else changed but, when the back
/// was refused, the grant of the object's reserve before it.
pub open spec fn large_refused(before: SourceView, after: SourceView, pages: nat) -> bool {
    let r = after.refusals.last();
    &&& after == before.granted(granted_before(r, blocks_for(pages))).recorded(r)
    &&& large_refusal(before, r, pages)
}

/// An object of `size` bytes, more than one block's and no more than isize::MAX, takes more pages
/// than a block holds and at least `size` bytes, and its pages and record page fit in its span.
proof fn lemma_sizes(size: nat)
    requires
        BLOCK_BYTES < size <= isize::MAX,
    ensures
        pages_for(size) > BLOCK_PAGES,
        size <= pages_for(size) * PAGE_BYTES,
        pages_for(size) * PAGE_BYTES <= isize::MAX + PAGE_BYTES,
{
    let pb = PAGE_BYTES as int;
    let s1 = size - 1;
    lemma_fundamental_div_mod(s1, pb);
    let q = s1 / pb;
    let r = s1 % pb;
    assert(q >= BLOCK_PAGES) by {
        lemma_div_is_ordered(BLOCK_PAGES as int * pb, s1, pb);
        lemma_div_by_multiple(BLOCK_PAGES as int, pb);
    }
    assert(size <= (q + 1) * pb) by (nonlinear_arith)
        requires
            s1 == pb * q + r,
            r < pb,
            size == s1 + 1,
    ;
    assert((q + 1) * pb == pb * q + pb) by (nonlinear_arith);
}

/// An object of `pages` pages and its record page fit in the span `blocks_for(pages)` gives it.
pub proof fn lemma_blocks_for(pages: nat)
    ensures
        blocks_for(pages) > 0,
        (pages + 1) * PAGE_BYTES <= span_bytes(blocks_for(pages)),
        pages * PAGE_BYTES + PAGE_BYTES == (pages + 1) * PAGE_BYTES,
{
    let bp = BLOCK_PAGES as int;
    lemma_fundamental_div_mod(pages as int, bp);
    let q = pages as int / bp;
    let r = pages as int % bp;
    assert(pages + 1 <= bp * (q + 1)) by (nonlinear_arith)
        requires
            pages == bp * q + r,
            r < bp,
    ;
    assert((pages + 1) * PAGE_BYTES <= (q + 1) * BLOCK_BYTES) by (nonlinear_arith)
        requires
            pages + 1 <= bp * (q + 1),
            BLOCK_BYTES == PAGE_BYTES * bp,
            PAGE_BYTES > 0,
    ;
    assert(pages * PAGE_BYTES + PAGE_BYTES == (pages + 1) * PAGE_BYTES) by (nonlinear_arith);
}

/// The record page of an object at a block-aligned base is a page, aligned for a node, and a node
/// fits in it with room to spare.
proof fn lemma_record(b: int, pages: nat)
    requires
        b % BLOCK_BYTES as int == 0,
    ensures
        b % PAGE_BYTES as int == 0,
        record(b, pages) % PAGE_BYTES as int == 0,
        record(b, pages) % align_of::<LargeNode>() as int == 0,
        0 < size_of::<LargeNode>() < PAGE_BYTES,
{
    let pb = PAGE_BYTES as int;
    let m = record(b, pages);
    lemma_large_node_layout();
    lemma_mod_mod(b, pb, BLOCK_PAGES as int);
    lemma_mod_multiples_vanish(pages as int, b, pb);
    assert(m % pb == 0);
    let al = align_of::<LargeNode>() as int;
    lemma_fundamental_div_mod(m, pb);
    lemma_fundamental_div_mod(pb, al);
    let x = m / pb;
    let r = pb / al;
    assert(m == (r * x) * al) by (nonlinear_arith)
        requires
            m == pb * x,
            pb == al * r,
    ;
    lemma_mod_multiples_basic(r * x, al);
}

/// The pointer to the node at the record page `r`, with the provenance of `hp`.
fn record_at(hp: *mut u8, r: usize) -> (p: *mut LargeNode)
    ensures
        p == ptr_mut_from_data::<LargeNode>(PtrData { addr: r, provenance: hp@.provenance, metadata: () }),
{
    hp.with_addr(r) as *mut LargeNode
}

/// A large object's node, at the start of its record page: the record page of the next large
/// object, or 0 at the end of the list, the object's base and its pages.
#[repr(C)]
pub struct LargeNode {
    next: usize,
    base: usize,
    pages: usize,
}

/// The large-object map.
pub struct LargeMap {
    /// The record page of the first object, while one is held; it carries the source's provenance.
    head: Option<*mut u8>,
    /// The bases of the objects, in the order their nodes link them.
    chain: Ghost<Seq<int>>,
    // Only proofs read the nodes and the rests, and a cargo build erases them.
    /// The permission to each object's node, by base.
    #[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
    nodes: Tracked<Map<int, PointsTo<LargeNode>>>,
    /// The permission to the rest of each object's record page, after its node, by base.
    #[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
    rests: Tracked<Map<int, PointsToRaw>>,
}

impl LargeMap {
    /// The node of the object at `b`.
    spec fn node(&self, b: int) -> LargeNode {
        self.nodes@[b].value()
    }

    /// The record page of the object at `b`.
    spec fn record_of(&self, b: int) -> int {
        record(b, self.node(b).pages as nat)
    }

    /// The large objects, by base, with their pages.
    pub closed spec fn objects(&self) -> Map<int, nat> {
        Map::new(self.nodes@.dom(), |b: int| self.node(b).pages as nat)
    }

    /// The node of the object at `b` is at its record page, names it and its pages, more than one
    /// block's; the source holds its span as `large_span` says; and the rest of the record page is
    /// held beside the node.
    spec fn node_wf(&self, b: int, src: SourceView) -> bool {
        let n = self.node(b).pages as nat;
        &&& self.nodes@[b].ptr() == record_ptr(b, n, src.provenance)
        &&& self.nodes@[b].is_init()
        &&& self.node(b).base as int == b
        &&& n > BLOCK_PAGES
        &&& src.spans.contains_key(b)
        &&& src.spans[b] == large_span(b, n)
        &&& self.rests@.contains_key(b)
        &&& self.rests@[b].is_range(record(b, n) + size_of::<LargeNode>(), PAGE_BYTES - size_of::<LargeNode>())
        &&& self.rests@[b].provenance() == src.provenance
    }

    /// The node at position `i` of the chain links the record page of the object after it, or ends
    /// the list.
    spec fn linked(&self, i: int) -> bool {
        self.node(self.chain@[i]).next as int == if i + 1 < self.chain@.len() {
            self.record_of(self.chain@[i + 1])
        } else {
            0
        }
    }

    /// The list from `head` links exactly the objects, each node well formed over the source whose
    /// view is `src`.
    pub closed spec fn wf(&self, src: SourceView) -> bool {
        &&& self.chain@.no_duplicates()
        &&& forall|b: int|
            #![trigger self.nodes@.contains_key(b)]
            #![trigger self.chain@.contains(b)]
            self.nodes@.contains_key(b) <==> self.chain@.contains(b)
        &&& forall|b: int| #[trigger] self.nodes@.contains_key(b) ==> self.node_wf(b, src)
        &&& forall|i: int| 0 <= i < self.chain@.len() ==> #[trigger] self.linked(i)
        &&& match self.head {
            None => self.chain@.len() == 0,
            Some(h) => {
                &&& self.chain@.len() > 0
                &&& h@.addr as int == self.record_of(self.chain@[0])
                &&& h@.provenance == src.provenance
            },
        }
    }

    /// An object's node is well formed, the object is in the chain, and its span lies in the
    /// address space, block-aligned above address 0, with room for its pages and record page.
    proof fn lemma_base(&self, b: int, src: SourceView)
        requires
            self.wf(src),
            src.wf(),
            self.nodes@.contains_key(b),
        ensures
            self.node_wf(b, src),
            self.chain@.contains(b),
            self.chain@.len() > 0,
            self.head is Some,
            b > 0,
            b % BLOCK_BYTES as int == 0,
            b % PAGE_BYTES as int == 0,
            self.record_of(b) % PAGE_BYTES as int == 0,
            self.record_of(b) % align_of::<LargeNode>() as int == 0,
            0 < size_of::<LargeNode>() < PAGE_BYTES,
            b < self.record_of(b),
            self.record_of(b) + PAGE_BYTES <= b + span_bytes(blocks_for(self.node(b).pages as nat)),
            b + span_bytes(blocks_for(self.node(b).pages as nat)) <= usize::MAX as int + 1,
            self.node(b).pages * PAGE_BYTES + PAGE_BYTES == (self.node(b).pages + 1) * PAGE_BYTES,
    {
        let n = self.node(b).pages as nat;
        assert(self.node_wf(b, src));
        assert(src.released_span(b).fits(b, src.spans[b].blocks));
        lemma_blocks_for(n);
        lemma_record(b, n);
        assert(n * PAGE_BYTES > 0) by (nonlinear_arith)
            requires
                n > 0,
                PAGE_BYTES > 0,
        ;
    }

    /// The object at position `i` of the chain is held, its node well formed and linked.
    proof fn lemma_at(&self, i: int, src: SourceView)
        requires
            self.wf(src),
            src.wf(),
            0 <= i < self.chain@.len(),
        ensures
            self.nodes@.contains_key(self.chain@[i]),
            self.node_wf(self.chain@[i], src),
            self.linked(i),
            self.chain@[i] < self.record_of(self.chain@[i]),
            0 < self.record_of(self.chain@[i]),
            self.record_of(self.chain@[i]) + PAGE_BYTES <= usize::MAX as int + 1,
    {
        assert(self.chain@.contains(self.chain@[i]));
        self.lemma_base(self.chain@[i], src);
    }

    /// The invariant on the view: every large object is a reserved span of `blocks_for(pages)`
    /// blocks, its pages more than one block's, whose backed pages are exactly its pages and its
    /// record page.
    pub proof fn lemma_view(&self, src: SourceView)
        requires
            self.wf(src),
        ensures
            forall|b: int| #[trigger]
                self.objects().contains_key(b) ==> {
                    &&& self.objects()[b] > BLOCK_PAGES
                    &&& src.spans.contains_key(b)
                    &&& src.spans[b] == large_span(b, self.objects()[b])
                },
    {
        assert forall|b: int| #[trigger] self.objects().contains_key(b) implies {
            &&& self.objects()[b] > BLOCK_PAGES
            &&& src.spans.contains_key(b)
            &&& src.spans[b] == large_span(b, self.objects()[b])
        } by {
            assert(self.node_wf(b, src));
        }
    }

    /// A change to the source that keeps its provenance and every large object's span keeps the
    /// map well formed.
    pub proof fn lemma_frame(&self, s: SourceView, t: SourceView)
        requires
            self.wf(s),
            t.provenance == s.provenance,
            forall|b: int| #[trigger]
                self.objects().contains_key(b) ==> t.spans.contains_key(b) && t.spans[b] == s.spans[b],
        ensures
            self.wf(t),
    {
        assert forall|b: int| #[trigger] self.nodes@.contains_key(b) implies self.node_wf(b, t) by {
            assert(self.node_wf(b, s));
            assert(self.objects().contains_key(b));
        }
    }

    /// The map holding no object.
    pub fn new() -> (r: Self)
        ensures
            r.objects() == Map::<int, nat>::empty(),
            forall|s: SourceView| #[trigger] r.wf(s),
    {
        let r = LargeMap {
            head: None,
            chain: Ghost(Seq::empty()),
            nodes: Tracked(Map::tracked_empty()),
            rests: Tracked(Map::tracked_empty()),
        };
        assert(r.objects() =~= Map::<int, nat>::empty());
        r
    }

    /// The place of the object at `p` in the list, when `p` is a large object's base: the record
    /// page of the object before it, or 0 when it is the first, and its own record page.
    fn locate(&self, p: usize, Ghost(src): Ghost<SourceView>) -> (r: Option<(usize, usize)>)
        requires
            self.wf(src),
            src.wf(),
        ensures
            r is Some == self.objects().contains_key(p as int),
            r matches Some((prev, cur)) ==> {
                &&& cur as int == self.record_of(p as int)
                &&& exists|j: int|
                    0 <= j < self.chain@.len() && #[trigger] self.chain@[j] == p as int && prev as int == if j == 0 {
                        0
                    } else {
                        self.record_of(self.chain@[j - 1])
                    }
            },
    {
        let hp = match self.head {
            None => {
                proof {
                    if self.nodes@.contains_key(p as int) {
                        assert(self.chain@.contains(p as int));
                    }
                }
                return None;
            },
            Some(h) => h,
        };
        let mut prev: usize = 0;
        let mut cur: usize = hp.addr();
        let ghost mut j: int = 0;
        proof {
            self.lemma_at(0, src);
        }
        while cur != 0
            invariant
                self.wf(src),
                src.wf(),
                self.head == Some(hp),
                0 <= j <= self.chain@.len(),
                cur as int == if j < self.chain@.len() { self.record_of(self.chain@[j]) } else { 0 },
                prev as int == if j == 0 { 0 } else { self.record_of(self.chain@[j - 1]) },
                forall|i: int| 0 <= i < j ==> #[trigger] self.chain@[i] != p as int,
            decreases self.chain@.len() - j,
        {
            proof {
                if j >= self.chain@.len() {
                    assert(cur == 0);
                }
                self.lemma_at(j, src);
            }
            let ghost b = self.chain@[j];
            let ptr = record_at(hp, cur);
            let tracked perm = self.nodes.borrow().tracked_borrow(b);
            let node = ptr_ref(ptr, Tracked(perm));
            if node.base == p {
                proof {
                    assert(self.chain@[j] == p as int);
                    assert(self.nodes@.contains_key(p as int));
                }
                return Some((prev, cur));
            }
            prev = cur;
            cur = node.next;
            proof {
                j = j + 1;
                if j < self.chain@.len() {
                    self.lemma_at(j, src);
                }
            }
        }
        proof {
            if j < self.chain@.len() {
                self.lemma_at(j, src);
            }
            if self.nodes@.contains_key(p as int) {
                assert(self.chain@.contains(p as int));
                let i = choose|i: int| 0 <= i < self.chain@.len() && self.chain@[i] == p as int;
                assert(self.chain@[i] != p as int);
            }
        }
        None
    }

    /// Whether `p` is a large object's base.
    pub fn contains(&self, p: usize, Ghost(src): Ghost<SourceView>) -> (r: bool)
        requires
            self.wf(src),
            src.wf(),
        ensures
            r == self.objects().contains_key(p as int),
    {
        self.locate(p, Ghost(src)).is_some()
    }

    /// Reserves a span for an object of `size` bytes, more than one block's, and backs the object's
    /// pages and its record page; or refuses, when the source refused the reserve or the back in
    /// this call, and changes nothing but the refusal the source records.
    pub fn alloc_large<S: SpanSource>(&mut self, src: &mut S, size: usize) -> (r: Option<(*mut u8, Tracked<PointsToRaw>)>)
        requires
            old(self).wf(old(src)@),
            old(src)@.wf(),
            BLOCK_BYTES < size <= isize::MAX as usize,
        ensures
            final(src)@.wf(),
            final(self).wf(final(src)@),
            match r {
                None => {
                    &&& final(self).objects() == old(self).objects()
                    &&& large_refused(old(src)@, final(src)@, pages_for(size as nat))
                },
                Some((p, perm)) => {
                    let b = p@.addr as int;
                    let n = pages_for(size as nat);
                    &&& p@.provenance == old(src)@.provenance
                    &&& old(src)@.fits(b, blocks_for(n))
                    &&& !old(self).objects().contains_key(b)
                    &&& final(src)@ == old(src)@.reserved(b, blocks_for(n)).backed_run(b, b, n + 1)
                    &&& final(self).objects() == old(self).objects().insert(b, n)
                    &&& perm@.is_range(b, n * PAGE_BYTES)
                    &&& perm@.provenance() == old(src)@.provenance
                    &&& size <= n * PAGE_BYTES
                },
            },
    {
        let ghost start = src@;
        let ghost old_objects = self.objects();
        let pages = (size - 1) / PAGE_BYTES + 1;
        let ghost n = pages as nat;
        proof {
            lemma_sizes(size as nat);
            lemma_blocks_for(n);
            assert(n == pages_for(size as nat));
        }
        let blocks = pages / BLOCK_PAGES + 1;
        let base = match src.reserve(blocks) {
            None => {
                proof {
                    self.lemma_frame(start, src@);
                    lemma_granted_none(start);
                }
                return None;
            },
            Some(base) => base,
        };
        let b = base.addr();
        let ghost bi = b as int;
        let ghost reserved = src@;
        proof {
            assert(!start.spans.contains_key(bi)) by {
                if start.spans.contains_key(bi) {
                    assert(start.apart(bi, blocks as nat, bi));
                }
            }
            assert(!old_objects.contains_key(bi)) by {
                if old_objects.contains_key(bi) {
                    assert(self.node_wf(bi, start));
                }
            }
            lemma_record(bi, n);
        }
        let perm = match src.back(Ghost(bi), b, pages + 1) {
            None => {
                src.release_span(b);
                proof {
                    assert(src@.spans =~= start.spans);
                    let r = Refusal {
                        request: Request::Back { span: bi, start: bi, pages: n + 1 },
                        spans: start.reserved(bi, blocks as nat).spans,
                    };
                    assert(src@.grants =~= start.grants + seq![Request::Reserve { blocks: blocks as nat }]);
                    assert(src@ == start.granted(granted_before(r, blocks as nat)).recorded(r));
                    self.lemma_frame(start, src@);
                }
                return None;
            },
            Some(perm) => perm,
        };
        let rec = b + pages * PAGE_BYTES;
        let ghost ri = rec as int;
        let tracked run = perm.get();
        let ghost object = Set::range(bi, ri);
        let tracked (obj, page) = run.split(object);
        let ghost first = Set::range(ri, ri + size_of::<LargeNode>() as int);
        proof {
            assert(page.dom() =~= Set::range(ri, ri + PAGE_BYTES));
        }
        let tracked (node_raw, rest) = page.split(first);
        let tracked mut typed = node_raw.into_typed::<LargeNode>(rec);
        let ptr = record_at(base, rec);
        let next = match self.head {
            None => 0,
            Some(h) => h.addr(),
        };
        ptr_mut_write(ptr, Tracked(&mut typed), LargeNode { next, base: b, pages });
        proof {
            self.nodes.borrow_mut().tracked_insert(bi, typed);
            self.rests.borrow_mut().tracked_insert(bi, rest);
        }
        let ghost old_chain = self.chain@;
        self.chain = Ghost(seq![bi] + old_chain);
        self.head = Some(base.with_addr(rec));
        proof {
            let fin = src@;
            assert(fin.spans[bi].backed =~= run_pages(bi, n + 1));
            assert(fin.spans[bi] == large_span(bi, n));
            assert(self.rests@[bi].dom() =~= Set::range(ri + size_of::<LargeNode>(), ri + PAGE_BYTES));
            assert(self.record_of(bi) == ri);
            assert forall|i: int| 0 <= i < old_chain.len() implies old_chain[i] != bi by {
                old(self).lemma_at(i, start);
            }
            let chain = self.chain@;
            assert forall|i: int| 0 <= i < old_chain.len() implies #[trigger] chain[i + 1] == old_chain[i] by {}
            assert(chain[0] == bi);
            assert(chain.no_duplicates()) by {
                assert forall|i: int, i2: int| 0 <= i < chain.len() && 0 <= i2 < chain.len() && i != i2 implies chain[i] != chain[i2] by {
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
            assert forall|c: int| #![trigger self.nodes@.contains_key(c)] #![trigger self.chain@.contains(c)] self.nodes@.contains_key(c) <==> self.chain@.contains(c) by {
                if self.chain@.contains(c) {
                    let i = choose|i: int| 0 <= i < chain.len() && chain[i] == c;
                    if i > 0 {
                        assert(chain[i] == old_chain[i - 1]);
                        assert(old_chain.contains(c));
                        assert(old(self).nodes@.contains_key(c));
                    }
                }
                if self.nodes@.contains_key(c) && c != bi {
                    assert(old(self).nodes@.contains_key(c));
                    assert(old_chain.contains(c));
                    let i = choose|i: int| 0 <= i < old_chain.len() && old_chain[i] == c;
                    assert(chain[i + 1] == c);
                }
            }
            assert forall|c: int| #[trigger] self.nodes@.contains_key(c) implies self.node_wf(c, fin) by {
                if c != bi {
                    assert(old(self).node_wf(c, start));
                    assert(start.spans.contains_key(c));
                    assert(fin.spans[c] == start.spans[c]);
                }
            }
            assert forall|i: int| 0 <= i < self.chain@.len() implies #[trigger] self.linked(i) by {
                if i > 0 {
                    assert(old(self).linked(i - 1));
                    assert(chain[i] == old_chain[i - 1]);
                    old(self).lemma_at(i - 1, start);
                    if i + 1 < chain.len() {
                        assert(chain[i + 1] == old_chain[i]);
                        old(self).lemma_at(i, start);
                    }
                } else if old_chain.len() > 0 {
                    assert(chain[1] == old_chain[0]);
                    old(self).lemma_at(0, start);
                }
            }
            assert(self.objects() =~= old_objects.insert(bi, n));
        }
        Some((base, Tracked(obj)))
    }

    /// Takes back the large object at `p` with the permission to its pages, and gives its span back
    /// to the source, record page and all.
    pub fn free_large<S: SpanSource>(&mut self, src: &mut S, p: usize, perm: Tracked<PointsToRaw>)
        requires
            old(self).wf(old(src)@),
            old(src)@.wf(),
            old(self).objects().contains_key(p as int),
            perm@.is_range(p as int, old(self).objects()[p as int] * PAGE_BYTES),
            perm@.provenance() == old(src)@.provenance,
        ensures
            final(src)@.wf(),
            final(self).wf(final(src)@),
            final(self).objects() == old(self).objects().remove(p as int),
            final(src)@ == old(src)@.released_span(p as int),
    {
        let ghost start = src@;
        let ghost old_objects = self.objects();
        let ghost old_chain = self.chain@;
        let ghost pi = p as int;
        let (prev, cur) = match self.locate(p, Ghost(start)) {
            None => {
                proof {
                    assert(false);
                }
                return;
            },
            Some(r) => r,
        };
        let ghost j = choose|j: int|
            0 <= j < old_chain.len() && #[trigger] old_chain[j] == pi && prev as int == if j == 0 {
                0
            } else {
                self.record_of(old_chain[j - 1])
            };
        let ghost n = self.node(pi).pages as nat;
        proof {
            self.lemma_base(pi, start);
            self.lemma_at(j, start);
            if j > 0 {
                self.lemma_at(j - 1, start);
            }
            if j + 1 < old_chain.len() {
                self.lemma_at(j + 1, start);
            }
        }
        let hp = self.head.unwrap();
        let ptr = record_at(hp, cur);
        let tracked mut nperm = self.nodes.borrow_mut().tracked_remove(pi);
        let node = ptr_mut_read(ptr, Tracked(&mut nperm));
        let next = node.next;
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
                assert(q != pi);
            }
            let pptr = record_at(hp, prev);
            let tracked mut pperm = self.nodes.borrow_mut().tracked_remove(q);
            let mut pnode = ptr_mut_read(pptr, Tracked(&mut pperm));
            pnode.next = next;
            ptr_mut_write(pptr, Tracked(&mut pperm), pnode);
            proof {
                self.nodes.borrow_mut().tracked_insert(q, pperm);
            }
        }
        self.chain = Ghost(old_chain.remove(j));
        let tracked rest = self.rests.borrow_mut().tracked_remove(pi);
        let tracked node_raw = nperm.into_raw();
        let tracked page = node_raw.join(rest);
        proof {
            assert(old_objects[pi] == n);
            assert(cur as int == pi + n * PAGE_BYTES);
            assert(page.dom() =~= Set::range(cur as int, cur as int + PAGE_BYTES));
            assert(perm@.dom() =~= Set::range(pi, cur as int));
        }
        let tracked whole = perm.get().join(page);
        proof {
            assert(whole.dom() =~= Set::range(pi, pi + (n + 1) * PAGE_BYTES));
        }
        src.release(Ghost(pi), p, node.pages + 1, Tracked(whole));
        proof {
            assert(src@.spans[pi].backed =~= Set::<int>::empty());
        }
        src.release_span(p);
        proof {
            let fin = src@;
            assert(fin.spans =~= start.spans.remove(pi));
            assert(fin == start.released_span(pi));
            let chain = self.chain@;
            let len = old_chain.len();
            assert(chain.len() == len - 1);
            assert forall|i: int| 0 <= i < len - 1 implies #[trigger] chain[i] == if i < j { old_chain[i] } else { old_chain[i + 1] } by {}
            assert(chain.no_duplicates()) by {
                assert forall|i: int, i2: int| 0 <= i < chain.len() && 0 <= i2 < chain.len() && i != i2 implies chain[i] != chain[i2] by {
                    let oi = if i < j { i } else { i + 1 };
                    let oi2 = if i2 < j { i2 } else { i2 + 1 };
                    assert(chain[i] == old_chain[oi]);
                    assert(chain[i2] == old_chain[oi2]);
                }
            }
            assert forall|x: int| #![trigger self.nodes@.contains_key(x)] #![trigger self.chain@.contains(x)] self.nodes@.contains_key(x) <==> self.chain@.contains(x) by {
                if self.chain@.contains(x) {
                    let i = choose|i: int| 0 <= i < chain.len() && chain[i] == x;
                    let oi = if i < j { i } else { i + 1 };
                    assert(old_chain[oi] == x);
                    assert(oi != j);
                    assert(old_chain.contains(x));
                    assert(old(self).nodes@.contains_key(x));
                }
                if self.nodes@.contains_key(x) {
                    assert(old(self).nodes@.contains_key(x));
                    assert(old_chain.contains(x));
                    let oi = choose|oi: int| 0 <= oi < len && old_chain[oi] == x;
                    assert(oi != j);
                    let i = if oi < j { oi } else { oi - 1 };
                    assert(chain[i] == x);
                }
            }
            assert forall|x: int| #[trigger] self.nodes@.contains_key(x) implies self.node_wf(x, fin) by {
                assert(old(self).node_wf(x, start));
                assert(start.spans[x] == fin.spans[x]);
            }
            assert forall|i: int| 0 <= i < chain.len() implies #[trigger] self.linked(i) by {
                if i + 1 == j {
                    assert(old(self).linked(j - 1));
                    if j + 1 < len {
                        assert(chain[j] == old_chain[j + 1]);
                    }
                } else if i < j {
                    assert(old(self).linked(i));
                    assert(old_chain[i] != old_chain[j - 1]);
                    old(self).lemma_at(i, start);
                    old(self).lemma_at(i + 1, start);
                } else {
                    assert(old(self).linked(i + 1));
                    assert(old_chain[i + 1] != pi);
                    if j > 0 {
                        assert(old_chain[i + 1] != old_chain[j - 1]);
                    }
                    old(self).lemma_at(i + 1, start);
                    if i + 1 < chain.len() {
                        assert(chain[i + 1] == old_chain[i + 2]);
                        old(self).lemma_at(i + 2, start);
                    }
                }
            }
            if j == 0 {
                assert(old(self).linked(0));
                if len > 1 {
                    assert(chain[0] == old_chain[1]);
                    old(self).lemma_at(1, start);
                }
            }
            assert(self.objects() =~= old_objects.remove(pi));
        }
    }
}

} // verus!
