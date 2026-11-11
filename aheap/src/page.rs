// SPDX-License-Identifier: MIT
//! The page buddy: page runs cut from spans of two blocks each, a block buddy per block.
//!
//! It owns the span source. Each span it holds, a run span, is a reserved span of SPAN_BLOCKS
//! blocks, and each of its blocks is cut into runs by a block buddy of its own. The span's metadata
//! page, the first page of its second block, is that block's first run, of order 0: it is backed
//! with the span, given back with it, and holds the span's node, the two block buddies' records and
//! the base of the next held span. The nodes link every held span into one list from `head`, so the
//! page buddy holds as many run spans as the source gives, and every page of a held span is in a
//! free block, an allocated run or its metadata page. The first block holds no record, so a run span
//! can give its whole first block; design/page-buddy-metadata-in-the-span/.
//!
//! The view is by block. `spans` maps the base of each block of each held span to its buddy's
//! blocks, the metadata page among them as an allocated block of order 0 at page 0 of the second
//! block; `used` maps it to the runs allocated to callers in it, so no metadata page is in `used`.
//! `metas` holds the metadata pages, which are the bases of the second blocks, and `span_base` names
//! the span a block is in.
//!
//! - `alloc_run(k)` takes from the block with a free block of the smallest order at or above k,
//!   across every held span; only when none has one does it reserve a new span. It refuses, and
//!   changes no held span, exactly when no held span has such a block and the source refused to
//!   reserve the span or to back its metadata page.
//! - `free_run(p)` takes back the run at p and never refuses. A span left with no run is given back
//!   to the source, unless fewer than the configured spares are idle, when it stays as a spare. The
//!   run's pages must be unbacked.
//! - `back_run(p, k)` backs the pages of the allocated run at p through the source and returns a
//!   pointer to it with the permission to its bytes, or refuses and changes nothing else;
//!   `release_run(p, k, perm)` gives them back. A run `alloc_run` returns has no page backed: the
//!   page buddy does not back the runs it cuts, and its caller backs what it writes.
//!
//! Each states the source's view after it exactly: a refusal by the source leaves it as it was with
//! that one refusal counted, so `Source` and a `None` from `back_run` answer only a refusal the source
//! made in the call; a run from a held span leaves it as it was, a new span is reserved with its
//! metadata page backed (`took_span`), and a span given back is released, so a sequence that frees
//! every run it cut ends at the view it started from.
//!
//! `lemma_view` states the invariant on the view, among it where each metadata page lies and that
//! a held span's first block with no run is the initial block, so `lemma_idle_fits` shows a run of
//! any order fits while such a span is held.
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

broadcast use {group_raw_ptr_axioms, vstd::set_lib::range_set_properties};

/// The blocks of a run span: each is cut into runs, and the second's first page is the metadata
/// page.
pub const SPAN_BLOCKS: usize = 2;

/// Why `alloc_run` refused.
pub enum Refused {
    /// The source refused to reserve a span, or to back its metadata page, in this call: its view
    /// counts one more refusal.
    Source,
}

/// The base of the block that holds address `p`.
pub open spec fn span_of(p: int) -> int {
    p - p % BLOCK_BYTES as int
}

/// The page of its block that address `p` is in.
pub open spec fn page_of(p: int) -> int {
    (p % BLOCK_BYTES as int) / PAGE_BYTES as int
}

/// The metadata page of the run span at `b`: the first page of its second block, which is that
/// block's base.
pub open spec fn meta_page(b: int) -> int {
    b + BLOCK_BYTES as int
}

/// The allocated runs of a block's blocks, by head, with their orders.
pub open spec fn used_of(blocks: Map<int, Block>) -> Map<int, nat> {
    Map::new(blocks.dom().filter(|h: int| !blocks[h].free), |h: int| blocks[h].order)
}

/// The held spans whose blocks `used` maps to no run, by metadata page.
pub open spec fn idle_of(used: Map<int, Map<int, nat>>, metas: Set<int>) -> Set<int> {
    metas.filter(
        |m: int|
            used[m].dom() == Set::<int>::empty() && used[m - BLOCK_BYTES as int].dom() == Set::<
                int,
            >::empty(),
    )
}

/// The base of the span whose block is at `c`, given the metadata pages: the block before `c` when
/// `c` is a second block.
pub open spec fn base_in(metas: Set<int>, c: int) -> int {
    if metas.contains(c) {
        c - BLOCK_BYTES as int
    } else {
        c
    }
}

/// `used` with the two blocks of a new span at `b`, neither holding a run.
pub open spec fn fresh(used: Map<int, Map<int, nat>>, b: int) -> Map<int, Map<int, nat>> {
    used.insert(b, Map::<int, nat>::empty()).insert(meta_page(b), Map::<int, nat>::empty())
}

/// The pointer to the node of the run span at `b`.
pub open spec fn node_ptr(b: int, provenance: Provenance) -> *mut Node {
    ptr_mut_from_data(PtrData { addr: meta_page(b) as usize, provenance, metadata: () })
}

/// Address `a` is a page of one of the runs `u` holds, by head, in the block at `x`.
pub open spec fn in_runs(x: int, u: Map<int, nat>, a: int) -> bool {
    exists|q: int| #[trigger] u.contains_key(q) && run_pages(x + q * PAGE_BYTES as int, pages(u[q]) as nat).contains(a)
}

/// The span at `b` is a reserved span of SPAN_BLOCKS blocks whose metadata page is backed and whose
/// other backed pages lie in the runs `lo` holds in its first block or `hi` holds in its second.
pub open spec fn held(src: SourceView, b: int, lo: Map<int, nat>, hi: Map<int, nat>) -> bool {
    &&& src.spans.contains_key(b)
    &&& src.spans[b].blocks == SPAN_BLOCKS
    &&& src.spans[b].backed.contains(meta_page(b))
    &&& forall|a: int| #[trigger]
        src.spans[b].backed.contains(a) ==> a == meta_page(b) || in_runs(b, lo, a) || in_runs(
            meta_page(b),
            hi,
            a,
        )
}

/// `after` is `before` with a run of order `k` cut at `p`, in the block of `p`, apart from every run
/// that block had.
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

/// The block at `h` of the block at `b` is free, of order `k` or more, and no free block of order `k`
/// or more in any block has a smaller order.
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

/// The source went from `before` to `after` by reserving the new run span at `b` and backing its
/// metadata page.
pub open spec fn took_span(before: SourceView, after: SourceView, b: int) -> bool {
    &&& !before.spans.contains_key(b)
    &&& after == before.reserved(b, SPAN_BLOCKS as nat).backed_run(b, meta_page(b), 1)
}

/// The order a best-fit search has found so far is at most `ord`.
spec fn below(best: Option<(usize, bool, usize)>, ord: nat) -> bool {
    match best {
        None => false,
        Some((_, _, o)) => o <= ord,
    }
}

/// A run span's node, at the start of its metadata page: the base of the next held span, or 0 at
/// the end of the list, and the block buddies of its first and second blocks.
#[repr(C)]
pub struct Node {
    next: usize,
    lo: BlockBuddy,
    hi: BlockBuddy,
}

/// The page `h` of the block-aligned block at `base` is a page whose block is `base` and whose page
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

/// A page-aligned address is page `page_of(p)` of the block-aligned block at `span_of(p)`: the
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

/// Runs of `n` pages at page `h` and of `o` pages at page `q` of the block at `b`, apart as pages,
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

/// A run of `n` pages at page `h` of the block at `x` lies in that block, and starts past its first
/// page when `h` is not 0.
proof fn lemma_in_block(x: int, h: int, n: int)
    requires
        0 <= h,
        0 <= n,
        h + n <= BLOCK_PAGES,
    ensures
        x <= x + h * PAGE_BYTES as int,
        x + h * PAGE_BYTES as int + n * PAGE_BYTES as int <= x + BLOCK_BYTES as int,
        h > 0 ==> x + PAGE_BYTES as int <= x + h * PAGE_BYTES as int,
        forall|a: int| #[trigger]
            run_pages(x + h * PAGE_BYTES as int, n as nat).contains(a) ==> x <= a < x + BLOCK_BYTES as int,
        h > 0 ==> !run_pages(x + h * PAGE_BYTES as int, n as nat).contains(x),
{
    let pb = PAGE_BYTES as int;
    assert(h * pb + n * pb <= BLOCK_PAGES as int * pb) by (nonlinear_arith)
        requires
            h + n <= BLOCK_PAGES as int,
            pb > 0,
    ;
    assert(0 <= h * pb) by (nonlinear_arith)
        requires
            0 <= h,
            pb > 0,
    ;
    if h > 0 {
        assert(pb <= h * pb) by (nonlinear_arith)
            requires
                h >= 1,
                pb > 0,
        ;
    }
}

/// A page of a run `u` holds in the block at `x`, `u` being runs of the buddy `bb`, lies in that
/// block, and outside the run cut at `bb`'s free block `h` with an order of `k` or less.
proof fn lemma_run_page(x: int, bb: BlockBuddy, u: Map<int, nat>, a: int, h: int, k: nat)
    requires
        bb.wf(),
        forall|q: int| #[trigger] u.contains_key(q) ==> bb.used().contains_key(q) && u[q] == bb.used()[q],
        in_runs(x, u, a),
    ensures
        x <= a < x + BLOCK_BYTES as int,
        bb.blocks().contains_key(h) && bb.blocks()[h].free && k <= bb.blocks()[h].order ==> !run_pages(
            x + h * PAGE_BYTES as int,
            pages(k) as nat,
        ).contains(a),
{
    let q = choose|q: int| #[trigger] u.contains_key(q) && run_pages(x + q * PAGE_BYTES as int, pages(u[q]) as nat).contains(a);
    bb.lemma_view();
    assert(bb.blocks().contains_key(q) && !bb.blocks()[q].free && bb.blocks()[q].order == u[q]);
    assert(placed(q, bb.blocks()[q]));
    lemma_pages_pos(u[q]);
    lemma_in_block(x, q, pages(u[q]));
    if bb.blocks().contains_key(h) && bb.blocks()[h].free && k <= bb.blocks()[h].order {
        assert(q != h);
        lemma_pages(k, bb.blocks()[h].order);
        lemma_pages_pos(k);
        lemma_runs_apart(x, h, pages(k), q, pages(u[q]));
    }
}

/// The run of one page at a page-aligned `s` holds only `s`.
proof fn lemma_one_page(s: int)
    requires
        s % PAGE_BYTES as int == 0,
    ensures
        run_pages(s, 1) == Set::<int>::empty().insert(s),
{
    let pb = PAGE_BYTES as int;
    assert forall|a: int| #[trigger] run_pages(s, 1).contains(a) implies a == s by {
        lemma_fundamental_div_mod(a, pb);
        lemma_fundamental_div_mod(s, pb);
        let qa = a / pb;
        let qs = s / pb;
        assert(qa == qs) by (nonlinear_arith)
            requires
                a == pb * qa,
                s == pb * qs,
                s <= a < s + pb,
                pb > 0,
        ;
    }
    assert(run_pages(s, 1).contains(s));
    assert(run_pages(s, 1) =~= Set::<int>::empty().insert(s));
}

/// The metadata page of a block-aligned span is a page and the base of a block, aligned for a node,
/// and a node fits in it with room to spare.
proof fn lemma_meta(b: int)
    requires
        b % BLOCK_BYTES as int == 0,
    ensures
        meta_page(b) % BLOCK_BYTES as int == 0,
        meta_page(b) % PAGE_BYTES as int == 0,
        meta_page(b) % align_of::<Node>() as int == 0,
        0 < size_of::<Node>() < PAGE_BYTES,
{
    let bb = BLOCK_BYTES as int;
    let pb = PAGE_BYTES as int;
    let m = meta_page(b);
    lemma_node_layout();
    lemma_mod_add_multiples_vanish(b, bb);
    lemma_mod_mod(m, pb, BLOCK_PAGES as int);
    let al = align_of::<Node>() as int;
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

/// A block buddy's runs are `used_of` its blocks.
proof fn lemma_used_of(bb: BlockBuddy)
    ensures
        used_of(bb.blocks()) == bb.used(),
{
    assert(used_of(bb.blocks()).dom() =~= bb.used().dom());
    assert(used_of(bb.blocks()) =~= bb.used());
}

/// The pointer to the node of the span at `b`, with the provenance of `hp`.
fn node_at(hp: *mut u8, b: usize) -> (r: *mut Node)
    requires
        b + BLOCK_BYTES <= usize::MAX,
    ensures
        r == node_ptr(b as int, hp@.provenance),
{
    hp.with_addr(b + BLOCK_BYTES) as *mut Node
}

/// The page buddy over a span source.
pub struct PageBuddy<S: SpanSource> {
    source: S,
    /// The first held span, while one is held; it carries the source's provenance.
    head: Option<*mut u8>,
    /// The idle spans kept rather than given back.
    spares: usize,
    /// The held spans with no run allocated.
    idle: usize,
    /// The bases of the held spans, in the order their nodes link them.
    chain: Ghost<Seq<int>>,
    /// The metadata pages of the held spans.
    metas: Ghost<Set<int>>,
    /// The permission to each held span's node, by base.
    nodes: Tracked<Map<int, PointsTo<Node>>>,
    /// The permission to the rest of each held span's metadata page, after its node, by base.
    rests: Tracked<Map<int, PointsToRaw>>,
}

impl<S: SpanSource> PageBuddy<S> {
    /// The node of the held span at `b`.
    spec fn node(&self, b: int) -> Node {
        self.nodes@[b].value()
    }

    /// The block buddy of the held span at `b`: its second block's when `hi`, its first's otherwise.
    spec fn half(&self, b: int, hi: bool) -> BlockBuddy {
        if hi {
            self.node(b).hi
        } else {
            self.node(b).lo
        }
    }

    /// The blocks of the block at `c`: its span's first block's, or its second's.
    spec fn blocks_of(&self, c: int) -> Map<int, Block> {
        if self.nodes@.contains_key(c) {
            self.node(c).lo.blocks()
        } else {
            self.node(c - BLOCK_BYTES as int).hi.blocks()
        }
    }

    /// The runs allocated to callers in the block at `c`: every run of a first block, and every run
    /// of a second block but its metadata page.
    spec fn used_in(&self, c: int) -> Map<int, nat> {
        if self.nodes@.contains_key(c) {
            self.node(c).lo.used()
        } else {
            self.node(c - BLOCK_BYTES as int).hi.used().remove(0)
        }
    }

    /// The blocks of the held spans, by base, with the blocks of each.
    pub closed spec fn spans(&self) -> Map<int, Map<int, Block>> {
        Map::new(self.nodes@.dom().union(self.metas@), |c: int| self.blocks_of(c))
    }

    /// The runs allocated to callers in each block of a held span, by head, with their orders.
    pub closed spec fn used(&self) -> Map<int, Map<int, nat>> {
        Map::new(self.nodes@.dom().union(self.metas@), |c: int| self.used_in(c))
    }

    /// The metadata pages of the held spans.
    pub closed spec fn metas(&self) -> Set<int> {
        self.metas@
    }

    /// The source's view.
    pub closed spec fn source(&self) -> SourceView {
        self.source@
    }

    /// The idle spans the page buddy keeps rather than gives back.
    pub closed spec fn spares(&self) -> nat {
        self.spares as nat
    }

    /// The base of the span whose block is at `c`.
    pub open spec fn span_base(&self, c: int) -> int {
        base_in(self.metas(), c)
    }

    /// The held spans with no run allocated, by metadata page.
    pub open spec fn idle_spans(&self) -> Set<int> {
        idle_of(self.used(), self.metas())
    }

    /// Some block of a held span has a free block of order `k` or more.
    pub open spec fn fits(&self, k: nat) -> bool {
        exists|b: int, h: int|
            #![trigger self.spans()[b].contains_key(h)]
            self.spans().contains_key(b) && self.spans()[b].contains_key(h) && self.spans()[b][h].free
                && self.spans()[b][h].order >= k
    }

    /// `p` is the head of a run allocated to a caller.
    pub open spec fn holds(&self, p: int) -> bool {
        &&& p % PAGE_BYTES as int == 0
        &&& self.used().contains_key(span_of(p))
        &&& self.used()[span_of(p)].contains_key(page_of(p))
    }

    /// The node of the held span at `b` is at its metadata page and holds its two block buddies,
    /// the second's first run the metadata page, and the rest of the metadata page is held beside it.
    spec fn node_wf(&self, b: int) -> bool {
        let src = self.source@;
        &&& self.nodes@[b].ptr() == node_ptr(b, src.provenance)
        &&& self.nodes@[b].is_init()
        &&& self.node(b).lo.wf()
        &&& self.node(b).hi.wf()
        &&& self.node(b).hi.used().contains_key(0)
        &&& self.node(b).hi.used()[0] == 0
        &&& held(src, b, self.node(b).lo.used(), self.node(b).hi.used().remove(0))
        &&& self.rests@.contains_key(b)
        &&& self.rests@[b].is_range(meta_page(b) + size_of::<Node>(), PAGE_BYTES - size_of::<Node>())
        &&& self.rests@[b].provenance() == src.provenance
    }

    /// The node at position `i` of the chain links the span after it, or ends the list.
    spec fn linked(&self, i: int) -> bool {
        self.node(self.chain@[i]).next as int == if i + 1 < self.chain@.len() {
            self.chain@[i + 1]
        } else {
            0
        }
    }

    /// The list from `head` links exactly the held spans, each node well formed, the metadata pages
    /// are the held spans' and the count of idle spans is right.
    pub closed spec fn wf(&self) -> bool {
        &&& self.source@.wf()
        &&& self.idle <= self.spares
        &&& self.idle as int == self.idle_spans().len()
        &&& self.chain@.no_duplicates()
        &&& forall|b: int|
            #![trigger self.nodes@.contains_key(b)]
            #![trigger self.chain@.contains(b)]
            self.nodes@.contains_key(b) <==> self.chain@.contains(b)
        &&& forall|b: int| #[trigger] self.nodes@.contains_key(b) ==> self.metas@.contains(meta_page(b))
        &&& forall|m: int| #[trigger] self.metas@.contains(m) ==> self.nodes@.contains_key(m - BLOCK_BYTES as int)
        &&& forall|b: int| #[trigger] self.nodes@.contains_key(b) ==> self.node_wf(b)
        &&& forall|i: int| 0 <= i < self.chain@.len() ==> #[trigger] self.linked(i)
        &&& match self.head {
            None => self.chain@.len() == 0,
            Some(h) => {
                &&& self.chain@.len() > 0
                &&& h@.addr as int == self.chain@[0]
                &&& h@.provenance == self.source@.provenance
            },
        }
    }

    /// A held span's node is well formed, the span is in the chain, and the span fits in the
    /// address space, block-aligned above address 0.
    proof fn lemma_base(&self, b: int)
        requires
            self.wf(),
            self.nodes@.contains_key(b),
        ensures
            self.node_wf(b),
            self.chain@.contains(b),
            self.chain@.len() > 0,
            self.head is Some,
            self.metas@.contains(meta_page(b)),
            b > 0,
            b % BLOCK_BYTES as int == 0,
            b + span_bytes(SPAN_BLOCKS as nat) <= usize::MAX as int + 1,
    {
        assert(self.node_wf(b));
        assert(self.source@.released_span(b).fits(b, self.source@.spans[b].blocks));
    }

    /// Two held spans are apart.
    proof fn lemma_apart(&self, b: int, c: int)
        requires
            self.wf(),
            self.nodes@.contains_key(b),
            self.nodes@.contains_key(c),
            b != c,
        ensures
            b + span_bytes(SPAN_BLOCKS as nat) <= c || c + span_bytes(SPAN_BLOCKS as nat) <= b,
    {
        self.lemma_base(b);
        self.lemma_base(c);
        let src = self.source@;
        assert(src.released_span(b).fits(b, src.spans[b].blocks));
        assert(src.released_span(b).spans.contains_key(c));
        assert(src.released_span(b).apart(b, src.spans[b].blocks, c));
    }

    /// A metadata page is the second block of a held span and no held span's base.
    proof fn lemma_meta_block(&self, m: int)
        requires
            self.wf(),
            self.metas@.contains(m),
        ensures
            self.nodes@.contains_key(m - BLOCK_BYTES as int),
            !self.nodes@.contains_key(m),
            meta_page(m - BLOCK_BYTES as int) == m,
    {
        if self.nodes@.contains_key(m) {
            self.lemma_apart(m - BLOCK_BYTES as int, m);
        }
    }

    /// The block at `c` of a held span: the base of its span, which block of it `c` is, its blocks
    /// and its runs.
    proof fn lemma_block(&self, c: int)
        requires
            self.wf(),
            self.spans().contains_key(c),
        ensures
            self.used().contains_key(c),
            self.nodes@.contains_key(self.span_base(c)),
            c == self.span_base(c) || c == meta_page(self.span_base(c)),
            self.metas@.contains(c) == (c == meta_page(self.span_base(c))),
            self.nodes@.contains_key(c) == (c == self.span_base(c)),
            self.spans()[c] == if c == self.span_base(c) {
                self.node(c).lo.blocks()
            } else {
                self.node(self.span_base(c)).hi.blocks()
            },
            self.used()[c] == if c == self.span_base(c) {
                self.node(c).lo.used()
            } else {
                self.node(self.span_base(c)).hi.used().remove(0)
            },
    {
        if self.metas@.contains(c) {
            self.lemma_meta_block(c);
        } else {
            assert(self.nodes@.contains_key(c));
        }
    }

    /// Both blocks of the held span at `b` are in the view, as its node's buddies.
    proof fn lemma_blocks_of(&self, b: int)
        requires
            self.wf(),
            self.nodes@.contains_key(b),
        ensures
            self.spans().contains_key(b),
            self.spans().contains_key(meta_page(b)),
            self.used().contains_key(b),
            self.used().contains_key(meta_page(b)),
            self.span_base(b) == b,
            self.span_base(meta_page(b)) == b,
            !self.metas@.contains(b),
            self.spans()[b] == self.node(b).lo.blocks(),
            self.spans()[meta_page(b)] == self.node(b).hi.blocks(),
            self.used()[b] == self.node(b).lo.used(),
            self.used()[meta_page(b)] == self.node(b).hi.used().remove(0),
    {
        self.lemma_base(b);
        if self.metas@.contains(b) {
            self.lemma_meta_block(b);
        }
        self.lemma_meta_block(meta_page(b));
    }

    /// A page buddy that differs from a well-formed one only in its source's value, the view the
    /// same, is well formed.
    proof fn lemma_same_view(&self, other: &Self)
        requires
            other.wf(),
            self.source@ == other.source@,
            self.head == other.head,
            self.spares == other.spares,
            self.idle == other.idle,
            self.chain == other.chain,
            self.metas == other.metas,
            self.nodes == other.nodes,
            self.rests == other.rests,
        ensures
            self.wf(),
            self.spans() == other.spans(),
            self.used() == other.used(),
    {
        assert(self.spans() =~= other.spans());
        assert(self.used() =~= other.used());
        assert(self.idle_spans() == other.idle_spans());
        assert forall|b: int| #[trigger] self.nodes@.contains_key(b) implies self.node_wf(b) by {
            assert(other.node_wf(b));
        }
        assert forall|i: int| 0 <= i < self.chain@.len() implies #[trigger] self.linked(i) by {
            assert(other.linked(i));
        }
    }

    /// The source refused in a call that changed nothing else: the page buddy is well formed with
    /// the same view.
    proof fn lemma_refused(&self, other: &Self)
        requires
            other.wf(),
            self.source@ == other.source@.refused(),
            self.head == other.head,
            self.spares == other.spares,
            self.idle == other.idle,
            self.chain == other.chain,
            self.metas == other.metas,
            self.nodes == other.nodes,
            self.rests == other.rests,
        ensures
            self.wf(),
            self.spans() == other.spans(),
            self.used() == other.used(),
    {
        lemma_refused_wf(other.source@);
        assert(self.spans() =~= other.spans());
        assert(self.used() =~= other.used());
        assert(self.idle_spans() == other.idle_spans());
        assert forall|b: int| #[trigger] self.nodes@.contains_key(b) implies self.node_wf(b) by {
            assert(other.node_wf(b));
        }
        assert forall|i: int| 0 <= i < self.chain@.len() implies #[trigger] self.linked(i) by {
            assert(other.linked(i));
        }
    }

    /// The span at position `i` of the chain is held, its node well formed and linked.
    proof fn lemma_at(&self, i: int)
        requires
            self.wf(),
            0 <= i < self.chain@.len(),
        ensures
            self.nodes@.contains_key(self.chain@[i]),
            self.node_wf(self.chain@[i]),
            self.linked(i),
            self.chain@[i] > 0,
            self.chain@[i] % BLOCK_BYTES as int == 0,
            self.chain@[i] + span_bytes(SPAN_BLOCKS as nat) <= usize::MAX as int + 1,
    {
        assert(self.chain@.contains(self.chain@[i]));
        self.lemma_base(self.chain@[i]);
    }

    /// The invariant on the view: every held span is a reserved span of SPAN_BLOCKS blocks whose
    /// metadata page, the first page of its second block, is backed and is that block's allocated
    /// block of order 0 at page 0, and whose other backed pages lie in its blocks' runs; each block
    /// partitioned and coalesced, a first block with no run the initial block; and no more idle spans
    /// are held than the spares.
    pub proof fn lemma_view(&self)
        requires
            self.wf(),
        ensures
            self.source().wf(),
            self.idle_spans().len() <= self.spares(),
            self.used().dom() == self.spans().dom(),
            forall|m: int| #[trigger]
                self.metas().contains(m) ==> {
                    &&& self.spans().contains_key(m)
                    &&& self.spans().contains_key(m - BLOCK_BYTES as int)
                    &&& !self.metas().contains(m - BLOCK_BYTES as int)
                },
            forall|c: int|
                #[trigger] self.spans().contains_key(c) ==> {
                    &&& partitioned(self.spans()[c])
                    &&& coalesced(self.spans()[c])
                    &&& c > 0
                    &&& c % BLOCK_BYTES as int == 0
                    &&& if self.metas().contains(c) {
                        &&& self.spans()[c].contains_key(0)
                        &&& self.spans()[c][0] == (Block { order: 0, free: false })
                        &&& self.used()[c] == used_of(self.spans()[c]).remove(0)
                        &&& held(self.source(), c - BLOCK_BYTES as int, self.used()[c - BLOCK_BYTES as int], self.used()[c])
                    } else {
                        &&& self.metas().contains(meta_page(c))
                        &&& self.used()[c] == used_of(self.spans()[c])
                        &&& self.used()[c].dom() == Set::<int>::empty() ==> self.spans()[c] == initial()
                        &&& held(self.source(), c, self.used()[c], self.used()[meta_page(c)])
                    }
                },
    {
        assert(self.used().dom() =~= self.spans().dom());
        assert forall|m: int| #[trigger] self.metas().contains(m) implies {
            &&& self.spans().contains_key(m)
            &&& self.spans().contains_key(m - BLOCK_BYTES as int)
            &&& !self.metas().contains(m - BLOCK_BYTES as int)
        } by {
            self.lemma_meta_block(m);
            self.lemma_blocks_of(m - BLOCK_BYTES as int);
        }
        assert forall|c: int| #[trigger] self.spans().contains_key(c) implies {
            &&& partitioned(self.spans()[c])
            &&& coalesced(self.spans()[c])
            &&& c > 0
            &&& c % BLOCK_BYTES as int == 0
            &&& if self.metas().contains(c) {
                &&& self.spans()[c].contains_key(0)
                &&& self.spans()[c][0] == (Block { order: 0, free: false })
                &&& self.used()[c] == used_of(self.spans()[c]).remove(0)
                &&& held(self.source(), c - BLOCK_BYTES as int, self.used()[c - BLOCK_BYTES as int], self.used()[c])
            } else {
                &&& self.metas().contains(meta_page(c))
                &&& self.used()[c] == used_of(self.spans()[c])
                &&& self.used()[c].dom() == Set::<int>::empty() ==> self.spans()[c] == initial()
                &&& held(self.source(), c, self.used()[c], self.used()[meta_page(c)])
            }
        } by {
            self.lemma_block(c);
            let b = self.span_base(c);
            self.lemma_blocks_of(b);
            lemma_meta(b);
            let bb = if c == b {
                self.node(b).lo
            } else {
                self.node(b).hi
            };
            assert(self.spans()[c] == bb.blocks());
            bb.lemma_view();
            lemma_used_of(bb);
            if c == b {
                if self.used()[c].dom() == Set::<int>::empty() {
                    bb.lemma_idle();
                }
            } else {
                assert(bb.used().contains_key(0));
                assert(bb.blocks().contains_key(0));
            }
        }
    }

    /// A held span's first block with no run allocated is one free block of order BLOCK_ORDER, so a
    /// run of any order fits while it is held.
    pub proof fn lemma_idle_fits(&self, b: int, k: nat)
        requires
            self.wf(),
            self.spans().contains_key(b),
            !self.metas().contains(b),
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
            r.spans() == Map::<int, Map<int, Block>>::empty(),
            r.used() == Map::<int, Map<int, nat>>::empty(),
            r.metas() == Set::<int>::empty(),
    {
        let r = PageBuddy {
            source,
            head: None,
            spares,
            idle: 0,
            chain: Ghost(Seq::empty()),
            metas: Ghost(Set::empty()),
            nodes: Tracked(Map::tracked_empty()),
            rests: Tracked(Map::tracked_empty()),
        };
        assert(r.spans() =~= Map::<int, Map<int, Block>>::empty());
        assert(r.used() =~= Map::<int, Map<int, nat>>::empty());
        assert(r.idle_spans() =~= Set::<int>::empty());
        r
    }

    /// The held span and the block of it with a free block of the smallest order at or above `k`
    /// across every held span, with that order; or none when no held span has a free block of order
    /// `k` or more.
    fn best_span(&self, k: usize) -> (r: Option<(usize, bool, usize)>)
        requires
            self.wf(),
            k <= BLOCK_ORDER,
        ensures
            match r {
                None => !self.fits(k as nat),
                Some((b, hi, o)) => {
                    &&& self.nodes@.contains_key(b as int)
                    &&& k <= o <= BLOCK_ORDER
                    &&& self.half(b as int, hi).fits(k as nat)
                    &&& exists|h: int|
                        #[trigger] self.half(b as int, hi).blocks().contains_key(h) && self.half(b as int, hi).blocks()[h] == (Block { order: o as nat, free: true })
                    &&& forall|c: int, q: int|
                        #![trigger self.spans()[c].contains_key(q)]
                        self.spans().contains_key(c) && self.spans()[c].contains_key(q)
                            && self.spans()[c][q].free && self.spans()[c][q].order >= k
                            ==> self.spans()[c][q].order >= o
                },
            },
    {
        let hp = match self.head {
            None => {
                proof {
                    if self.fits(k as nat) {
                        let (c, h) = choose|c: int, h: int|
                            #![trigger self.spans()[c].contains_key(h)]
                            self.spans().contains_key(c) && self.spans()[c].contains_key(h)
                                && self.spans()[c][h].free && self.spans()[c][h].order >= k;
                        self.lemma_block(c);
                        self.lemma_base(self.span_base(c));
                    }
                }
                return None;
            },
            Some(hp) => hp,
        };
        let mut best: Option<(usize, bool, usize)> = None;
        let mut cur: usize = hp.addr();
        let ghost mut j: int = 0;
        while cur != 0
            invariant
                self.wf(),
                k <= BLOCK_ORDER,
                self.head == Some(hp),
                0 <= j <= self.chain@.len(),
                cur as int == if j < self.chain@.len() { self.chain@[j] } else { 0 },
                match best {
                    None => true,
                    Some((c, hi, o)) => {
                        &&& self.nodes@.contains_key(c as int)
                        &&& k <= o <= BLOCK_ORDER
                        &&& exists|h: int|
                            #[trigger] self.half(c as int, hi).blocks().contains_key(h) && self.half(c as int, hi).blocks()[h] == (Block { order: o as nat, free: true })
                    },
                },
                forall|i: int, q: int|
                    #![trigger self.node(self.chain@[i]).lo.blocks().contains_key(q)]
                    0 <= i < j && self.node(self.chain@[i]).lo.blocks().contains_key(q)
                        && self.node(self.chain@[i]).lo.blocks()[q].free
                        && self.node(self.chain@[i]).lo.blocks()[q].order >= k ==> below(
                        best,
                        self.node(self.chain@[i]).lo.blocks()[q].order,
                    ),
                forall|i: int, q: int|
                    #![trigger self.node(self.chain@[i]).hi.blocks().contains_key(q)]
                    0 <= i < j && self.node(self.chain@[i]).hi.blocks().contains_key(q)
                        && self.node(self.chain@[i]).hi.blocks()[q].free
                        && self.node(self.chain@[i]).hi.blocks()[q].order >= k ==> below(
                        best,
                        self.node(self.chain@[i]).hi.blocks()[q].order,
                    ),
            decreases self.chain@.len() - j,
        {
            proof {
                self.lemma_at(j);
            }
            let ptr = node_at(hp, cur);
            let tracked perm = self.nodes.borrow().tracked_borrow(cur as int);
            let node = ptr_ref(ptr, Tracked(perm));
            let ghost best0 = best;
            proof {
                assert(*node == self.node(cur as int));
                assert(cur as int == self.chain@[j]);
            }
            let lo_o = node.lo.fit_order(k);
            if let Some(o) = lo_o {
                let better = match best {
                    None => true,
                    Some((_, _, bo)) => o < bo,
                };
                if better {
                    best = Some((cur, false, o));
                }
            }
            let ghost best1 = best;
            let hi_o = node.hi.fit_order(k);
            if let Some(o) = hi_o {
                let better = match best {
                    None => true,
                    Some((_, _, bo)) => o < bo,
                };
                if better {
                    best = Some((cur, true, o));
                }
            }
            proof {
                assert forall|x: nat| below(best0, x) implies below(best, x) by {}
                if let Some((c, hi, o)) = best {
                    if c == cur && best != best0 {
                        let bb = if hi { node.hi } else { node.lo };
                        let h = choose|h: int| #[trigger]
                            bb.blocks().contains_key(h) && bb.blocks()[h] == (Block { order: o as nat, free: true });
                        assert(self.half(c as int, hi).blocks().contains_key(h));
                    }
                }
                if let Some(o) = lo_o {
                    assert forall|x: nat| o <= x implies below(best, x) by {
                        assert(below(best1, x));
                    }
                }
                if let Some(o) = hi_o {
                    assert forall|x: nat| o <= x implies below(best, x) by {}
                }
                assert forall|i: int, q: int|
                    #![trigger self.node(self.chain@[i]).lo.blocks().contains_key(q)]
                    0 <= i < j + 1 && self.node(self.chain@[i]).lo.blocks().contains_key(q)
                        && self.node(self.chain@[i]).lo.blocks()[q].free
                        && self.node(self.chain@[i]).lo.blocks()[q].order >= k implies below(
                        best,
                        self.node(self.chain@[i]).lo.blocks()[q].order,
                    ) by {
                    if i == j {
                        assert(node.lo.blocks().contains_key(q));
                        assert(node.lo.fits(k as nat));
                    }
                }
                assert forall|i: int, q: int|
                    #![trigger self.node(self.chain@[i]).hi.blocks().contains_key(q)]
                    0 <= i < j + 1 && self.node(self.chain@[i]).hi.blocks().contains_key(q)
                        && self.node(self.chain@[i]).hi.blocks()[q].free
                        && self.node(self.chain@[i]).hi.blocks()[q].order >= k implies below(
                        best,
                        self.node(self.chain@[i]).hi.blocks()[q].order,
                    ) by {
                    if i == j {
                        assert(node.hi.blocks().contains_key(q));
                        assert(node.hi.fits(k as nat));
                    }
                }
            }
            cur = node.next;
            proof {
                j = j + 1;
                if j < self.chain@.len() {
                    self.lemma_at(j);
                }
            }
        }
        proof {
            if j < self.chain@.len() {
                self.lemma_at(j);
            }
            assert(j == self.chain@.len());
            assert forall|c: int, q: int|
                #![trigger self.spans()[c].contains_key(q)]
                self.spans().contains_key(c) && self.spans()[c].contains_key(q)
                    && self.spans()[c][q].free && self.spans()[c][q].order >= k implies below(
                best,
                self.spans()[c][q].order,
            ) by {
                self.lemma_block(c);
                let b = self.span_base(c);
                self.lemma_base(b);
                let i = choose|i: int| 0 <= i < self.chain@.len() && self.chain@[i] == b;
                if c == b {
                    assert(self.node(self.chain@[i]).lo.blocks().contains_key(q));
                } else {
                    assert(self.node(self.chain@[i]).hi.blocks().contains_key(q));
                }
            }
            match best {
                None => {
                    if self.fits(k as nat) {
                        let (c, h) = choose|c: int, h: int|
                            #![trigger self.spans()[c].contains_key(h)]
                            self.spans().contains_key(c) && self.spans()[c].contains_key(h)
                                && self.spans()[c][h].free && self.spans()[c][h].order >= k;
                        assert(below(best, self.spans()[c][h].order));
                    }
                },
                Some((c, hi, o)) => {
                    let bb = if hi {
                        self.node(c as int).hi
                    } else {
                        self.node(c as int).lo
                    };
                    let h = choose|h: int| #[trigger]
                        bb.blocks().contains_key(h) && bb.blocks()[h] == (Block { order: o as nat, free: true });
                    assert(bb.blocks().contains_key(h));
                },
            }
        }
        best
    }

    /// The position of the held span whose block is at `c` in the list: the base of the span before
    /// it, or 0 when it is the first, and its base.
    fn find(&self, c: usize) -> (r: (usize, usize))
        requires
            self.wf(),
            self.spans().contains_key(c as int),
        ensures
            r.1 as int == self.span_base(c as int),
            exists|j: int|
                0 <= j < self.chain@.len() && #[trigger] self.chain@[j] == r.1 as int && r.0 as int == if j == 0 {
                    0
                } else {
                    self.chain@[j - 1]
                },
    {
        let ghost b = self.span_base(c as int);
        proof {
            self.lemma_block(c as int);
            self.lemma_base(b);
        }
        let hp = self.head.unwrap();
        let ghost jb = choose|i: int| 0 <= i < self.chain@.len() && self.chain@[i] == b;
        let mut prev: usize = 0;
        let mut cur: usize = hp.addr();
        let ghost mut j: int = 0;
        proof {
            self.lemma_at(0);
        }
        while cur != c && cur + BLOCK_BYTES != c
            invariant
                self.wf(),
                self.spans().contains_key(c as int),
                b == self.span_base(c as int),
                self.head == Some(hp),
                0 <= j <= jb < self.chain@.len(),
                self.chain@[jb] == b,
                cur as int == self.chain@[j],
                cur + BLOCK_BYTES <= usize::MAX,
                prev as int == if j == 0 { 0 } else { self.chain@[j - 1] },
            decreases jb - j,
        {
            proof {
                self.lemma_at(j);
                self.lemma_block(c as int);
                assert(j != jb);
            }
            let ptr = node_at(hp, cur);
            let tracked perm = self.nodes.borrow().tracked_borrow(cur as int);
            let node = ptr_ref(ptr, Tracked(perm));
            prev = cur;
            cur = node.next;
            proof {
                j = j + 1;
                self.lemma_at(j);
            }
        }
        proof {
            self.lemma_block(c as int);
            if cur as int != b {
                self.lemma_at(j);
                self.lemma_at(jb);
                self.lemma_blocks_of(cur as int);
                assert(self.chain@[j] != self.chain@[jb]);
            }
        }
        (prev, cur)
    }

    /// Cuts a run of order `k` in the first block of the held span at `b`, or in its second when
    /// `hi`, from its free block of the smallest order at or above `k`.
    fn alloc_in(&mut self, b: usize, hi: bool, k: usize) -> (p: usize)
        requires
            old(self).wf(),
            k <= BLOCK_ORDER,
            old(self).nodes@.contains_key(b as int),
            old(self).half(b as int, hi).fits(k as nat),
        ensures
            final(self).wf(),
            final(self).spares() == old(self).spares(),
            final(self).spans().dom() == old(self).spans().dom(),
            final(self).metas() == old(self).metas(),
            final(self).source() == old(self).source(),
            span_of(p as int) == if hi {
                meta_page(b as int)
            } else {
                b as int
            },
            final(self).span_base(span_of(p as int)) == b,
            cut(old(self).used(), final(self).used(), p as int, k as nat),
            final(self).source().unbacked(b as int, p as int, pages(k as nat) as nat),
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
        let ghost bi = b as int;
        let ghost mi = meta_page(bi);
        proof {
            self.lemma_base(bi);
            self.lemma_blocks_of(bi);
            lemma_meta(bi);
        }
        let hp = self.head.unwrap();
        let ghost n0 = self.node(bi);
        let ptr = node_at(hp, b);
        let tracked mut perm = self.nodes.borrow_mut().tracked_remove(bi);
        let mut node = ptr_mut_read(ptr, Tracked(&mut perm));
        let was_idle = node.lo.is_idle() && node.hi.idle_from(1);
        let h = if hi {
            node.hi.alloc(k).unwrap()
        } else {
            node.lo.alloc(k).unwrap()
        };
        ptr_mut_write(ptr, Tracked(&mut perm), node);
        proof {
            self.nodes.borrow_mut().tracked_insert(bi, perm);
            if was_idle {
                assert(old_idle.contains(mi)) by {
                    assert(n0.lo.used().dom() == Set::<int>::empty());
                    assert(old(self).used()[mi] == n0.hi.used().remove(0));
                    assert(n0.hi.used().remove(0).dom() =~= Set::<int>::empty()) by {
                        assert forall|q: int| !n0.hi.used().remove(0).dom().contains(q) by {
                            if q != 0 && n0.hi.used().dom().contains(q) {
                                n0.hi.lemma_view();
                                assert(placed(q, n0.hi.blocks()[q]));
                            }
                        }
                    }
                }
            }
        }
        if was_idle {
            self.idle = self.idle - 1;
        }
        let ghost x = if hi { mi } else { bi };
        let ghost bb0 = if hi { n0.hi } else { n0.lo };
        let ghost u = old_used[x];
        proof {
            lemma_pages_pos(k as nat);
            bb0.lemma_view();
            assert(bb0.blocks().contains_key(h as int));
            assert(placed(h as int, bb0.blocks()[h as int]));
            lemma_pages(k as nat, bb0.blocks()[h as int].order);
            if hi {
                assert(n0.hi.used().contains_key(0));
                assert(h != 0);
                assert(node.hi.used().remove(0) =~= n0.hi.used().remove(0).insert(h as int, k as nat));
            }
            assert(u == if hi { n0.hi.used().remove(0) } else { n0.lo.used() });
            assert(self.nodes@.dom() =~= old(self).nodes@.dom());
            assert(self.spans() =~= old_spans.insert(x, if hi { node.hi.blocks() } else { node.lo.blocks() })) by {
                assert forall|c: int| #[trigger] self.spans().contains_key(c) && c != x implies self.spans()[c] == old_spans[c] by {
                    if c != bi && !self.nodes@.contains_key(c) && c - BLOCK_BYTES as int == bi {
                        assert(c == mi && !hi);
                        assert(node.hi == n0.hi);
                    }
                }
            }
            assert(self.used() =~= old_used.insert(x, u.insert(h as int, k as nat))) by {
                assert forall|c: int| #[trigger] self.used().contains_key(c) && c != x implies self.used()[c] == old_used[c] by {
                    if c != bi && !self.nodes@.contains_key(c) && c - BLOCK_BYTES as int == bi {
                        assert(c == mi && !hi);
                        assert(node.hi == n0.hi);
                    }
                }
            }
            // The span was idle exactly when both its blocks held no run; it holds one now.
            assert(old(self).used()[mi] == n0.hi.used().remove(0));
            if was_idle {
                assert(n0.lo.used().dom() == Set::<int>::empty());
                assert(n0.hi.used().remove(0).dom() =~= Set::<int>::empty()) by {
                    assert forall|q: int| !n0.hi.used().remove(0).dom().contains(q) by {
                        if q != 0 && n0.hi.used().dom().contains(q) {
                            n0.hi.lemma_view();
                            assert(placed(q, n0.hi.blocks()[q]));
                        }
                    }
                }
                assert(old_idle.contains(mi));
            } else {
                if n0.lo.used().dom() == Set::<int>::empty() {
                    let q = choose|q: int| 1 <= q && #[trigger] n0.hi.used().dom().contains(q);
                    assert(n0.hi.used().remove(0).dom().contains(q));
                }
                assert(!old_idle.contains(mi));
            }
            assert(self.used()[x].contains_key(h as int));
            assert forall|m: int| #[trigger] self.metas@.contains(m) && m != mi implies (self.used()[m] == old_used[m]
                && self.used()[m - BLOCK_BYTES as int] == old_used[m - BLOCK_BYTES as int]) by {
                old(self).lemma_meta_block(m);
                assert(m != bi);
                assert(m - BLOCK_BYTES as int != mi);
            }
            if was_idle {
                assert(self.idle_spans() =~= old_idle.remove(mi));
            } else {
                assert(self.idle_spans() =~= old_idle);
            }
            assert forall|q: int| #[trigger] u.contains_key(q) implies h + pages(k as nat) <= q || q
                + pages(u[q]) <= h by {
                assert(bb0.blocks().contains_key(q) && !bb0.blocks()[q].free);
                assert(q != h);
            }
            assert(self.used() == old_used.insert(x, old_used[x].insert(h as int, k as nat)));
            lemma_address(x, h as int);
            assert forall|c: int| #[trigger] self.nodes@.contains_key(c) implies self.node_wf(c) by {
                assert(old(self).node_wf(c));
                if c == bi {
                    let src = self.source@;
                    assert forall|a: int| #[trigger] src.spans[bi].backed.contains(a) implies a == mi
                        || in_runs(bi, node.lo.used(), a) || in_runs(mi, node.hi.used().remove(0), a) by {
                        if in_runs(bi, n0.lo.used(), a) {
                            let q = choose|q: int| #[trigger] n0.lo.used().contains_key(q) && run_pages(bi + q * PAGE_BYTES as int, pages(n0.lo.used()[q]) as nat).contains(a);
                            assert(node.lo.used().contains_key(q) && node.lo.used()[q] == n0.lo.used()[q]);
                        } else if in_runs(mi, n0.hi.used().remove(0), a) {
                            let q = choose|q: int| #[trigger] n0.hi.used().remove(0).contains_key(q) && run_pages(mi + q * PAGE_BYTES as int, pages(n0.hi.used().remove(0)[q]) as nat).contains(a);
                            assert(node.hi.used().remove(0).contains_key(q) && node.hi.used().remove(0)[q] == n0.hi.used().remove(0)[q]);
                        }
                    }
                }
            }
            assert forall|i: int| 0 <= i < self.chain@.len() implies #[trigger] self.linked(i) by {
                assert(old(self).linked(i));
            }
            // The run lies in its block, apart from the metadata page and from every backed run.
            let run = run_pages(x + h * PAGE_BYTES as int, pages(k as nat) as nat);
            lemma_in_block(x, h as int, pages(k as nat));
            lemma_in_block(bi, 0, 1);
            lemma_in_block(mi, 0, 1);
            lemma_one_page(mi);
            let src = self.source@;
            assert forall|a: int| #[trigger] src.spans[bi].backed.contains(a) implies !run.contains(a) by {
                if a == mi {
                    if !hi {
                        assert(x + h * PAGE_BYTES as int + pages(k as nat) * PAGE_BYTES as int <= mi);
                    }
                } else if in_runs(bi, n0.lo.used(), a) {
                    lemma_run_page(bi, n0.lo, n0.lo.used(), a, h as int, k as nat);
                } else {
                    assert(in_runs(mi, n0.hi.used().remove(0), a));
                    lemma_run_page(mi, n0.hi, n0.hi.used().remove(0), a, h as int, k as nat);
                }
            }
            assert(old_spans[x] == bb0.blocks());
        }
        let xb = if hi { b + BLOCK_BYTES } else { b };
        xb + h * PAGE_BYTES
    }

    /// Cuts a run of order `k` from a new span, when no held span has a free block of order `k` or
    /// more: reserves the span, backs its metadata page, cuts the page from its second block and the
    /// run from its first, and puts its node at the head of the list.
    fn alloc_new(&mut self, k: usize) -> (r: Result<usize, Refused>)
        requires
            old(self).wf(),
            k <= BLOCK_ORDER,
            !old(self).fits(k as nat),
        ensures
            final(self).wf(),
            final(self).spares() == old(self).spares(),
            match r {
                Err(Refused::Source) => {
                    &&& final(self).spans() == old(self).spans()
                    &&& final(self).used() == old(self).used()
                    &&& final(self).metas() == old(self).metas()
                    &&& final(self).source() == old(self).source().refused()
                },
                Ok(p) => {
                    let b = span_of(p as int);
                    &&& !old(self).spans().contains_key(b)
                    &&& !old(self).spans().contains_key(meta_page(b))
                    &&& !final(self).metas().contains(b)
                    &&& final(self).spans().dom() == old(self).spans().dom().insert(b).insert(meta_page(b))
                    &&& final(self).metas() == old(self).metas().insert(meta_page(b))
                    &&& cut(fresh(old(self).used(), b), final(self).used(), p as int, k as nat)
                    &&& final(self).source().unbacked(b, p as int, pages(k as nat) as nat)
                    &&& took_span(old(self).source(), final(self).source(), b)
                },
            },
    {
        let ghost old_used = self.used();
        let ghost old_spans = self.spans();
        let ghost old_idle = self.idle_spans();
        let ghost start = self.source@;
        let base = match self.source.reserve(SPAN_BLOCKS) {
            None => {
                proof {
                    self.lemma_refused(old(self));
                }
                return Err(Refused::Source);
            },
            Some(base) => base,
        };
        let b = base.addr();
        let ghost bi = b as int;
        let ghost mi = meta_page(bi);
        proof {
            assert(!start.spans.contains_key(bi)) by {
                if start.spans.contains_key(bi) {
                    assert(start.apart(bi, SPAN_BLOCKS as nat, bi));
                }
            }
            // The new span is apart from every held one, so neither of its blocks is in the view.
            assert forall|c: int| #[trigger] old(self).nodes@.contains_key(c) implies c + 2 * BLOCK_BYTES as int <= bi || bi + 2 * BLOCK_BYTES as int <= c by {
                old(self).lemma_base(c);
                assert(start.spans.contains_key(c));
                assert(start.apart(bi, SPAN_BLOCKS as nat, c));
            }
            assert(!old_spans.contains_key(bi)) by {
                if old(self).metas@.contains(bi) {
                    assert(old(self).nodes@.contains_key(bi - BLOCK_BYTES as int));
                }
            }
            assert(!old_spans.contains_key(mi)) by {
                if old(self).metas@.contains(mi) {
                    assert(old(self).nodes@.contains_key(mi - BLOCK_BYTES as int));
                }
            }
            lemma_meta(bi);
        }
        let m = b + BLOCK_BYTES;
        let perm = match self.source.back(Ghost(bi), m, 1) {
            None => {
                self.source.release_span(b);
                proof {
                    assert(self.source@.spans =~= start.spans);
                    assert(self.source@ == start.refused());
                    self.lemma_refused(old(self));
                }
                return Err(Refused::Source);
            },
            Some(perm) => perm,
        };
        let tracked raw = perm.get();
        let ghost first = Set::range(m as int, m as int + size_of::<Node>() as int);
        let tracked (node_raw, rest) = raw.split(first);
        let tracked mut typed = node_raw.into_typed::<Node>(m);
        let ptr = base.with_addr(m) as *mut Node;
        let next = match self.head {
            None => 0,
            Some(h) => h.addr(),
        };
        let mut lo = BlockBuddy::new();
        let mut hi = BlockBuddy::new();
        proof {
            lemma_block_pages();
            assert(hi.blocks().contains_key(0) && hi.blocks()[0].free);
            assert(lo.blocks().contains_key(0) && lo.blocks()[0].free);
        }
        let mp = hi.alloc(0).unwrap();
        proof {
            assert(mp == 0);
            assert(hi.used() == Map::<int, nat>::empty().insert(0, 0));
        }
        let h = lo.alloc(k).unwrap();
        ptr_mut_write(ptr, Tracked(&mut typed), Node { next, lo, hi });
        proof {
            self.nodes.borrow_mut().tracked_insert(bi, typed);
            self.rests.borrow_mut().tracked_insert(bi, rest);
        }
        let ghost old_chain = self.chain@;
        self.chain = Ghost(seq![bi] + old_chain);
        self.metas = Ghost(self.metas@.insert(mi));
        self.head = Some(base);
        let ghost x = bi;
        proof {
            let src = self.source@;
            lemma_one_page(mi);
            assert(src.spans[bi].backed =~= Set::<int>::empty().insert(mi));
            assert(lo.used() =~= Map::<int, nat>::empty().insert(h as int, k as nat));
            assert(hi.used().remove(0) =~= Map::<int, nat>::empty());
            assert forall|i: int| 0 <= i < old_chain.len() implies old_chain[i] != bi by {
                old(self).lemma_at(i);
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
            assert forall|c: int| #[trigger] self.metas@.contains(c) implies self.nodes@.contains_key(c - BLOCK_BYTES as int) by {
                if c != mi {
                    assert(old(self).metas@.contains(c));
                }
            }
            assert forall|c: int| #[trigger] self.nodes@.contains_key(c) implies self.node_wf(c) by {
                if c != bi {
                    assert(old(self).node_wf(c));
                    assert(start.spans.contains_key(c));
                    assert(src.spans[c] == start.spans[c]);
                } else {
                    assert(self.rests@[bi].dom() =~= Set::range(mi + size_of::<Node>(), mi + PAGE_BYTES));
                }
            }
            assert forall|i: int| 0 <= i < self.chain@.len() implies #[trigger] self.linked(i) by {
                if i > 0 {
                    assert(old(self).linked(i - 1));
                    assert(chain[i] == old_chain[i - 1]);
                    if i + 1 < chain.len() {
                        assert(chain[i + 1] == old_chain[i]);
                    }
                } else if old_chain.len() > 0 {
                    assert(chain[1] == old_chain[0]);
                }
            }
            // The view gains the new span's two blocks, one holding the run.
            assert(!old(self).metas@.contains(bi));
            assert(!old(self).metas@.contains(mi));
            assert(!old(self).nodes@.contains_key(mi));
            assert(!old(self).nodes@.contains_key(bi - BLOCK_BYTES as int));
            assert(self.spans().dom() =~= old_spans.dom().insert(bi).insert(mi));
            assert forall|c: int| #[trigger] old_spans.contains_key(c) implies self.spans()[c] == old_spans[c] && self.used()[c] == old_used[c] by {
                old(self).lemma_block(c);
                assert(c != bi && c != mi);
                if !self.nodes@.contains_key(c) {
                    assert(c - BLOCK_BYTES as int != bi);
                }
            }
            let fr = fresh(old_used, bi);
            assert(self.used() =~= fr.insert(x, fr[x].insert(h as int, k as nat))) by {
                assert(self.used()[bi] == lo.used());
                assert(self.used()[mi] == hi.used().remove(0));
            }
            assert(self.used()[x].contains_key(h as int));
            assert forall|c: int| #[trigger] self.metas@.contains(c) && c != mi implies (self.used()[c] == old_used[c]
                && self.used()[c - BLOCK_BYTES as int] == old_used[c - BLOCK_BYTES as int]) by {
                old(self).lemma_meta_block(c);
                old(self).lemma_blocks_of(c - BLOCK_BYTES as int);
            }
            assert(!self.idle_spans().contains(mi));
            assert(self.idle_spans() =~= old_idle);
            lemma_meta(bi);
            assert(mi % BLOCK_BYTES as int == 0);
            lemma_address(x, h as int);
            lemma_pages_pos(k as nat);
            assert(placed(h as int, Block { order: k as nat, free: false }));
            let run = run_pages(x + h * PAGE_BYTES as int, pages(k as nat) as nat);
            lemma_in_block(x, h as int, pages(k as nat));
            assert(!run.contains(mi)) by {
                assert(x + h * PAGE_BYTES as int + pages(k as nat) * PAGE_BYTES as int <= mi);
            }
            assert(src.spans[bi].backed.disjoint(run));
            assert(self.span_base(x) == bi);
            assert(took_span(start, src, bi));
        }
        Ok(b + h * PAGE_BYTES)
    }

    /// Cuts a run of order `k`: from the block with a free block of the smallest order at or above
    /// `k`, or from a new span when no held span has one. Refuses, and changes no held span, only
    /// when no held span has one and the source refused in this call, which its view counts.
    pub fn alloc_run(&mut self, k: usize) -> (r: Result<usize, Refused>)
        requires
            old(self).wf(),
            k <= BLOCK_ORDER,
        ensures
            final(self).wf(),
            final(self).spares() == old(self).spares(),
            match r {
                Err(Refused::Source) => {
                    &&& !old(self).fits(k as nat)
                    &&& final(self).spans() == old(self).spans()
                    &&& final(self).used() == old(self).used()
                    &&& final(self).metas() == old(self).metas()
                    &&& final(self).source() == old(self).source().refused()
                },
                Ok(p) => {
                    let b = final(self).span_base(span_of(p as int));
                    &&& final(self).source().unbacked(b, p as int, pages(k as nat) as nat)
                    &&& if old(self).spans().contains_key(span_of(p as int)) {
                        &&& best(old(self).spans(), span_of(p as int), page_of(p as int), k as nat)
                        &&& cut(old(self).used(), final(self).used(), p as int, k as nat)
                        &&& final(self).spans().dom() == old(self).spans().dom()
                        &&& final(self).metas() == old(self).metas()
                        &&& final(self).source() == old(self).source()
                    } else {
                        &&& !old(self).fits(k as nat)
                        &&& span_of(p as int) == b
                        &&& !old(self).spans().contains_key(b)
                        &&& !old(self).spans().contains_key(meta_page(b))
                        &&& !final(self).metas().contains(b)
                        &&& final(self).spans().dom() == old(self).spans().dom().insert(b).insert(meta_page(b))
                        &&& final(self).metas() == old(self).metas().insert(meta_page(b))
                        &&& cut(fresh(old(self).used(), b), final(self).used(), p as int, k as nat)
                        &&& took_span(old(self).source(), final(self).source(), b)
                    }
                },
            },
    {
        let ghost old_spans = self.spans();
        match self.best_span(k) {
            Some((b, hi, o)) => {
                let ghost x = if hi { meta_page(b as int) } else { b as int };
                proof {
                    self.lemma_blocks_of(b as int);
                }
                let p = self.alloc_in(b, hi, k);
                proof {
                    let h = page_of(p as int);
                    let s = old_spans[x];
                    assert(span_of(p as int) == x);
                    assert(s.contains_key(h) && s[h].free && s[h].order >= k);
                    let h0 = choose|h0: int|
                        #[trigger] s.contains_key(h0) && s[h0] == (Block { order: o as nat, free: true });
                    assert(s.contains_key(h0));
                    assert(s[h].order <= o);
                    assert(old_spans.contains_key(x));
                }
                Ok(p)
            },
            None => self.alloc_new(k),
        }
    }

    /// Takes back the run at `p`, none of whose pages is backed. A span left with no run is given
    /// back to the source with its metadata page, unless fewer than the spares are idle, when it
    /// stays as a spare.
    pub fn free_run(&mut self, p: usize)
        requires
            old(self).wf(),
            old(self).holds(p as int),
            old(self).source().unbacked(
                old(self).span_base(span_of(p as int)),
                p as int,
                pages(old(self).used()[span_of(p as int)][page_of(p as int)]) as nat,
            ),
        ensures
            final(self).wf(),
            final(self).spares() == old(self).spares(),
            ({
                let c = span_of(p as int);
                let b = old(self).span_base(c);
                let after = old(self).used().insert(c, old(self).used()[c].remove(page_of(p as int)));
                if after[b].dom() != Set::<int>::empty() || after[meta_page(b)].dom() != Set::<int>::empty()
                    || old(self).idle_spans().len() < old(self).spares() {
                    &&& final(self).used() == after
                    &&& final(self).spans().dom() == old(self).spans().dom()
                    &&& final(self).metas() == old(self).metas()
                    &&& final(self).source() == old(self).source()
                } else {
                    &&& final(self).used() == old(self).used().remove(b).remove(meta_page(b))
                    &&& final(self).spans().dom() == old(self).spans().dom().remove(b).remove(meta_page(b))
                    &&& final(self).metas() == old(self).metas().remove(meta_page(b))
                    &&& final(self).source() == old(self).source().released_span(b)
                }
            }),
    {
        let ghost old_used = self.used();
        let ghost old_spans = self.spans();
        let ghost old_idle = self.idle_spans();
        let ghost start = self.source@;
        let ghost old_chain = self.chain@;
        let c = p - p % BLOCK_BYTES;
        let h = (p % BLOCK_BYTES) / PAGE_BYTES;
        let ghost ci = c as int;
        proof {
            assert(old_spans.contains_key(ci));
            self.lemma_block(ci);
            lemma_head(p as int);
        }
        let (prev, b) = self.find(c);
        let ghost bi = b as int;
        let ghost mi = meta_page(bi);
        let ghost j = choose|j: int|
            0 <= j < old_chain.len() && #[trigger] old_chain[j] == bi && prev as int == if j == 0 {
                0
            } else {
                old_chain[j - 1]
            };
        proof {
            self.lemma_at(j);
            if j > 0 {
                self.lemma_at(j - 1);
            }
            if j + 1 < old_chain.len() {
                self.lemma_at(j + 1);
            }
            self.lemma_blocks_of(bi);
            lemma_meta(bi);
        }
        let hp = self.head.unwrap();
        let ghost n0 = self.node(bi);
        let ghost u0 = old_used[ci];
        let ptr = node_at(hp, b);
        let tracked mut perm = self.nodes.borrow_mut().tracked_remove(bi);
        let mut node = ptr_mut_read(ptr, Tracked(&mut perm));
        let in_hi = c != b;
        proof {
            if in_hi {
                assert(ci == mi);
                assert(u0 == n0.hi.used().remove(0));
                assert(h != 0);
                assert(n0.hi.used().contains_key(h as int));
            } else {
                assert(u0 == n0.lo.used());
            }
        }
        if in_hi {
            node.hi.free(h);
        } else {
            node.lo.free(h);
        }
        let idle = node.lo.is_idle() && node.hi.idle_from(1);
        let ghost after = old_used.insert(ci, u0.remove(h as int));
        proof {
            if in_hi {
                assert(node.hi.used().remove(0) =~= u0.remove(h as int));
                assert(node.hi.used().contains_key(0) && node.hi.used()[0] == 0);
                assert(node.lo.used() == n0.lo.used());
            } else {
                assert(node.lo.used() == u0.remove(h as int));
                assert(node.hi.used() == n0.hi.used());
            }
            assert(after[bi] == node.lo.used());
            assert(after[mi] == node.hi.used().remove(0));
            node.hi.lemma_view();
            assert(idle == (after[bi].dom() == Set::<int>::empty() && after[mi].dom() == Set::<int>::empty())) by {
                if node.hi.used().remove(0).dom() == Set::<int>::empty() {
                    assert forall|q: int| 1 <= q implies !(#[trigger] node.hi.used().dom().contains(q)) by {
                        assert(!node.hi.used().remove(0).dom().contains(q));
                    }
                }
                if forall|q: int| 1 <= q ==> !(#[trigger] node.hi.used().dom().contains(q)) {
                    assert forall|q: int| !(#[trigger] node.hi.used().remove(0).dom().contains(q)) by {
                        if node.hi.used().remove(0).dom().contains(q) {
                            assert(node.hi.used().dom().contains(q));
                            assert(placed(q, node.hi.blocks()[q]));
                        }
                    }
                    assert(node.hi.used().remove(0).dom() =~= Set::<int>::empty());
                }
            }
            assert(!old_idle.contains(mi)) by {
                assert(u0.contains_key(h as int));
            }
            // Every backed page but the metadata page is still in a run: the freed run held none.
            let run = run_pages(p as int, pages(u0[h as int]) as nat);
            assert forall|a: int| #[trigger] start.spans[bi].backed.contains(a) implies a == mi
                || in_runs(bi, node.lo.used(), a) || in_runs(mi, node.hi.used().remove(0), a) by {
                if in_runs(bi, n0.lo.used(), a) {
                    let q = choose|q: int| #[trigger] n0.lo.used().contains_key(q) && run_pages(bi + q * PAGE_BYTES as int, pages(n0.lo.used()[q]) as nat).contains(a);
                    if !in_hi && q == h as int {
                        assert(run.contains(a));
                    }
                    assert(node.lo.used().contains_key(q) && node.lo.used()[q] == n0.lo.used()[q]);
                } else if in_runs(mi, n0.hi.used().remove(0), a) {
                    let q = choose|q: int| #[trigger] n0.hi.used().remove(0).contains_key(q) && run_pages(mi + q * PAGE_BYTES as int, pages(n0.hi.used().remove(0)[q]) as nat).contains(a);
                    if in_hi && q == h as int {
                        assert(run.contains(a));
                    }
                    assert(node.hi.used().remove(0).contains_key(q) && node.hi.used().remove(0)[q] == n0.hi.used().remove(0)[q]);
                }
            }
            assert forall|m: int| #[trigger] self.metas@.contains(m) && m != mi implies (after[m] == old_used[m]
                && after[m - BLOCK_BYTES as int] == old_used[m - BLOCK_BYTES as int]) by {
                old(self).lemma_meta_block(m);
                assert(m != bi);
                assert(m - BLOCK_BYTES as int != mi);
            }
        }
        if idle && self.idle >= self.spares {
            let next = node.next;
            if prev == 0 {
                if next == 0 {
                    self.head = None;
                } else {
                    self.head = Some(hp.with_addr(next));
                }
            } else {
                proof {
                    assert(prev as int != bi);
                }
                let pptr = node_at(hp, prev);
                let tracked mut pperm = self.nodes.borrow_mut().tracked_remove(prev as int);
                let mut pnode = ptr_mut_read(pptr, Tracked(&mut pperm));
                pnode.next = next;
                ptr_mut_write(pptr, Tracked(&mut pperm), pnode);
                proof {
                    self.nodes.borrow_mut().tracked_insert(prev as int, pperm);
                }
            }
            self.chain = Ghost(old_chain.remove(j));
            self.metas = Ghost(self.metas@.remove(mi));
            let m = b + BLOCK_BYTES;
            let tracked rest = self.rests.borrow_mut().tracked_remove(bi);
            let tracked node_raw = perm.into_raw();
            let tracked raw = node_raw.join(rest);
            proof {
                lemma_one_page(mi);
                assert(raw.dom() =~= Set::range(mi, mi + PAGE_BYTES));
                assert(start.spans[bi].backed.contains(mi));
            }
            self.source.release(Ghost(bi), m, 1, Tracked(raw));
            proof {
                assert(node.lo.used().dom() =~= Set::<int>::empty());
                assert(node.hi.used().remove(0).dom() =~= Set::<int>::empty());
                assert forall|a: int| #[trigger] start.spans[bi].backed.contains(a) implies a == mi by {
                    if a != mi {
                        if in_runs(bi, node.lo.used(), a) {
                            let q = choose|q: int| #[trigger] node.lo.used().contains_key(q) && run_pages(bi + q * PAGE_BYTES as int, pages(node.lo.used()[q]) as nat).contains(a);
                            assert(node.lo.used().dom().contains(q));
                        } else {
                            let q = choose|q: int| #[trigger] node.hi.used().remove(0).contains_key(q) && run_pages(mi + q * PAGE_BYTES as int, pages(node.hi.used().remove(0)[q]) as nat).contains(a);
                            assert(node.hi.used().remove(0).dom().contains(q));
                        }
                    }
                }
                assert(self.source@.spans[bi].backed =~= Set::<int>::empty());
            }
            self.source.release_span(b);
            proof {
                let src = self.source@;
                assert(src.spans =~= start.spans.remove(bi));
                assert(src == start.released_span(bi));
                let chain = self.chain@;
                let n = old_chain.len();
                assert(chain.len() == n - 1);
                assert forall|i: int| 0 <= i < n - 1 implies #[trigger] chain[i] == if i < j { old_chain[i] } else { old_chain[i + 1] } by {}
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
                        let oi = choose|oi: int| 0 <= oi < n && old_chain[oi] == x;
                        assert(oi != j);
                        let i = if oi < j { oi } else { oi - 1 };
                        assert(chain[i] == x);
                    }
                }
                assert forall|x: int| #[trigger] self.nodes@.contains_key(x) implies self.metas@.contains(meta_page(x)) by {
                    assert(old(self).metas@.contains(meta_page(x)));
                }
                assert forall|x: int| #[trigger] self.metas@.contains(x) implies self.nodes@.contains_key(x - BLOCK_BYTES as int) by {
                    assert(old(self).nodes@.contains_key(x - BLOCK_BYTES as int));
                }
                assert forall|x: int| #[trigger] self.nodes@.contains_key(x) implies self.node_wf(x) by {
                    assert(old(self).node_wf(x));
                    assert(start.spans[x] == src.spans[x]);
                }
                assert forall|i: int| 0 <= i < chain.len() implies #[trigger] self.linked(i) by {
                    if i + 1 == j {
                        assert(old(self).linked(j));
                        if j + 1 < n {
                            assert(chain[j] == old_chain[j + 1]);
                        }
                    } else if i < j {
                        assert(old(self).linked(i));
                        assert(prev as int == old_chain[j - 1]);
                        assert(old_chain[i] != old_chain[j - 1]);
                        assert(old_chain[i] != prev as int);
                    } else {
                        assert(old(self).linked(i + 1));
                        if j > 0 {
                            assert(prev as int == old_chain[j - 1]);
                            assert(old_chain[i + 1] != old_chain[j - 1]);
                        } else {
                            old(self).lemma_at(i + 1);
                        }
                        assert(old_chain[i + 1] != prev as int);
                        if i + 1 < chain.len() {
                            assert(chain[i + 1] == old_chain[i + 2]);
                        }
                    }
                }
                if j == 0 {
                    assert(old(self).linked(0));
                    if n > 1 {
                        assert(chain[0] == old_chain[1]);
                    }
                }
                assert(self.spans().dom() =~= old_spans.dom().remove(bi).remove(mi));
                assert(self.used() =~= old_used.remove(bi).remove(mi)) by {
                    assert forall|x: int| #[trigger] self.used().contains_key(x) implies self.used()[x] == old_used[x] by {
                        old(self).lemma_block(x);
                    }
                }
                assert(self.idle_spans() =~= old_idle) by {
                    assert forall|x: int| #[trigger] self.metas@.contains(x) implies (self.used()[x] == old_used[x]
                        && self.used()[x - BLOCK_BYTES as int] == old_used[x - BLOCK_BYTES as int]) by {
                        old(self).lemma_meta_block(x);
                        old(self).lemma_blocks_of(x - BLOCK_BYTES as int);
                    }
                }
            }
        } else {
            ptr_mut_write(ptr, Tracked(&mut perm), node);
            proof {
                self.nodes.borrow_mut().tracked_insert(bi, perm);
            }
            if idle {
                self.idle = self.idle + 1;
            }
            proof {
                assert(self.nodes@.dom() =~= old(self).nodes@.dom());
                assert(self.used() =~= after) by {
                    assert forall|x: int| #[trigger] self.used().contains_key(x) && x != ci implies self.used()[x] == old_used[x] by {
                        if x != bi && !self.nodes@.contains_key(x) && x - BLOCK_BYTES as int == bi {
                            assert(x == mi && !in_hi);
                            assert(node.hi == n0.hi);
                        }
                    }
                }
                assert(self.spans().dom() =~= old_spans.dom());
                if idle {
                    assert(self.idle_spans() =~= old_idle.insert(mi));
                } else {
                    assert(self.idle_spans() =~= old_idle);
                }
                assert forall|x: int| #[trigger] self.nodes@.contains_key(x) implies self.node_wf(x) by {
                    assert(old(self).node_wf(x));
                }
                assert forall|i: int| 0 <= i < self.chain@.len() implies #[trigger] self.linked(i) by {
                    assert(old(self).linked(i));
                }
            }
        }
    }

    /// The allocated run of order `k` at `p` lies in its block, a block of a held span, with `p` its
    /// page `page_of(p)`, apart from the span's metadata page.
    proof fn lemma_run(&self, p: int, k: nat)
        requires
            self.wf(),
            self.holds(p),
            self.used()[span_of(p)][page_of(p)] == k,
        ensures
            k <= BLOCK_ORDER,
            self.nodes@.contains_key(self.span_base(span_of(p))),
            self.node_wf(self.span_base(span_of(p))),
            self.head is Some,
            self.span_base(span_of(p)) + span_bytes(SPAN_BLOCKS as nat) <= usize::MAX as int + 1,
            p == span_of(p) + page_of(p) * PAGE_BYTES,
            self.source@.runs_in(self.span_base(span_of(p)), p, pages(k) as nat),
            !run_pages(p, pages(k) as nat).contains(meta_page(self.span_base(span_of(p)))),
            in_runs(span_of(p), self.used()[span_of(p)], p),
            forall|a: int| #[trigger] run_pages(p, pages(k) as nat).contains(a) ==> in_runs(span_of(p), self.used()[span_of(p)], a),
    {
        let c = span_of(p);
        let h = page_of(p);
        let pb = PAGE_BYTES as int;
        assert(self.used().dom() =~= self.spans().dom()) by {
            self.lemma_view();
        }
        self.lemma_block(c);
        let b = self.span_base(c);
        self.lemma_base(b);
        self.lemma_blocks_of(b);
        lemma_meta(b);
        let r = if c == b {
            self.node(b).lo
        } else {
            self.node(b).hi
        };
        r.lemma_view();
        assert(r.used().contains_key(h));
        assert(r.blocks().contains_key(h) && !r.blocks()[h].free && r.blocks()[h].order == k);
        assert(placed(h, r.blocks()[h]));
        lemma_pages_pos(k);
        lemma_head(p);
        lemma_in_block(c, h, pages(k));
        if c != b {
            assert(h != 0);
        } else {
            assert(p + pages(k) * pb <= meta_page(b));
        }
        assert(self.used()[c].contains_key(h));
        assert(run_pages(c + h * pb, pages(k) as nat).contains(p));
        assert forall|a: int| #[trigger] run_pages(p, pages(k) as nat).contains(a) implies in_runs(c, self.used()[c], a) by {
            assert(self.used()[c].contains_key(h));
        }
    }

    /// Backs the pages of the allocated run of order `k` at `p`, none of them backed, through the
    /// source, and returns a pointer to the run with the permission to exactly its bytes; or
    /// refuses, backs nothing and changes nothing but the source's count of refusals.
    pub fn back_run(&mut self, p: usize, k: usize) -> (r: Option<(*mut u8, Tracked<PointsToRaw>)>)
        requires
            old(self).wf(),
            old(self).holds(p as int),
            old(self).used()[span_of(p as int)][page_of(p as int)] == k,
            old(self).source().unbacked(old(self).span_base(span_of(p as int)), p as int, pages(k as nat) as nat),
        ensures
            final(self).wf(),
            final(self).spares() == old(self).spares(),
            final(self).spans() == old(self).spans(),
            final(self).used() == old(self).used(),
            final(self).metas() == old(self).metas(),
            match r {
                None => final(self).source() == old(self).source().refused(),
                Some((ptr, perm)) => {
                    &&& ptr@.addr == p
                    &&& ptr@.provenance == old(self).source().provenance
                    &&& perm@.is_range(p as int, pages(k as nat) * PAGE_BYTES)
                    &&& perm@.provenance() == old(self).source().provenance
                    &&& final(self).source() == old(self).source().backed_run(
                        old(self).span_base(span_of(p as int)),
                        p as int,
                        pages(k as nat) as nat,
                    )
                },
            },
    {
        let ghost bi = self.span_base(span_of(p as int));
        let ghost ci = span_of(p as int);
        let ghost run = run_pages(p as int, pages(k as nat) as nat);
        proof {
            self.lemma_run(p as int, k as nat);
            self.lemma_blocks_of(bi);
        }
        let hp = self.head.unwrap();
        let n = order_pages(k);
        let ghost start = self.source@;
        let perm = match self.source.back(Ghost(bi), p, n) {
            None => {
                proof {
                    self.lemma_refused(old(self));
                }
                return None;
            },
            Some(perm) => perm,
        };
        proof {
            assert(self.spans() =~= old(self).spans());
            assert(self.used() =~= old(self).used());
            assert forall|c: int| #[trigger] self.nodes@.contains_key(c) implies self.node_wf(c) by {
                assert(old(self).node_wf(c));
                if c == bi {
                    let lo = self.node(c).lo.used();
                    let hi = self.node(c).hi.used().remove(0);
                    assert forall|a: int| #[trigger] self.source@.spans[c].backed.contains(a) implies a
                        == meta_page(c) || in_runs(c, lo, a) || in_runs(meta_page(c), hi, a) by {
                        if run.contains(a) {
                            assert(in_runs(ci, self.used()[ci], a));
                        }
                    }
                } else {
                    assert(self.source@.spans[c] == start.spans[c]);
                }
            }
            assert forall|i: int| 0 <= i < self.chain@.len() implies #[trigger] self.linked(i) by {
                assert(old(self).linked(i));
            }
        }
        Some((hp.with_addr(p), perm))
    }

    /// Gives back through the source the pages of the allocated run of order `k` at `p`, every one
    /// of them backed, taking the permission to its bytes.
    pub fn release_run(&mut self, p: usize, k: usize, perm: Tracked<PointsToRaw>)
        requires
            old(self).wf(),
            old(self).holds(p as int),
            old(self).used()[span_of(p as int)][page_of(p as int)] == k,
            old(self).source().backed(old(self).span_base(span_of(p as int)), p as int, pages(k as nat) as nat),
            perm@.is_range(p as int, pages(k as nat) * PAGE_BYTES),
            perm@.provenance() == old(self).source().provenance,
        ensures
            final(self).wf(),
            final(self).spares() == old(self).spares(),
            final(self).spans() == old(self).spans(),
            final(self).used() == old(self).used(),
            final(self).metas() == old(self).metas(),
            final(self).source() == old(self).source().released_run(
                old(self).span_base(span_of(p as int)),
                p as int,
                pages(k as nat) as nat,
            ),
    {
        let ghost bi = self.span_base(span_of(p as int));
        let ghost run = run_pages(p as int, pages(k as nat) as nat);
        proof {
            self.lemma_run(p as int, k as nat);
        }
        let n = order_pages(k);
        let ghost start = self.source@;
        self.source.release(Ghost(bi), p, n, perm);
        proof {
            assert(self.spans() =~= old(self).spans());
            assert(self.used() =~= old(self).used());
            assert forall|c: int| #[trigger] self.nodes@.contains_key(c) implies self.node_wf(c) by {
                assert(old(self).node_wf(c));
                if c == bi {
                    let lo = self.node(c).lo.used();
                    let hi = self.node(c).hi.used().remove(0);
                    assert(!run.contains(meta_page(c)));
                    assert forall|a: int| #[trigger] self.source@.spans[c].backed.contains(a) implies a
                        == meta_page(c) || in_runs(c, lo, a) || in_runs(meta_page(c), hi, a) by {
                        assert(start.spans[c].backed.contains(a));
                    }
                } else {
                    assert(self.source@.spans[c] == start.spans[c]);
                }
            }
            assert forall|i: int| 0 <= i < self.chain@.len() implies #[trigger] self.linked(i) by {
                assert(old(self).linked(i));
            }
        }
    }
}

} // verus!
