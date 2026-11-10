//! The buddy of one block: it cuts page runs of order 0 up to BLOCK_ORDER out of the BLOCK_PAGES
//! pages of a block, and takes them back.
//!
//! Its state is out of band: one tag byte per page. The first page of each block, its head, records
//! the block's order and whether it is free; every other page of the block is inner. The ghost view
//! maps each head to its block.
//!
//! - `alloc(k)` takes the free block of the smallest order at or above k, splits it down to order k
//!   and returns its head; it refuses, and changes nothing, exactly when no free block has order k
//!   or more.
//! - `free(p)` takes back the run at p and coalesces it with its buddy while the buddy is free. It
//!   never refuses.
//! - With no run allocated the view is the initial one, a single free block of order BLOCK_ORDER
//!   (`lemma_idle`), and `is_idle` says whether that holds.
//!
//! `lemma_view` states the invariant on the view: the blocks partition the pages, each aligned to
//! its order, and no free block has a free buddy of its order.
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

use crate::arch::*;

verus! {

broadcast use vstd::set_lib::range_set_properties;

/// The tag of an inner page.
const INNER: u8 = 0;

/// Added to a head's tag when its block is free.
const FREE: u8 = 64;

/// The pages of a run of order `o`: two to the `o`.
pub open spec fn pages(o: nat) -> int
    decreases o,
{
    if o == 0 {
        1
    } else {
        2 * pages((o - 1) as nat)
    }
}

/// One block: its order and whether it is free.
pub ghost struct Block {
    pub order: nat,
    pub free: bool,
}

/// The block at head `h` lies in the pages of one block and is aligned to its order.
pub open spec fn placed(h: int, b: Block) -> bool {
    &&& 0 <= h
    &&& b.order <= BLOCK_ORDER
    &&& h % pages(b.order) == 0
    &&& h + pages(b.order) <= BLOCK_PAGES as int
}

/// The block at head `h` holds page `p`.
pub open spec fn within(h: int, b: Block, p: int) -> bool {
    h <= p < h + pages(b.order)
}

/// The head of the buddy of the block of order `o` at `h`: the other half of the block of order
/// `o + 1` that holds it.
pub open spec fn buddy(h: int, o: nat) -> int {
    if h % pages((o + 1) as nat) == 0 {
        h + pages(o)
    } else {
        h - pages(o)
    }
}

/// `blocks` has a free block of order `o` at `h`.
pub open spec fn free_block(blocks: Map<int, Block>, h: int, o: nat) -> bool {
    blocks.contains_key(h) && blocks[h] == Block { order: o, free: true }
}

/// Some block holds page `p`.
pub open spec fn covered(blocks: Map<int, Block>, p: int) -> bool {
    exists|h: int| #[trigger] blocks.contains_key(h) && within(h, blocks[h], p)
}

/// The blocks are placed, pairwise apart, and hold every page.
pub open spec fn partitioned(blocks: Map<int, Block>) -> bool {
    &&& forall|h: int| #[trigger] blocks.contains_key(h) ==> placed(h, blocks[h])
    &&& forall|h: int, q: int|
        #[trigger] blocks.contains_key(h) && #[trigger] blocks.contains_key(q) && h != q ==> h
            + pages(blocks[h].order) <= q || q + pages(blocks[q].order) <= h
    &&& forall|p: int| 0 <= p < BLOCK_PAGES as int ==> #[trigger] covered(blocks, p)
}

/// No free block below the block's order has a free buddy of its order.
pub open spec fn coalesced(blocks: Map<int, Block>) -> bool {
    forall|h: int|
        #[trigger] blocks.contains_key(h) && blocks[h].free && blocks[h].order < BLOCK_ORDER
            ==> !free_block(blocks, buddy(h, blocks[h].order), blocks[h].order)
}

/// The view of a block nothing has been cut from.
pub open spec fn initial() -> Map<int, Block> {
    Map::empty().insert(0, Block { order: BLOCK_ORDER as nat, free: true })
}

/// The tag of a block's head.
spec fn tag(b: Block) -> int {
    b.order as int + 1 + (if b.free {
        FREE as int
    } else {
        0int
    })
}

/// `w` with every page of the run of `len` pages from `start` owned by `start`.
spec fn reowned(w: Map<int, int>, start: int, len: int) -> Map<int, int> {
    Map::new(
        vstd::set_lib::set_int_range(0, BLOCK_PAGES as int),
        |p: int|
            if start <= p < start + len {
                start
            } else {
                w[p]
            },
    )
}

pub proof fn lemma_pages_pos(o: nat)
    ensures
        pages(o) >= 1,
    decreases o,
{
    if o > 0 {
        lemma_pages_pos((o - 1) as nat);
    }
}

/// A run of a higher order is a whole number of runs of a lower one.
pub proof fn lemma_pages(a: nat, b: nat)
    requires
        a <= b,
    ensures
        1 <= pages(a) <= pages(b),
        pages(b) % pages(a) == 0,
    decreases b - a,
{
    lemma_pages_pos(a);
    if a == b {
        lemma_fundamental_div_mod_converse_mod(pages(a), pages(a), 1, 0);
    } else {
        let c = (b - 1) as nat;
        lemma_pages(a, c);
        lemma_fundamental_div_mod(pages(c), pages(a));
        let q = pages(c) / pages(a);
        assert(pages(b) == 2 * pages(c));
        assert(pages(b) == (2 * q) * pages(a) + 0) by (nonlinear_arith)
            requires
                pages(b) == 2 * pages(c),
                pages(c) == pages(a) * q + pages(c) % pages(a),
                pages(c) % pages(a) == 0,
        ;
        lemma_fundamental_div_mod_converse_mod(pages(b), pages(a), 2 * q, 0);
    }
}

pub proof fn lemma_block_pages()
    ensures
        pages(BLOCK_ORDER as nat) == BLOCK_PAGES as int,
{
    assert(pages(BLOCK_ORDER as nat) == BLOCK_PAGES as int) by (compute);
}

/// What is aligned to a higher order is aligned to a lower one.
proof fn lemma_aligned_down(x: int, a: nat, b: nat)
    requires
        a <= b,
        x % pages(b) == 0,
    ensures
        x % pages(a) == 0,
{
    lemma_pages(a, b);
    lemma_fundamental_div_mod(x, pages(b));
    lemma_fundamental_div_mod(pages(b), pages(a));
    let q = x / pages(b);
    let r = pages(b) / pages(a);
    assert(x == (q * r) * pages(a) + 0) by (nonlinear_arith)
        requires
            x == pages(b) * q + x % pages(b),
            x % pages(b) == 0,
            pages(b) == pages(a) * r + pages(b) % pages(a),
            pages(b) % pages(a) == 0,
    ;
    lemma_fundamental_div_mod_converse_mod(x, pages(a), q * r, 0);
}

/// The lower half of a block of order `o + 1` and its upper half are buddies.
proof fn lemma_upper(h: int, o: nat)
    requires
        h % pages((o + 1) as nat) == 0,
    ensures
        h % pages(o) == 0,
        (h + pages(o)) % pages(o) == 0,
        (h + pages(o)) % pages((o + 1) as nat) == pages(o),
        buddy(h, o) == h + pages(o),
        buddy(h + pages(o), o) == h,
{
    let p = pages(o);
    lemma_pages_pos(o);
    assert(pages((o + 1) as nat) == 2 * p);
    lemma_fundamental_div_mod(h, 2 * p);
    let q = h / (2 * p);
    assert(h == (2 * q) * p + 0 && h + p == (2 * q + 1) * p + 0 && h + p == q * (2 * p) + p)
        by (nonlinear_arith)
        requires
            h == (2 * p) * q + h % (2 * p),
            h % (2 * p) == 0,
    ;
    lemma_fundamental_div_mod_converse_mod(h, p, 2 * q, 0);
    lemma_fundamental_div_mod_converse_mod(h + p, p, 2 * q + 1, 0);
    lemma_fundamental_div_mod_converse_mod(h + p, 2 * p, q, p);
}

/// A head aligned to `o` but not to `o + 1` is an upper half.
proof fn lemma_lower(h: int, o: nat)
    requires
        0 <= h,
        h % pages(o) == 0,
        h % pages((o + 1) as nat) != 0,
    ensures
        pages(o) <= h,
        (h - pages(o)) % pages((o + 1) as nat) == 0,
{
    let p = pages(o);
    lemma_pages_pos(o);
    assert(pages((o + 1) as nat) == 2 * p);
    lemma_fundamental_div_mod(h, p);
    let a = h / p;
    assert(h == p * a) by {
        assert(h == p * a + h % p);
    }
    assert(a >= 0) by (nonlinear_arith)
        requires
            h == p * a,
            h >= 0,
            p > 0,
    ;
    lemma_fundamental_div_mod(a, 2);
    let c = a / 2;
    if a % 2 == 0 {
        assert(h == c * (2 * p) + 0) by (nonlinear_arith)
            requires
                h == p * a,
                a == 2 * c + 0,
        ;
        lemma_fundamental_div_mod_converse_mod(h, 2 * p, c, 0);
        assert(false);
    }
    assert(a == 2 * c + 1);
    assert(h - p == c * (2 * p) + 0 && h - p >= 0) by (nonlinear_arith)
        requires
            h == p * a,
            a == 2 * c + 1,
            a >= 0,
            p > 0,
    ;
    lemma_fundamental_div_mod_converse_mod(h - p, 2 * p, c, 0);
}

/// A head's buddy is a head of the same order whose buddy is the head, and the two are the halves of
/// a block of the next order.
proof fn lemma_buddy(h: int, o: nat)
    requires
        0 <= h,
        h % pages(o) == 0,
    ensures
        0 <= buddy(h, o),
        buddy(h, o) % pages(o) == 0,
        buddy(buddy(h, o), o) == h,
        h % pages((o + 1) as nat) == 0 ==> buddy(h, o) == h + pages(o),
        h % pages((o + 1) as nat) != 0 ==> buddy(h, o) == h - pages(o) && buddy(h, o) % pages(
            (o + 1) as nat,
        ) == 0,
{
    lemma_pages_pos(o);
    if h % pages((o + 1) as nat) == 0 {
        lemma_upper(h, o);
    } else {
        lemma_lower(h, o);
        lemma_upper(h - pages(o), o);
    }
}

/// An aligned run that starts inside the block ends inside it.
proof fn lemma_fit(x: int, o: nat)
    requires
        0 <= x < BLOCK_PAGES as int,
        o <= BLOCK_ORDER,
        x % pages(o) == 0,
    ensures
        x + pages(o) <= BLOCK_PAGES as int,
{
    lemma_pages(o, BLOCK_ORDER as nat);
    lemma_block_pages();
    let p = pages(o);
    let n = BLOCK_PAGES as int;
    lemma_fundamental_div_mod(x, p);
    lemma_fundamental_div_mod(n, p);
    let q = x / p;
    let r = n / p;
    assert(x == q * p && n == r * p) by (nonlinear_arith)
        requires
            x == p * q + x % p,
            x % p == 0,
            n == p * r + n % p,
            n % p == 0,
    ;
    lemma_mul_strict_inequality_converse(q, r, p);
    lemma_mul_inequality(q + 1, r, p);
    assert((q + 1) * p == q * p + p) by (nonlinear_arith);
}

/// Two heads aligned to `o`, the second within the first's run of order `o`, are one.
proof fn lemma_same_block(h: int, s: int, o: nat)
    requires
        h % pages(o) == 0,
        s % pages(o) == 0,
        h <= s < h + pages(o),
    ensures
        h == s,
{
    let p = pages(o);
    lemma_pages_pos(o);
    lemma_fundamental_div_mod(h, p);
    lemma_fundamental_div_mod(s, p);
    let a = h / p;
    let c = s / p;
    assert(s - h == (c - a) * p + 0) by (nonlinear_arith)
        requires
            h == p * a + h % p,
            h % p == 0,
            s == p * c + s % p,
            s % p == 0,
    ;
    lemma_fundamental_div_mod_converse_mod(s - h, p, c - a, 0);
    lemma_fundamental_div_mod_converse_mod(s - h, p, 0, s - h);
}

/// The pages of a run of order `o`.
fn order_pages(o: usize) -> (r: usize)
    requires
        o <= BLOCK_ORDER,
    ensures
        r as int == pages(o as nat),
{
    let mut r: usize = 1;
    let mut i: usize = 0;
    while i < o
        invariant
            i <= o <= BLOCK_ORDER,
            r as int == pages(i as nat),
        decreases o - i,
    {
        proof {
            lemma_pages((i + 1) as nat, BLOCK_ORDER as nat);
            lemma_block_pages();
        }
        r = r * 2;
        i = i + 1;
    }
    r
}

/// The buddy state of one block's pages.
pub struct BlockBuddy {
    tags: [u8; BLOCK_PAGES],
    blocks: Ghost<Map<int, Block>>,
    owner: Ghost<Map<int, int>>,
}

impl BlockBuddy {
    /// The blocks, by head.
    pub closed spec fn blocks(&self) -> Map<int, Block> {
        self.blocks@
    }

    /// The allocated runs, by head, with their orders.
    pub open spec fn used(&self) -> Map<int, nat> {
        Map::new(
            self.blocks().dom().filter(|h: int| !self.blocks()[h].free),
            |h: int| self.blocks()[h].order,
        )
    }

    /// Some free block has order `k` or more.
    pub open spec fn fits(&self, k: nat) -> bool {
        exists|h: int|
            #[trigger] self.blocks().contains_key(h) && self.blocks()[h].free && self.blocks()[h].order
                >= k
    }

    /// The tags record the blocks: each head's tag is its block's, every other page of a block is
    /// inner, every page has an owner whose block holds it, and the blocks are coalesced.
    pub closed spec fn wf(&self) -> bool {
        let b = self.blocks@;
        let t = self.tags@;
        let w = self.owner@;
        &&& forall|h: int| #[trigger]
            b.contains_key(h) ==> placed(h, b[h]) && t[h] as int == tag(b[h])
        &&& forall|p: int|
            #![trigger t[p]]
            0 <= p < BLOCK_PAGES as int && t[p] != INNER ==> b.contains_key(p)
        &&& forall|h: int, p: int|
            #![trigger b.contains_key(h), t[p]]
            b.contains_key(h) && h < p < h + pages(b[h].order) ==> t[p] == INNER
        &&& forall|p: int|
            0 <= p < BLOCK_PAGES as int ==> b.contains_key(#[trigger] w[p]) && within(
                w[p],
                b[w[p]],
                p,
            )
        &&& coalesced(b)
    }

    /// Two blocks are apart.
    proof fn lemma_apart(&self, h: int, q: int)
        requires
            self.wf(),
            self.blocks@.contains_key(h),
            self.blocks@.contains_key(q),
            h != q,
        ensures
            h + pages(self.blocks@[h].order) <= q || q + pages(self.blocks@[q].order) <= h,
    {
        let t = self.tags@;
        assert(t[h] as int == tag(self.blocks@[h]));
        assert(t[q] as int == tag(self.blocks@[q]));
    }

    /// The invariant on the view: the blocks partition the block's pages, each aligned to its order,
    /// and no free block has a free buddy of its order.
    pub proof fn lemma_view(&self)
        requires
            self.wf(),
        ensures
            partitioned(self.blocks()),
            coalesced(self.blocks()),
    {
        let b = self.blocks@;
        assert forall|h: int, q: int|
            #[trigger] b.contains_key(h) && #[trigger] b.contains_key(q) && h != q implies h + pages(
            b[h].order,
        ) <= q || q + pages(b[q].order) <= h by {
            self.lemma_apart(h, q);
        }
        assert forall|p: int| 0 <= p < BLOCK_PAGES as int implies #[trigger] covered(b, p) by {
            let h = self.owner@[p];
            assert(b.contains_key(h) && within(h, b[h], p));
        }
    }

    /// With no run allocated, the view is the initial one.
    pub proof fn lemma_idle(&self)
        requires
            self.wf(),
            self.used().dom() == Set::<int>::empty(),
        ensures
            self.blocks() == initial(),
    {
        let b = self.blocks@;
        assert forall|h: int| #[trigger] b.contains_key(h) implies b[h].free by {
            if !b[h].free {
                assert(self.used().dom().contains(h));
            }
        }
        lemma_block_pages();
        self.lemma_whole(BLOCK_ORDER as nat, 0);
        let h0 = self.owner@[0];
        assert(b.contains_key(h0) && within(h0, b[h0], 0));
        assert(placed(h0, b[h0]));
        assert(h0 == 0);
        lemma_pages(b[0].order, BLOCK_ORDER as nat);
        assert(b[0].order == BLOCK_ORDER);
        assert forall|q: int| #[trigger] b.contains_key(q) implies q == 0 by {
            if q != 0 {
                assert(placed(q, b[q]));
                lemma_pages_pos(b[q].order);
                assert(self.tags@[q] as int == tag(b[q]));
            }
        }
        assert(b =~= initial());
    }

    /// With every block free, the block holding an aligned run of order `o` has order `o` or more.
    proof fn lemma_whole(&self, o: nat, s: int)
        requires
            self.wf(),
            forall|h: int| #[trigger] self.blocks@.contains_key(h) ==> self.blocks@[h].free,
            o <= BLOCK_ORDER,
            0 <= s,
            s % pages(o) == 0,
            s + pages(o) <= BLOCK_PAGES as int,
        ensures
            self.blocks@[self.owner@[s]].order >= o,
        decreases o,
    {
        if o > 0 {
            let c = (o - 1) as nat;
            let p = pages(c);
            let b = self.blocks@;
            let w = self.owner@;
            lemma_pages_pos(c);
            assert((c + 1) as nat == o);
            assert(pages(o) == 2 * p);
            lemma_upper(s, c);
            self.lemma_whole(c, s);
            let h = w[s];
            assert(b.contains_key(h) && within(h, b[h], s));
            if b[h].order == c {
                assert(placed(h, b[h]));
                lemma_same_block(h, s, c);
                let x = s + p;
                self.lemma_whole(c, x);
                let h2 = w[x];
                assert(b.contains_key(h2) && within(h2, b[h2], x));
                assert(placed(h2, b[h2]));
                assert(h2 != s);
                self.lemma_apart(s, h2);
                assert(h2 == x);
                let o2 = b[h2].order;
                if o2 == c {
                    assert(b[s].free);
                    assert(free_block(b, x, c));
                    assert(!free_block(b, buddy(s, c), c));
                } else {
                    lemma_aligned_down(x, o, o2);
                }
            }
        }
    }

    /// A head keeps its order and takes the state `free`.
    proof fn lemma_retag(s: Self, t: Self, h: int, free: bool, tv: u8)
        requires
            s.wf(),
            s.blocks@.contains_key(h),
            free ==> (s.blocks@[h].order < BLOCK_ORDER ==> !free_block(
                s.blocks@,
                buddy(h, s.blocks@[h].order),
                s.blocks@[h].order,
            )),
            tv as int == tag(Block { order: s.blocks@[h].order, free }),
            t.tags@ == s.tags@.update(h, tv),
            t.blocks@ == s.blocks@.insert(h, Block { order: s.blocks@[h].order, free }),
            t.owner@ == s.owner@,
        ensures
            t.wf(),
            free ==> t.used() == s.used().remove(h),
            !free ==> t.used() == s.used().insert(h, s.blocks@[h].order),
    {
        let sb = s.blocks@;
        let st = s.tags@;
        let tb = t.blocks@;
        let tt = t.tags@;
        let o = sb[h].order;
        let n = BLOCK_PAGES as int;
        assert(placed(h, sb[h]));
        lemma_pages_pos(o);
        assert(st[h] as int == tag(sb[h]));
        assert forall|q: int| #[trigger] tb.contains_key(q) implies placed(q, tb[q]) && tt[q] as int
            == tag(tb[q]) by {
            if q != h {
                assert(placed(q, sb[q]));
                lemma_pages_pos(sb[q].order);
                assert(st[q] as int == tag(sb[q]));
            }
        }
        assert forall|r: int| 0 <= r < n && #[trigger] tt[r] != INNER implies tb.contains_key(r) by {
            if r != h {
                assert(st[r] == tt[r]);
            }
        }
        assert forall|q: int, r: int|
            #[trigger] tb.contains_key(q) && q < r < q + pages(tb[q].order) implies #[trigger] tt[r]
            == INNER by {
            assert(sb.contains_key(q));
            assert(placed(q, sb[q]));
            assert(st[r] == INNER);
        }
        assert forall|r: int| 0 <= r < n implies tb.contains_key(#[trigger] t.owner@[r]) && within(
            t.owner@[r],
            tb[t.owner@[r]],
            r,
        ) by {
            assert(sb.contains_key(s.owner@[r]) && within(s.owner@[r], sb[s.owner@[r]], r));
        }
        assert forall|q: int|
            #[trigger] tb.contains_key(q) && tb[q].free && tb[q].order
                < BLOCK_ORDER implies !free_block(tb, buddy(q, tb[q].order), tb[q].order) by {
            let oq = tb[q].order;
            assert(placed(q, tb[q]));
            lemma_buddy(q, oq);
            if q == h {
                lemma_buddy(h, o);
            } else {
                assert(sb[q] == tb[q]);
                if buddy(q, oq) == h && free && oq == o {
                    assert(free_block(sb, buddy(h, o), o));
                }
            }
        }
        if free {
            assert(t.used() =~= s.used().remove(h));
        } else {
            assert(t.used() =~= s.used().insert(h, o));
        }
    }

    /// A used block of order `o + 1` at `h` splits into a used lower half and a free upper half.
    proof fn lemma_split(s: Self, t: Self, h: int, o: nat, tv: u8, th: u8)
        requires
            s.wf(),
            o < BLOCK_ORDER,
            s.blocks@.contains_key(h),
            s.blocks@[h] == (Block { order: (o + 1) as nat, free: false }),
            tv as int == tag(Block { order: o, free: true }),
            th as int == tag(Block { order: o, free: false }),
            t.tags@ == s.tags@.update(h + pages(o), tv).update(h, th),
            t.blocks@ == s.blocks@.insert(h, Block { order: o, free: false }).insert(
                h + pages(o),
                Block { order: o, free: true },
            ),
            t.owner@ == reowned(s.owner@, h + pages(o), pages(o)),
        ensures
            t.wf(),
            t.used() == s.used().insert(h, o),
    {
        let sb = s.blocks@;
        let st = s.tags@;
        let sw = s.owner@;
        let tb = t.blocks@;
        let tt = t.tags@;
        let tw = t.owner@;
        let p = pages(o);
        let x = h + p;
        let n = BLOCK_PAGES as int;
        lemma_pages_pos(o);
        assert(pages((o + 1) as nat) == 2 * p);
        lemma_upper(h, o);
        assert(placed(h, sb[h]));
        assert(st[h] as int == tag(sb[h]));
        assert(st[x] == INNER);
        assert(!sb.contains_key(x)) by {
            if sb.contains_key(x) {
                assert(st[x] as int == tag(sb[x]));
            }
        }
        assert forall|q: int| #[trigger] tb.contains_key(q) implies placed(q, tb[q]) && tt[q] as int
            == tag(tb[q]) by {
            if q != x && q != h {
                assert(placed(q, sb[q]));
                lemma_pages_pos(sb[q].order);
                assert(st[q] as int == tag(sb[q]));
            }
        }
        assert forall|r: int| 0 <= r < n && #[trigger] tt[r] != INNER implies tb.contains_key(r) by {
            if r != x && r != h {
                assert(st[r] == tt[r]);
            }
        }
        assert forall|q: int, r: int|
            #[trigger] tb.contains_key(q) && q < r < q + pages(tb[q].order) implies #[trigger] tt[r]
            == INNER by {
            if q == h || q == x {
                assert(st[r] == INNER);
            } else {
                assert(sb.contains_key(q));
                assert(placed(q, sb[q]));
                assert(st[r] == INNER);
                s.lemma_apart(h, q);
            }
        }
        assert forall|r: int| 0 <= r < n implies tb.contains_key(#[trigger] tw[r]) && within(
            tw[r],
            tb[tw[r]],
            r,
        ) by {
            if !(x <= r < x + p) {
                assert(sb.contains_key(sw[r]) && within(sw[r], sb[sw[r]], r));
            }
        }
        assert forall|q: int|
            #[trigger] tb.contains_key(q) && tb[q].free && tb[q].order
                < BLOCK_ORDER implies !free_block(tb, buddy(q, tb[q].order), tb[q].order) by {
            if q != x {
                let oq = tb[q].order;
                assert(sb[q] == tb[q]);
                assert(placed(q, sb[q]));
                lemma_buddy(q, oq);
            }
        }
        assert(t.used() =~= s.used().insert(h, o));
    }

    /// A used block of order `o` at `h` and its free buddy become one used block of order `o + 1`
    /// at `lo`, the lower of the two.
    proof fn lemma_merge(s: Self, t: Self, h: int, o: nat, lo: int, hi: int, tv: u8)
        requires
            s.wf(),
            o < BLOCK_ORDER,
            s.blocks@.contains_key(h),
            s.blocks@[h] == (Block { order: o, free: false }),
            free_block(s.blocks@, buddy(h, o), o),
            lo == (if buddy(h, o) < h {
                buddy(h, o)
            } else {
                h
            }),
            hi == (if buddy(h, o) < h {
                h
            } else {
                buddy(h, o)
            }),
            tv as int == tag(Block { order: (o + 1) as nat, free: false }),
            t.tags@ == s.tags@.update(hi, INNER).update(lo, tv),
            t.blocks@ == s.blocks@.remove(hi).insert(
                lo,
                Block { order: (o + 1) as nat, free: false },
            ),
            t.owner@ == reowned(s.owner@, lo, pages((o + 1) as nat)),
        ensures
            t.wf(),
            t.used() == s.used().remove(h).insert(lo, (o + 1) as nat),
    {
        let sb = s.blocks@;
        let st = s.tags@;
        let sw = s.owner@;
        let tb = t.blocks@;
        let tt = t.tags@;
        let tw = t.owner@;
        let b = buddy(h, o);
        let p = pages(o);
        let n = BLOCK_PAGES as int;
        lemma_pages_pos(o);
        assert(pages((o + 1) as nat) == 2 * p);
        assert(placed(h, sb[h]));
        assert(placed(b, sb[b]));
        lemma_buddy(h, o);
        assert(lo % (2 * p) == 0);
        assert(hi == lo + p);
        assert(st[h] as int == tag(sb[h]));
        assert(st[b] as int == tag(sb[b]));
        assert forall|q: int| #[trigger] tb.contains_key(q) implies placed(q, tb[q]) && tt[q] as int
            == tag(tb[q]) by {
            if q != lo {
                assert(placed(q, sb[q]));
                lemma_pages_pos(sb[q].order);
                assert(st[q] as int == tag(sb[q]));
            }
        }
        assert forall|r: int| 0 <= r < n && #[trigger] tt[r] != INNER implies tb.contains_key(r) by {
            if r != lo && r != hi {
                assert(st[r] == tt[r]);
            }
        }
        assert forall|q: int, r: int|
            #[trigger] tb.contains_key(q) && q < r < q + pages(tb[q].order) implies #[trigger] tt[r]
            == INNER by {
            if q == lo {
                if r < hi {
                    assert(st[r] == INNER);
                } else if r > hi {
                    assert(st[r] == INNER);
                }
            } else {
                assert(sb.contains_key(q));
                assert(placed(q, sb[q]));
                assert(st[r] == INNER);
            }
        }
        assert forall|r: int| 0 <= r < n implies tb.contains_key(#[trigger] tw[r]) && within(
            tw[r],
            tb[tw[r]],
            r,
        ) by {
            if !(lo <= r < lo + 2 * p) {
                assert(sb.contains_key(sw[r]) && within(sw[r], sb[sw[r]], r));
            }
        }
        assert forall|q: int|
            #[trigger] tb.contains_key(q) && tb[q].free && tb[q].order
                < BLOCK_ORDER implies !free_block(tb, buddy(q, tb[q].order), tb[q].order) by {
            assert(sb[q] == tb[q]);
        }
        assert(t.used() =~= s.used().remove(h).insert(lo, (o + 1) as nat));
    }

    /// One free block of order BLOCK_ORDER.
    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            r.blocks() == initial(),
    {
        let mut tags = [INNER;BLOCK_PAGES];
        tags[0] = (BLOCK_ORDER + 1) as u8 + FREE;
        let r = BlockBuddy {
            tags,
            blocks: Ghost(initial()),
            owner: Ghost(
                Map::new(vstd::set_lib::set_int_range(0, BLOCK_PAGES as int), |p: int| 0int),
            ),
        };
        proof {
            lemma_block_pages();
        }
        r
    }

    /// The head of a free block of the smallest order at or above `k`, if any.
    fn best_fit(&self, k: usize) -> (r: Option<usize>)
        requires
            self.wf(),
            k <= BLOCK_ORDER,
        ensures
            match r {
                None => !self.fits(k as nat),
                Some(h) => {
                    &&& self.blocks().contains_key(h as int)
                    &&& self.blocks()[h as int].free
                    &&& self.blocks()[h as int].order >= k
                    &&& forall|q: int|
                        #[trigger] self.blocks().contains_key(q) && self.blocks()[q].free
                            && self.blocks()[q].order >= k ==> self.blocks()[q].order
                            >= self.blocks()[h as int].order
                },
            },
    {
        let mut best: Option<usize> = None;
        let mut best_order: usize = BLOCK_ORDER + 1;
        let mut p: usize = 0;
        while p < BLOCK_PAGES
            invariant
                self.wf(),
                k <= BLOCK_ORDER,
                p <= BLOCK_PAGES,
                match best {
                    None => best_order == BLOCK_ORDER + 1,
                    Some(h) => {
                        &&& self.blocks@.contains_key(h as int)
                        &&& self.blocks@[h as int] == (Block {
                            order: best_order as nat,
                            free: true,
                        })
                        &&& best_order >= k
                    },
                },
                forall|q: int|
                    0 <= q < p && #[trigger] self.blocks@.contains_key(q) && self.blocks@[q].free
                        && self.blocks@[q].order >= k ==> best_order <= self.blocks@[q].order,
            decreases BLOCK_PAGES - p,
        {
            let t = self.tags[p];
            proof {
                if t != INNER {
                    assert(self.blocks@.contains_key(p as int));
                }
                if self.blocks@.contains_key(p as int) {
                    assert(t as int == tag(self.blocks@[p as int]));
                    assert(placed(p as int, self.blocks@[p as int]));
                }
            }
            if t > FREE {
                let o = (t - FREE - 1) as usize;
                if o >= k && o < best_order {
                    best = Some(p);
                    best_order = o;
                }
            }
            p = p + 1;
        }
        proof {
            assert forall|q: int| #[trigger] self.blocks@.contains_key(q) implies 0 <= q
                < BLOCK_PAGES by {
                assert(placed(q, self.blocks@[q]));
                lemma_pages_pos(self.blocks@[q].order);
            }
            if best is None && self.fits(k as nat) {
                let q = choose|q: int|
                    #[trigger] self.blocks().contains_key(q) && self.blocks()[q].free
                        && self.blocks()[q].order >= k;
                assert(placed(q, self.blocks@[q]));
                assert(best_order <= self.blocks@[q].order);
            }
        }
        best
    }

    /// The smallest order at or above `k` that a free block has, if any.
    pub fn fit_order(&self, k: usize) -> (r: Option<usize>)
        requires
            self.wf(),
            k <= BLOCK_ORDER,
        ensures
            match r {
                None => !self.fits(k as nat),
                Some(o) => {
                    &&& k <= o <= BLOCK_ORDER
                    &&& exists|h: int| #[trigger]
                        self.blocks().contains_key(h) && self.blocks()[h] == (Block {
                            order: o as nat,
                            free: true,
                        })
                    &&& forall|q: int|
                        #[trigger] self.blocks().contains_key(q) && self.blocks()[q].free
                            && self.blocks()[q].order >= k ==> self.blocks()[q].order >= o
                },
            },
    {
        match self.best_fit(k) {
            None => None,
            Some(h) => {
                proof {
                    assert(placed(h as int, self.blocks@[h as int]));
                    lemma_pages_pos(self.blocks@[h as int].order);
                    assert(self.tags@[h as int] as int == tag(self.blocks@[h as int]));
                }
                Some((self.tags[h] - FREE - 1) as usize)
            },
        }
    }

    /// Cuts a run of order `k` from the free block of the smallest order at or above `k`, and
    /// returns its first page; or refuses, and changes nothing, when no free block has order `k` or
    /// more.
    pub fn alloc(&mut self, k: usize) -> (r: Option<usize>)
        requires
            old(self).wf(),
            k <= BLOCK_ORDER,
        ensures
            final(self).wf(),
            match r {
                None => !old(self).fits(k as nat) && *final(self) == *old(self),
                Some(p) => {
                    &&& placed(p as int, Block { order: k as nat, free: false })
                    &&& old(self).blocks().contains_key(p as int)
                    &&& old(self).blocks()[p as int].free
                    &&& old(self).blocks()[p as int].order >= k
                    &&& forall|q: int|
                        #[trigger] old(self).blocks().contains_key(q) && old(self).blocks()[q].free
                            && old(self).blocks()[q].order >= k ==> old(self).blocks()[q].order
                            >= old(self).blocks()[p as int].order
                    &&& final(self).used() == old(self).used().insert(p as int, k as nat)
                },
            },
    {
        let h = match self.best_fit(k) {
            None => return None,
            Some(h) => h,
        };
        proof {
            assert(placed(h as int, self.blocks@[h as int]));
            lemma_pages_pos(self.blocks@[h as int].order);
            assert(self.tags@[h as int] as int == tag(self.blocks@[h as int]));
        }
        let mut o = (self.tags[h] - FREE - 1) as usize;
        let ghost s0 = *self;
        let tu = (o + 1) as u8;
        self.tags[h] = tu;
        self.blocks = Ghost(self.blocks@.insert(h as int, Block { order: o as nat, free: false }));
        proof {
            Self::lemma_retag(s0, *self, h as int, false, tu);
        }
        let mut size = order_pages(o);
        while o > k
            invariant
                self.wf(),
                k <= o <= BLOCK_ORDER,
                size as int == pages(o as nat),
                self.blocks@.contains_key(h as int),
                self.blocks@[h as int] == (Block { order: o as nat, free: false }),
                self.used() == s0.used().insert(h as int, o as nat),
            decreases o,
        {
            let ghost s1 = *self;
            proof {
                assert(placed(h as int, self.blocks@[h as int]));
                lemma_pages_pos((o - 1) as nat);
                assert(pages(o as nat) == 2 * pages((o - 1) as nat));
            }
            o = o - 1;
            size = size / 2;
            let x = h + size;
            let tv = (o + 1) as u8 + FREE;
            let th = (o + 1) as u8;
            self.tags[x] = tv;
            self.tags[h] = th;
            self.blocks = Ghost(
                self.blocks@.insert(h as int, Block { order: o as nat, free: false }).insert(
                    x as int,
                    Block { order: o as nat, free: true },
                ),
            );
            self.owner = Ghost(reowned(self.owner@, x as int, size as int));
            proof {
                Self::lemma_split(s1, *self, h as int, o as nat, tv, th);
                assert(self.used() =~= s0.used().insert(h as int, o as nat));
            }
        }
        proof {
            assert(placed(h as int, self.blocks@[h as int]));
        }
        Some(h)
    }

    /// Takes back the run at `p`, coalescing it with its buddy while the buddy is free.
    pub fn free(&mut self, p: usize)
        requires
            old(self).wf(),
            old(self).used().contains_key(p as int),
        ensures
            final(self).wf(),
            final(self).used() == old(self).used().remove(p as int),
    {
        let ghost u0 = self.used();
        proof {
            assert(placed(p as int, self.blocks@[p as int]));
            lemma_pages_pos(self.blocks@[p as int].order);
            assert(self.tags@[p as int] as int == tag(self.blocks@[p as int]));
        }
        let mut o = (self.tags[p] - 1) as usize;
        let mut h = p;
        let mut size = order_pages(o);
        let mut done = false;
        while !done && o < BLOCK_ORDER
            invariant
                self.wf(),
                o <= BLOCK_ORDER,
                size as int == pages(o as nat),
                self.blocks@.contains_key(h as int),
                self.blocks@[h as int] == (Block { order: o as nat, free: false }),
                self.used().remove(h as int) == u0.remove(p as int),
                done ==> o < BLOCK_ORDER && !free_block(
                    self.blocks@,
                    buddy(h as int, o as nat),
                    o as nat,
                ),
            decreases 2 * (BLOCK_ORDER - o) + (if done {
                0int
            } else {
                1int
            }),
        {
            proof {
                lemma_pages_pos(o as nat);
                lemma_pages((o + 1) as nat, BLOCK_ORDER as nat);
                lemma_block_pages();
                assert(pages((o + 1) as nat) == 2 * pages(o as nat));
                assert(placed(h as int, self.blocks@[h as int]));
                lemma_buddy(h as int, o as nat);
                if h as int % pages((o + 1) as nat) == 0 {
                    lemma_fit(h as int, (o + 1) as nat);
                }
            }
            let b = if h % (2 * size) == 0 {
                h + size
            } else {
                h - size
            };
            let bt = self.tags[b];
            if bt != (o + 1) as u8 + FREE {
                proof {
                    if self.blocks@.contains_key(b as int) {
                        assert(self.tags@[b as int] as int == tag(self.blocks@[b as int]));
                    }
                }
                done = true;
            } else {
                proof {
                    assert(self.blocks@.contains_key(b as int));
                    assert(self.tags@[b as int] as int == tag(self.blocks@[b as int]));
                    assert(placed(b as int, self.blocks@[b as int]));
                }
                let ghost s1 = *self;
                let lo = if b < h {
                    b
                } else {
                    h
                };
                let hi = if b < h {
                    h
                } else {
                    b
                };
                let tv = (o + 2) as u8;
                self.tags[hi] = INNER;
                self.tags[lo] = tv;
                self.blocks = Ghost(
                    self.blocks@.remove(hi as int).insert(
                        lo as int,
                        Block { order: (o + 1) as nat, free: false },
                    ),
                );
                self.owner = Ghost(reowned(self.owner@, lo as int, 2 * size as int));
                proof {
                    Self::lemma_merge(s1, *self, h as int, o as nat, lo as int, hi as int, tv);
                    assert(self.used().remove(lo as int) =~= u0.remove(p as int));
                }
                h = lo;
                o = o + 1;
                size = size * 2;
            }
        }
        let ghost s2 = *self;
        proof {
            assert(placed(h as int, self.blocks@[h as int]));
            lemma_pages_pos(o as nat);
        }
        let tv = (o + 1) as u8 + FREE;
        self.tags[h] = tv;
        self.blocks = Ghost(self.blocks@.insert(h as int, Block { order: o as nat, free: true }));
        proof {
            Self::lemma_retag(s2, *self, h as int, true, tv);
            assert(self.used() =~= u0.remove(p as int));
        }
    }

    /// Whether no run is allocated, which is when the view is the initial one (`lemma_idle`).
    pub fn is_idle(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == (self.used().dom() == Set::<int>::empty()),
    {
        let mut p: usize = 0;
        while p < BLOCK_PAGES
            invariant
                self.wf(),
                p <= BLOCK_PAGES,
                forall|q: int| 0 <= q < p ==> !(#[trigger] self.used().dom().contains(q)),
            decreases BLOCK_PAGES - p,
        {
            let t = self.tags[p];
            proof {
                if self.blocks@.contains_key(p as int) {
                    assert(t as int == tag(self.blocks@[p as int]));
                }
                if t != INNER {
                    assert(self.blocks@.contains_key(p as int));
                }
            }
            if t != INNER && t <= FREE {
                proof {
                    assert(self.used().dom().contains(p as int));
                }
                return false;
            }
            p = p + 1;
        }
        proof {
            assert forall|q: int| !self.used().dom().contains(q) by {
                if self.used().dom().contains(q) {
                    assert(placed(q, self.blocks@[q]));
                    lemma_pages_pos(self.blocks@[q].order);
                }
            }
            assert(self.used().dom() =~= Set::<int>::empty());
        }
        true
    }
}

} // verus!
