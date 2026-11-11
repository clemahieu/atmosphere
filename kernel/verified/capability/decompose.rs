// SPDX-License-Identifier: MIT

//! A run of pages as the maximal aligned blocks of at most a given order: from the run's first page,
//! the largest order up to the cap its page is aligned to and the run holds, then the same from the
//! page after that block. Boot hands the root one untyped per block of free memory, of any order, and
//! one frame capability per block of dom0's image, of order at most 9 so that each lies in one 2M
//! region. See design/root-process-at-boot/ and design/capability-names-a-block/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::capability::boot::*;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::define::*;
use crate::capability::steps::Steps;

/// The largest order at most m that page start is aligned to and n pages hold, 0 when none above 0 is.
pub open spec fn order_below(start: nat, n: nat, m: nat) -> nat
    decreases m,
{
    if m == 0 {
        0
    } else if start % pow2(m) == 0 && pow2(m) <= n {
        m
    } else {
        order_below(start, n, (m - 1) as nat)
    }
}

/// The blocks of order at most cap the run of n pages at page start decomposes into, in address order,
/// each as its first page and its order.
pub open spec fn run_blocks(start: nat, n: nat, cap: nat) -> Seq<(nat, nat)>
    decreases n,
    via run_blocks_decreases
{
    if n == 0 {
        Seq::empty()
    } else {
        let o = order_below(start, n, cap);
        seq![(start, o)] + run_blocks(start + pow2(o), (n - pow2(o)) as nat, cap)
    }
}

#[via_fn]
proof fn run_blocks_decreases(start: nat, n: nat, cap: nat) {
    if n != 0 {
        lemma_order_below(start, n, cap);
        lemma_pow2_pos(order_below(start, n, cap));
    }
}

/// Page x is one of the pages of block b, given as its first page and its order.
pub open spec fn in_page_block(b: (nat, nat), x: nat) -> bool {
    b.0 <= x < b.0 + pow2(b.1)
}

/// Page x is one of the n pages at page start.
pub open spec fn in_run(start: nat, n: nat, x: nat) -> bool {
    start <= x < start + n
}

/// The untyped capability boot hands the root for block b, given as its first page and its order.
pub open spec fn page_block_payload(b: (nat, nat)) -> Payload {
    untyped_payload((b.0 * PAGE_SZ) as usize, b.1 as u8)
}

/// The first block of order at most cap of the run of n pages at page start: its order and its size in
/// pages.
pub fn first_block(start: usize, n: usize, cap: u8, Tracked(steps): Tracked<&mut Steps>) -> (ret: (u8, usize))
    requires
        0 < n,
        start + n <= NUM_PAGES,
        cap <= MAX_ORDER,
    ensures
        final(steps).count <= old(steps).count + MAX_ORDER,
        ret.0 as nat == order_below(start as nat, n as nat, cap as nat),
        ret.1 as nat == pow2(ret.0 as nat),
        ret.1 <= n,
{
    let mut o: u8 = MAX_ORDER;
    let ghost steps0 = steps.count;
    let mut size: usize = 0x10_0000_0000; // not a page size: 2^MAX_ORDER, a count of pages
    proof {
        lemma2_to64_rest();
    }
    while o > cap
        invariant
            cap <= o <= MAX_ORDER,
            size as nat == pow2(o as nat),
            steps.count == steps0 + MAX_ORDER - o,
        decreases o,
    {
        proof {
            lemma_pow2_unfold(o as nat);
            steps.step();
        }
        o = o - 1;
        size = size / 2;
    }
    proof {
        lemma_pow2_pos(o as nat);
    }
    while o > 0 && !(start % size == 0 && size <= n)
        invariant
            o <= MAX_ORDER,
            size as nat == pow2(o as nat),
            size > 0,
            steps.count == steps0 + MAX_ORDER - o,
            order_below(start as nat, n as nat, o as nat) == order_below(start as nat, n as nat, cap as nat),
        decreases o,
    {
        proof {
            lemma_pow2_unfold(o as nat);
            lemma_pow2_pos((o - 1) as nat);
            steps.step();
        }
        o = o - 1;
        size = size / 2;
    }
    proof {
        lemma2_to64();
        lemma_order_below(start as nat, n as nat, cap as nat);
    }
    (o, size)
}

/// The order order_below picks is at most m, page start is aligned to it and n pages hold it, and no
/// larger order up to m is both.
pub proof fn lemma_order_below(start: nat, n: nat, m: nat)
    requires
        n > 0,
    ensures
        order_below(start, n, m) <= m,
        start % pow2(order_below(start, n, m)) == 0,
        pow2(order_below(start, n, m)) <= n,
        forall|k: nat|
            order_below(start, n, m) < k <= m ==> !(start % #[trigger] pow2(k) == 0 && pow2(k) <= n),
    decreases m,
{
    if m == 0 {
        lemma2_to64();
    } else if !(start % pow2(m) == 0 && pow2(m) <= n) {
        lemma_order_below(start, n, (m - 1) as nat);
    }
}

/// A page aligned to 2^b is aligned to 2^a for every a up to b.
proof fn lemma_aligned_below(x: nat, a: nat, b: nat)
    requires
        a <= b,
        x % pow2(b) == 0,
    ensures
        x % pow2(a) == 0,
{
    let r = (b - a) as nat;
    lemma_pow2_adds(a, r);
    assert(a + r == b);
    lemma_pow2_pos(a);
    lemma_pow2_pos(r);
    lemma_mod_mod(x as int, pow2(a) as int, pow2(r) as int);
    lemma_small_mod(0, pow2(a));
}

/// The page after a block of order o is aligned to o when the block's first page is, and to o + 1 when
/// the first page is aligned to o but not to o + 1.
proof fn lemma_aligned_after(x: nat, o: nat)
    requires
        x % pow2(o) == 0,
    ensures
        (x + pow2(o)) % pow2(o) == 0,
        x % pow2(o + 1) != 0 ==> (x + pow2(o)) % pow2(o + 1) == 0,
{
    let p = pow2(o) as int;
    lemma_pow2_pos(o);
    lemma_mod_add_multiples_vanish(x as int, p);
    if x % pow2(o + 1) != 0 {
        lemma_pow2_unfold(o + 1);
        assert(pow2(o + 1) as int == p * 2);
        lemma_mod_mod(x as int, p, 2);
        let r = x as int % (p * 2);
        lemma_fundamental_div_mod(r, p);
        lemma_small_mod(0, p as nat);
        assert(r % p == 0);
        let q = r / p;
        assert(r == p * q);
        assert(0 <= r < p * 2) by {
            lemma_mod_bound(x as int, p * 2);
        }
        assert(q == 1) by (nonlinear_arith)
            requires
                r == p * q,
                0 < r,
                r < p * 2,
                p > 0,
        ;
        lemma_fundamental_div_mod(x as int, p * 2);
        let d = x as int / (p * 2);
        assert(x + p == (p * 2) * (d + 1)) by (nonlinear_arith)
            requires
                x == (p * 2) * d + r,
                r == p,
        ;
        lemma_mod_multiples_basic(d + 1, p * 2);
        assert((d + 1) * (p * 2) == (p * 2) * (d + 1)) by (nonlinear_arith);
    }
}

/// The step from one block to the rest of the run: the first block is the run's first page at its
/// order, at most the cap, which the run holds, and the rest starts aligned to that order.
proof fn lemma_run_step(start: nat, n: nat, cap: nat)
    requires
        n > 0,
    ensures
        order_below(start, n, cap) <= cap,
        start % pow2(order_below(start, n, cap)) == 0,
        0 < pow2(order_below(start, n, cap)) <= n,
        (start + pow2(order_below(start, n, cap))) % pow2(order_below(start, n, cap)) == 0,
        run_blocks(start, n, cap) == seq![(start, order_below(start, n, cap))] + run_blocks(
            start + pow2(order_below(start, n, cap)),
            (n - pow2(order_below(start, n, cap))) as nat,
            cap,
        ),
{
    lemma_order_below(start, n, cap);
    lemma_pow2_pos(order_below(start, n, cap));
    lemma_aligned_after(start, order_below(start, n, cap));
}

/// A run that starts aligned to 2^k and is shorter than 2^k has at most k blocks: each is limited by
/// the pages left, so each is smaller than the one before.
proof fn lemma_run_blocks_below(start: nat, n: nat, k: nat)
    requires
        k <= MAX_ORDER,
        start % pow2(k) == 0,
        n < pow2(k),
    ensures
        run_blocks(start, n, MAX_ORDER as nat).len() <= k,
    decreases n,
{
    if n > 0 {
        let o = order_below(start, n, MAX_ORDER as nat);
        lemma_run_step(start, n, MAX_ORDER as nat);
        lemma_order_below(start, n, MAX_ORDER as nat);
        if o >= k {
            if o > k {
                lemma_pow2_strictly_increases(k, o);
            }
            assert(false);
        }
        lemma_aligned_below(start, o + 1, k);
        assert(!(start % pow2(o + 1) == 0 && pow2(o + 1) <= n));
        lemma_pow2_unfold(o + 1);
        lemma_run_blocks_below(start + pow2(o), (n - pow2(o)) as nat, o);
    }
}

/// A run shorter than 2^MAX_ORDER that starts aligned to 2^j has at most 2 * MAX_ORDER + 1 - j
/// blocks: while a block is limited by its first page's alignment the next starts aligned to more,
/// and once one is limited by the pages left the rest are under lemma_run_blocks_below.
proof fn lemma_run_blocks_count(start: nat, n: nat, j: nat)
    requires
        j <= MAX_ORDER,
        start % pow2(j) == 0,
        n < pow2(MAX_ORDER as nat),
    ensures
        run_blocks(start, n, MAX_ORDER as nat).len() <= 2 * MAX_ORDER + 1 - j,
    decreases n,
{
    if n > 0 {
        let o = order_below(start, n, MAX_ORDER as nat);
        lemma_run_step(start, n, MAX_ORDER as nat);
        lemma_order_below(start, n, MAX_ORDER as nat);
        if o == MAX_ORDER {
            assert(false);
        }
        lemma_pow2_unfold(o + 1);
        if pow2(o + 1) > n {
            lemma_run_blocks_below(start + pow2(o), (n - pow2(o)) as nat, o);
        } else {
            assert(start % pow2(o + 1) != 0);
            if j > o {
                lemma_aligned_below(start, o + 1, j);
            }
            lemma_aligned_after(start, o);
            lemma_run_blocks_count(start + pow2(o), (n - pow2(o)) as nat, o + 1);
        }
    }
}

/// The blocks of a run lie inside it, in address order, each aligned to its order, at most the cap, and
/// cover it.
proof fn lemma_run_blocks_place(start: nat, n: nat, cap: nat)
    ensures
        forall|i: int|
            0 <= i < run_blocks(start, n, cap).len() ==> {
                let b = #[trigger] run_blocks(start, n, cap)[i];
                &&& b.1 <= cap
                &&& b.0 % pow2(b.1) == 0
                &&& start <= b.0
                &&& b.0 + pow2(b.1) <= start + n
            },
        forall|i: int, j: int|
            0 <= i < j < run_blocks(start, n, cap).len() ==> #[trigger] run_blocks(start, n, cap)[i].0 + pow2(
                run_blocks(start, n, cap)[i].1,
            ) <= #[trigger] run_blocks(start, n, cap)[j].0,
        forall|x: nat|
            #[trigger] in_run(start, n, x) ==> exists|i: int|
                0 <= i < run_blocks(start, n, cap).len() && #[trigger] in_page_block(run_blocks(start, n, cap)[i], x),
    decreases n,
{
    if n > 0 {
        let o = order_below(start, n, cap);
        let next = start + pow2(o);
        let left = (n - pow2(o)) as nat;
        lemma_run_step(start, n, cap);
        lemma_run_blocks_place(next, left, cap);
        let bs = run_blocks(start, n, cap);
        let rs = run_blocks(next, left, cap);
        assert(bs.len() == rs.len() + 1);
        assert(bs[0] == (start, o));
        assert forall|i: int| 0 < i < bs.len() implies bs[i] == rs[i - 1] by {}
        assert forall|i: int| 0 <= i < bs.len() implies {
            let b = #[trigger] bs[i];
            &&& b.1 <= cap
            &&& b.0 % pow2(b.1) == 0
            &&& start <= b.0
            &&& b.0 + pow2(b.1) <= start + n
        } by {
            if i > 0 {
                assert(bs[i] == rs[i - 1]);
            }
        }
        assert forall|i: int, j: int| 0 <= i < j < bs.len() implies #[trigger] bs[i].0 + pow2(bs[i].1)
            <= #[trigger] bs[j].0 by {
            assert(bs[j] == rs[j - 1]);
            if i > 0 {
                assert(bs[i] == rs[i - 1]);
            }
        }
        assert forall|x: nat| #[trigger] in_run(start, n, x) implies exists|i: int|
            0 <= i < bs.len() && #[trigger] in_page_block(bs[i], x) by {
            if x < next {
                assert(in_page_block(bs[0], x));
            } else {
                assert(in_run(next, left, x));
                let i = choose|i: int| 0 <= i < rs.len() && #[trigger] in_page_block(rs[i], x);
                assert(bs[i + 1] == rs[i]);
                assert(in_page_block(bs[i + 1], x));
            }
        }
    }
}

/// A block inside NUM_PAGES aligned to its order is one an untyped capability can name.
proof fn lemma_page_block_wf(b: (nat, nat))
    requires
        b.1 <= MAX_ORDER,
        b.0 % pow2(b.1) == 0,
        b.0 + pow2(b.1) <= NUM_PAGES,
    ensures
        payload_wf(page_block_payload(b)),
{
    let p = pow2(b.1) as int;
    lemma_pow2_pos(b.1);
    lemma_fundamental_div_mod(b.0 as int, p);
    let q = b.0 as int / p;
    assert(b.0 * PAGE_SZ == q * (p * PAGE_SZ)) by (nonlinear_arith)
        requires
            b.0 == p * q + 0,
    ;
    lemma_mod_multiples_basic(q, p * PAGE_SZ as int);
    assert(b.0 * PAGE_SZ + p * PAGE_SZ <= NUM_PAGES * PAGE_SZ) by (nonlinear_arith)
        requires
            b.0 + p <= NUM_PAGES,
    ;
    assert((b.1 as u8) as nat == b.1);
    assert(block_bytes(b.1 as u8) == p * PAGE_SZ);
}

/// The decomposition of a run inside NUM_PAGES under a cap: its blocks are each of order at most the
/// cap, aligned to its size and named by an untyped capability that is payload_wf, pairwise disjoint,
/// and together exactly the run's pages; uncapped, at most 2 * (MAX_ORDER + 1).
pub proof fn lemma_run_blocks(start: nat, n: nat, cap: nat)
    requires
        start + n <= NUM_PAGES,
        cap <= MAX_ORDER,
    ensures
        cap == MAX_ORDER ==> run_blocks(start, n, cap).len() <= 2 * (MAX_ORDER + 1),
        forall|i: int|
            0 <= i < run_blocks(start, n, cap).len() ==> {
                let b = #[trigger] run_blocks(start, n, cap)[i];
                &&& b.1 <= cap
                &&& b.0 % pow2(b.1) == 0
                &&& payload_wf(page_block_payload(b))
            },
        forall|i: int, j: int, x: nat|
            0 <= i < run_blocks(start, n, cap).len() && 0 <= j < run_blocks(start, n, cap).len() && i != j
                ==> !(#[trigger] in_page_block(run_blocks(start, n, cap)[i], x) && #[trigger] in_page_block(
                run_blocks(start, n, cap)[j],
                x,
            )),
        forall|x: nat|
            #[trigger] in_run(start, n, x) <==> exists|i: int|
                0 <= i < run_blocks(start, n, cap).len() && #[trigger] in_page_block(run_blocks(start, n, cap)[i], x),
{
    let bs = run_blocks(start, n, cap);
    lemma_run_blocks_place(start, n, cap);
    lemma2_to64();
    lemma2_to64_rest();
    if cap == MAX_ORDER {
        lemma_run_blocks_count(start, n, 0);
    }
    assert forall|i: int| 0 <= i < bs.len() implies {
        let b = #[trigger] bs[i];
        &&& b.1 <= cap
        &&& b.0 % pow2(b.1) == 0
        &&& payload_wf(page_block_payload(b))
    } by {
        lemma_page_block_wf(bs[i]);
    }
    assert forall|i: int, j: int, x: nat|
        0 <= i < bs.len() && 0 <= j < bs.len() && i != j implies !(#[trigger] in_page_block(bs[i], x)
        && #[trigger] in_page_block(bs[j], x)) by {
        if i < j {
            assert(bs[i].0 + pow2(bs[i].1) <= bs[j].0);
        } else {
            assert(bs[j].0 + pow2(bs[j].1) <= bs[i].0);
        }
    }
    assert forall|x: nat| (exists|i: int| 0 <= i < bs.len() && #[trigger] in_page_block(bs[i], x)) implies
        #[trigger] in_run(start, n, x) by {
        let i = choose|i: int| 0 <= i < bs.len() && #[trigger] in_page_block(bs[i], x);
        assert(start <= bs[i].0 && bs[i].0 + pow2(bs[i].1) <= start + n);
    }
}

} // verus!
