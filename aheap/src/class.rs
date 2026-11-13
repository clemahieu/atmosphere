// SPDX-License-Identifier: MIT
//! The size classes: the slot size of each class, and the order of the page run each of its slabs is
//! cut from. design/heap-size-classes/.
//!
//! The first LINEAR_CLASSES classes are the first multiples of SLOT_MIN. Past them each doubling of
//! the slot size is cut into STEPS classes, an even step apart, up to the page, which is the last
//! class: CLASSES classes, all multiples of SLOT_MIN. A class's slabs are cut from a run of the
//! smallest order whose tail after the last slot is at most a TAIL_SHARE-th of the run, as long as
//! the run holds no more slots than a slab's bitmap has bits for.
//!
//! - `size(c)` is the slot size of class `c`, and `order(c)` the order of its slabs' runs.
//! - `class_of(n)` is the smallest class whose slots hold `n` bytes, for `n` up to the page.
//! - `lemma_class(c)` states what a slab of class `c` needs: its slot size is a multiple of
//!   SLOT_MIN, between SLOT_MIN and the page, its run holds at least one slot and at most MAP_SLOTS,
//!   and the classes grow with `c`.
#[cfg(verus_keep_ghost)]
use vstd::compute::*;
use vstd::prelude::*;

use crate::arch::*;
use crate::buddy::*;
use crate::slab::*;

verus! {

/// The classes that are the first multiples of SLOT_MIN.
pub const LINEAR_CLASSES: usize = 8;

/// The classes each doubling of the slot size past the linear classes is cut into.
pub const STEPS: usize = 4;

/// A slab's run wastes at most this share of itself after its last slot.
pub const TAIL_SHARE: usize = 8;

/// The slot size of the first class of doubling `g` past the linear classes, less one step: the
/// slot size that doubling starts above.
pub open spec fn group_base(g: nat) -> nat
    decreases g,
{
    if g == 0 {
        (LINEAR_CLASSES * SLOT_MIN) as nat
    } else {
        2 * group_base((g - 1) as nat)
    }
}

/// The slot size of class `c`.
pub open spec fn class_size(c: nat) -> nat {
    if c < LINEAR_CLASSES {
        (c + 1) * SLOT_MIN as nat
    } else {
        let d = (c - LINEAR_CLASSES) as nat;
        let b = group_base(d / STEPS as nat);
        b + (d % STEPS as nat + 1) * (b / STEPS as nat)
    }
}

/// The bytes of a run of order `k`.
pub open spec fn run_bytes(k: nat) -> int {
    pages(k) * PAGE_BYTES as int
}

/// A run of order `k` cut into slots of `s` bytes leaves at most a TAIL_SHARE-th of itself after its
/// last slot.
pub open spec fn snug(s: nat, k: nat) -> bool {
    (run_bytes(k) % s as int) * TAIL_SHARE as int <= run_bytes(k)
}

/// The order, from `k` up, of the run slots of `s` bytes are cut from: the first that is snug, that
/// is BLOCK_ORDER, or whose next order would hold more than MAP_SLOTS slots.
pub open spec fn order_from(s: nat, k: nat) -> nat
    decreases BLOCK_ORDER - k,
{
    if k >= BLOCK_ORDER || snug(s, k) || run_bytes(k + 1) / s as int > MAP_SLOTS as int {
        k
    } else {
        order_from(s, k + 1)
    }
}

/// The order of the runs class `c`'s slabs are cut from.
pub open spec fn slab_order(c: nat) -> nat {
    order_from(class_size(c), 0)
}

/// What a slab of class `c` needs of its slot size and its run, and that the next class is larger.
pub open spec fn class_ok(c: nat) -> bool {
    let s = class_size(c);
    let k = slab_order(c);
    &&& SLOT_MIN <= s <= PAGE_BYTES
    &&& s % SLOT_MIN as nat == 0
    &&& k <= BLOCK_ORDER
    &&& s <= run_bytes(k)
    &&& run_bytes(k) / s as int <= MAP_SLOTS as int
    &&& snug(s, k)
    &&& c + 1 < CLASSES ==> s < class_size(c + 1)
}

/// The last doubling past the linear classes that holds a class.
pub open spec fn last_group() -> nat {
    ((CLASSES - LINEAR_CLASSES) as int / STEPS as int) as nat
}

/// The first slot size of each doubling past the linear classes lies within the page.
pub open spec fn group_ok(g: nat) -> bool {
    group_base(g) <= PAGE_BYTES
}

/// Every class is as a slab needs, the first is SLOT_MIN and the last the page, and no doubling the
/// classes reach starts past the page.
proof fn lemma_classes()
    ensures
        class_size(0) == SLOT_MIN,
        class_size((CLASSES - 1) as nat) == PAGE_BYTES,
        forall|c: nat| c < CLASSES ==> #[trigger] class_ok(c),
        forall|g: nat| g <= last_group() ==> #[trigger] group_ok(g),
{
    assert(class_size(0) == SLOT_MIN) by (compute_only);
    assert(class_size((CLASSES - 1) as nat) == PAGE_BYTES) by (compute_only);
    assert((0..CLASSES as int).all_spec(|c: int| class_ok(c as nat))) by (compute_only);
    assert((0..(last_group() + 1) as int).all_spec(|g: int| group_ok(g as nat)))
        by (compute_only);
    assert forall|c: nat| c < CLASSES implies #[trigger] class_ok(c) by {
        all_spec_ensures(0..CLASSES as int, |c: int| class_ok(c as nat));
        assert((|c: int| class_ok(c as nat))(c as int));
    }
    assert forall|g: nat| g <= last_group() implies #[trigger] group_ok(g) by {
        all_spec_ensures(0..(last_group() + 1) as int, |g: int| group_ok(g as nat));
        assert((|g: int| group_ok(g as nat))(g as int));
    }
}

/// What a slab of class `c` needs: a slot size that is a multiple of SLOT_MIN between SLOT_MIN and
/// the page, a run of order at most BLOCK_ORDER that holds at least one slot and at most MAP_SLOTS,
/// with at most a TAIL_SHARE-th of it after its last slot; and the next class is larger.
pub proof fn lemma_class(c: nat)
    requires
        c < CLASSES,
    ensures
        SLOT_MIN <= class_size(c) <= PAGE_BYTES,
        class_size(c) % SLOT_MIN as nat == 0,
        slab_order(c) <= BLOCK_ORDER,
        class_size(c) <= run_bytes(slab_order(c)),
        run_bytes(slab_order(c)) / class_size(c) as int <= MAP_SLOTS as int,
        (run_bytes(slab_order(c)) % class_size(c) as int) * TAIL_SHARE as int <= run_bytes(slab_order(c)),
        c + 1 < CLASSES ==> class_size(c) < class_size(c + 1),
        class_size(0) == SLOT_MIN,
        class_size((CLASSES - 1) as nat) == PAGE_BYTES,
{
    lemma_classes();
    assert(class_ok(c));
}

/// The slot size of class `c`.
pub(crate) fn size(c: usize) -> (r: usize)
    requires
        c < CLASSES,
    ensures
        r as nat == class_size(c as nat),
{
    proof {
        lemma_classes();
        assert(class_ok(c as nat));
    }
    if c < LINEAR_CLASSES {
        return (c + 1) * SLOT_MIN;
    }
    let d = c - LINEAR_CLASSES;
    let g = d / STEPS;
    let mut b = LINEAR_CLASSES * SLOT_MIN;
    let mut i: usize = 0;
    while i < g
        invariant
            i <= g,
            g <= last_group(),
            b as nat == group_base(i as nat),
            forall|h: nat| h <= last_group() ==> #[trigger] group_ok(h),
        decreases g - i,
    {
        proof {
            assert(group_ok((i + 1) as nat));
        }
        b = b * 2;
        i = i + 1;
    }
    b + (d % STEPS + 1) * (b / STEPS)
}

/// The order of the runs class `c`'s slabs are cut from.
pub(crate) fn order(c: usize) -> (r: usize)
    requires
        c < CLASSES,
    ensures
        r as nat == slab_order(c as nat),
        r <= BLOCK_ORDER,
{
    let s = size(c);
    proof {
        lemma_class(c as nat);
        lemma_block_pages();
    }
    let mut k: usize = 0;
    loop
        invariant
            k <= BLOCK_ORDER,
            s as nat == class_size(c as nat),
            SLOT_MIN <= s <= PAGE_BYTES,
            order_from(s as nat, k as nat) == slab_order(c as nat),
        decreases BLOCK_ORDER - k,
    {
        if k >= BLOCK_ORDER {
            return k;
        }
        proof {
            lemma_block_pages();
            lemma_pages(k as nat, BLOCK_ORDER as nat);
            lemma_pages((k + 1) as nat, BLOCK_ORDER as nat);
        }
        let run = order_pages(k) * PAGE_BYTES;
        if (run % s) * TAIL_SHARE <= run {
            return k;
        }
        let next = order_pages(k + 1) * PAGE_BYTES;
        if next / s > MAP_SLOTS {
            return k;
        }
        k = k + 1;
    }
}

/// The smallest class whose slots hold `n` bytes.
#[cfg(verus_keep_ghost)]
pub(crate) fn class_of(n: usize) -> (c: usize)
    requires
        n <= PAGE_BYTES,
    ensures
        c < CLASSES,
        n <= class_size(c as nat),
        forall|d: nat| d < c ==> #[trigger] class_size(d) < n,
{
    proof {
        lemma_classes();
    }
    let mut c: usize = 0;
    while size(c) < n
        invariant
            c < CLASSES,
            n <= PAGE_BYTES,
            class_size((CLASSES - 1) as nat) == PAGE_BYTES,
            forall|d: nat| d < c ==> #[trigger] class_size(d) < n,
        decreases CLASSES - c,
    {
        proof {
            assert(c + 1 < CLASSES);
        }
        c = c + 1;
    }
    c
}

} // verus!
