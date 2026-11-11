// SPDX-License-Identifier: MIT
//! One slab: a backed page run cut into slots of one size, and the record that says which are free.
//!
//! The record is a plain value, so the allocator can keep it out of band, in a page apart from the
//! slots it describes: the run's base pointer and length, the slot size, the count of slots and of
//! free ones, and a bitmap of words whose bit i is set exactly when slot i is live or i is past the
//! last slot. The allocator never reads or writes a free slot. It holds the permission to each one
//! in a map of PointsToRaw, keyed by address, that its caller keeps for every slab at once. `owns`
//! states what that map holds of one slab: the bytes of each free slot at the slot's address,
//! nothing at a live slot's address, the run's tail after the last slot at the address after the
//! last slot when the slot size does not divide the run, and nothing else inside the run.
//!
//! - `new` takes a backed run and the permission to its bytes; every slot is free.
//! - `alloc` gives a free slot, its pointer and the permission to its bytes, or refuses exactly when
//!   no slot is free.
//! - `free` takes a live slot's permission back. It never refuses.
//! - `retire` takes back the permission to the whole run of a slab whose every slot is free.
//!
//! The bitmap holds one bit for each slot of a page of the smallest slots, so a slab holds at most
//! MAP_SLOTS slots; the slot sizes and run lengths that respect that are the size classes'.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::bits::*;

use crate::arch::*;

verus! {

broadcast use {group_raw_ptr_axioms, vstd::set_lib::range_set_properties};

/// The smallest slot: the alignment malloc promises under both targets' C ABIs, and StarMalloc's
/// smallest size class. Every slot is a multiple of it, and every slot address is aligned to it.
pub const SLOT_MIN: usize = 16;

/// The bits of one bitmap word.
pub const WORD_BITS: usize = 64;

/// The bitmap's words: one bit for each slot of a page of the smallest slots.
pub const MAP_WORDS: usize = PAGE_BYTES / SLOT_MIN / WORD_BITS;

/// The most slots one slab holds.
pub const MAP_SLOTS: usize = MAP_WORDS * WORD_BITS;

/// Bit `i` of the bitmap of words `m`.
pub open spec fn bit(m: Seq<u64>, i: int) -> bool {
    (m[i / WORD_BITS as int] >> ((i % WORD_BITS as int) as u64)) & 1u64 == 1u64
}

/// Setting and clearing bit `j` of a word changes bit `j` alone.
proof fn lemma_flip(x: u64, j: u64, k: u64)
    requires
        j < 64,
        k < 64,
    ensures
        ((x | (1u64 << j)) >> k) & 1u64 == 1u64 <==> (k == j || (x >> k) & 1u64 == 1u64),
        ((x & !(1u64 << j)) >> k) & 1u64 == 1u64 <==> (k != j && (x >> k) & 1u64 == 1u64),
{
    assert(j < 64 && k < 64 ==> (((x | (1u64 << j)) >> k) & 1u64 == 1u64 <==> (k == j || (x >> k) & 1u64
        == 1u64))) by (bit_vector);
    assert(j < 64 && k < 64 ==> (((x & !(1u64 << j)) >> k) & 1u64 == 1u64 <==> (k != j && (x >> k) & 1u64
        == 1u64))) by (bit_vector);
}

/// The bits of the words a new slab's bitmap is made of: none set, all set, and all from `s` up.
proof fn lemma_fill(s: u64, k: u64)
    requires
        s < 64,
        k < 64,
    ensures
        (0u64 >> k) & 1u64 == 0u64,
        (0xffff_ffff_ffff_ffffu64 >> k) & 1u64 == 1u64,
        ((0xffff_ffff_ffff_ffffu64 << s) >> k) & 1u64 == 1u64 <==> k >= s,
{
    assert(k < 64 ==> (0u64 >> k) & 1u64 == 0u64) by (bit_vector);
    assert(k < 64 ==> (0xffff_ffff_ffff_ffffu64 >> k) & 1u64 == 1u64) by (bit_vector);
    assert(s < 64 && k < 64 ==> (((0xffff_ffff_ffff_ffffu64 << s) >> k) & 1u64 == 1u64 <==> k >= s))
        by (bit_vector);
}

/// Index `i` of the bitmap is bit `i % WORD_BITS` of word `i / WORD_BITS`, and lies in word `w`
/// exactly when it lies between `w * WORD_BITS` and the next word.
proof fn lemma_word(i: int, w: int)
    requires
        0 <= i,
        0 <= w,
    ensures
        i == (i / WORD_BITS as int) * WORD_BITS as int + i % WORD_BITS as int,
        0 <= (i % WORD_BITS as int) < WORD_BITS,
        0 <= i / WORD_BITS as int,
        i < w * (WORD_BITS as int) <==> (i / WORD_BITS as int) < w,
        (i / WORD_BITS as int) == w <==> w * (WORD_BITS as int) <= i < w * (WORD_BITS as int) + (WORD_BITS as int),
{
    let b = WORD_BITS as int;
    lemma_fundamental_div_mod(i, b);
    lemma_mod_pos_bound(i, b);
    let q = i / b;
    let r = i % b;
    assert(i == q * b + r) by (nonlinear_arith)
        requires
            i == b * q + r,
    ;
    assert(0 <= q) by (nonlinear_arith)
        requires
            i == q * b + r,
            0 <= i,
            0 <= r < b,
            b == 64,
    ;
    assert(i < w * b <==> q < w) by (nonlinear_arith)
        requires
            i == q * b + r,
            0 <= r < b,
            b == 64,
    ;
    assert(q == w <==> w * b <= i < w * b + b) by (nonlinear_arith)
        requires
            i == q * b + r,
            0 <= r < b,
            b == 64,
    ;
}

/// The slot `i` of `slot` bytes from `base`, in a run of `bytes` bytes cut into `count` slots, lies in
/// the run, aligned to the smallest slot when the base and the slot are, and is the slot its offset
/// names.
proof fn lemma_slot(base: int, bytes: int, slot: int, count: int, i: int)
    requires
        0 < slot,
        0 <= bytes,
        count == bytes / slot,
        0 <= i <= count,
    ensures
        0 <= i * slot,
        i < count ==> i * slot + slot <= count * slot,
        i * slot <= count * slot <= bytes,
        bytes - count * slot < slot,
        (i * slot) / slot == i,
        (i * slot) % slot == 0,
        base % SLOT_MIN as int == 0 && slot % SLOT_MIN as int == 0 ==> (base + i * slot) % SLOT_MIN as int
            == 0,
{
    lemma_fundamental_div_mod(bytes, slot);
    lemma_mod_pos_bound(bytes, slot);
    assert(0 <= i * slot) by (nonlinear_arith)
        requires
            0 <= i,
            0 < slot,
    ;
    assert(i * slot <= count * slot) by (nonlinear_arith)
        requires
            i <= count,
            0 < slot,
    ;
    if i < count {
        assert(i * slot + slot <= count * slot) by (nonlinear_arith)
            requires
                i + 1 <= count,
                0 < slot,
        ;
    }
    assert(slot * count == count * slot) by (nonlinear_arith);
    lemma_fundamental_div_mod_converse(i * slot, slot, i, 0);
    if base % SLOT_MIN as int == 0 && slot % SLOT_MIN as int == 0 {
        let m = SLOT_MIN as int;
        lemma_fundamental_div_mod(base, m);
        lemma_fundamental_div_mod(slot, m);
        let qb = base / m;
        let qs = slot / m;
        assert(base + i * slot == (qb + i * qs) * m) by (nonlinear_arith)
            requires
                base == m * qb,
                slot == m * qs,
        ;
        lemma_fundamental_div_mod_converse(base + i * slot, m, qb + i * qs, 0);
    }
}

/// An offset that is a multiple of the slot is the slot its quotient names.
proof fn lemma_offset(off: int, slot: int)
    requires
        0 < slot,
        0 <= off,
        off % slot == 0,
    ensures
        off == (off / slot) * slot,
        0 <= off / slot,
        off > 0 ==> off >= slot,
{
    lemma_fundamental_div_mod(off, slot);
    let q = off / slot;
    assert(off == q * slot) by (nonlinear_arith)
        requires
            off == slot * q + 0,
    ;
    lemma_div_pos_is_pos(off, slot);
    if off > 0 {
        assert(q >= 1) by (nonlinear_arith)
            requires
                off == q * slot,
                off > 0,
                slot > 0,
        ;
        assert(q * slot >= slot) by (nonlinear_arith)
            requires
                q >= 1,
                slot > 0,
        ;
    }
}

/// Splits the first `n` slots of `slot` bytes from `base` off `run`, into `perms` at their
/// addresses, and returns the rest of `run`.
proof fn split_slots(
    tracked run: PointsToRaw,
    tracked perms: &mut Map<int, PointsToRaw>,
    base: int,
    slot: int,
    n: nat,
) -> (tracked rest: PointsToRaw)
    requires
        slot > 0,
        Set::range(base, base + n * slot).subset_of(run.dom()),
        forall|a: int| base <= a < base + n * slot ==> !old(perms).contains_key(a),
    ensures
        rest.provenance() == run.provenance(),
        rest.dom() == run.dom().difference(Set::range(base, base + n * slot)),
        forall|j: int|
            0 <= j < n ==> {
                &&& #[trigger] final(perms).contains_key(base + j * slot)
                &&& final(perms)[base + j * slot].is_range(base + j * slot, slot)
                &&& final(perms)[base + j * slot].provenance() == run.provenance()
            },
        forall|a: int| #[trigger]
            final(perms).contains_key(a) ==> old(perms).contains_key(a) || (base <= a < base + n * slot && (a
                - base) % slot == 0),
        forall|a: int| #[trigger]
            old(perms).contains_key(a) ==> final(perms).contains_key(a) && final(perms)[a] == old(perms)[a],
    decreases n,
{
    if n == 0 {
        assert(run.dom().difference(Set::range(base, base + n * slot)) =~= run.dom());
        run
    } else {
        let m = (n - 1) as nat;
        assert(m * slot + slot == n * slot) by (nonlinear_arith)
            requires
                m == n - 1,
        ;
        assert(0 <= m * slot) by (nonlinear_arith)
            requires
                slot > 0,
        ;
        assert forall|x: int| Set::range(base, base + slot).contains(x) implies run.dom().contains(x) by {
            assert(Set::range(base, base + n * slot).contains(x));
        }
        let tracked (one, more) = run.split(Set::range(base, base + slot));
        assert forall|x: int| Set::range(base + slot, base + slot + m * slot).contains(x) implies more.dom().contains(
            x,
        ) by {
            assert(Set::range(base, base + n * slot).contains(x));
        }
        let ghost before = *perms;
        perms.tracked_insert(base, one);
        let ghost mid = *perms;
        assert forall|a: int| base + slot <= a < base + slot + m * slot implies !mid.contains_key(a) by {
            assert(!before.contains_key(a));
        }
        let tracked rest = split_slots(more, perms, base + slot, slot, m);
        assert(rest.dom() =~= run.dom().difference(Set::range(base, base + n * slot)));
        assert forall|j: int| 0 <= j < n implies {
            &&& #[trigger] perms.contains_key(base + j * slot)
            &&& perms[base + j * slot].is_range(base + j * slot, slot)
            &&& perms[base + j * slot].provenance() == run.provenance()
        } by {
            if j == 0 {
                assert(base + j * slot == base);
                assert(mid.contains_key(base));
            } else {
                let k = j - 1;
                assert(base + j * slot == (base + slot) + k * slot) by (nonlinear_arith)
                    requires
                        k == j - 1,
                ;
                assert(perms.contains_key((base + slot) + k * slot));
            }
        }
        assert forall|a: int| #[trigger] perms.contains_key(a) implies before.contains_key(a) || (base <= a
            < base + n * slot && (a - base) % slot == 0) by {
            if !before.contains_key(a) {
                if a == base {
                    lemma_mod_multiples_basic(0, slot);
                } else {
                    assert(!mid.contains_key(a));
                    lemma_mod_add_multiples_vanish(a - base - slot, slot);
                }
            }
        }
        assert forall|a: int| #[trigger] before.contains_key(a) implies perms.contains_key(a) && perms[a]
            == before[a] by {
            assert(a != base);
            assert(mid.contains_key(a));
        }
        rest
    }
}

/// Takes the `n` slots of `slot` bytes from `base` out of `perms` and joins them into the permission
/// to their bytes.
proof fn join_slots(
    tracked perms: &mut Map<int, PointsToRaw>,
    base: int,
    slot: int,
    n: nat,
    p: Provenance,
) -> (tracked run: PointsToRaw)
    requires
        slot > 0,
        forall|j: int|
            0 <= j < n ==> {
                &&& #[trigger] old(perms).contains_key(base + j * slot)
                &&& old(perms)[base + j * slot].is_range(base + j * slot, slot)
                &&& old(perms)[base + j * slot].provenance() == p
            },
    ensures
        run.is_range(base, n * slot),
        run.provenance() == p,
        forall|a: int| #[trigger]
            final(perms).contains_key(a) ==> old(perms).contains_key(a) && final(perms)[a] == old(perms)[a],
        forall|a: int| #[trigger]
            old(perms).contains_key(a) ==> final(perms).contains_key(a) || (base <= a < base + n * slot && (a
                - base) % slot == 0),
        forall|a: int|
            base <= a < base + n * slot && (a - base) % slot == 0 ==> !#[trigger] final(perms).contains_key(a),
    decreases n,
{
    if n == 0 {
        PointsToRaw::empty(p)
    } else {
        let m = (n - 1) as nat;
        assert(m * slot + slot == n * slot) by (nonlinear_arith)
            requires
                m == n - 1,
        ;
        assert(0 <= m * slot) by (nonlinear_arith)
            requires
                slot > 0,
        ;
        let ghost before = *perms;
        assert(base + 0 * slot == base);
        assert(before.contains_key(base + 0 * slot));
        let tracked one = perms.tracked_remove(base);
        let ghost mid = *perms;
        assert forall|j: int| 0 <= j < m implies {
            &&& #[trigger] mid.contains_key((base + slot) + j * slot)
            &&& mid[(base + slot) + j * slot].is_range((base + slot) + j * slot, slot)
            &&& mid[(base + slot) + j * slot].provenance() == p
        } by {
            let k = j + 1;
            assert((base + slot) + j * slot == base + k * slot) by (nonlinear_arith)
                requires
                    k == j + 1,
            ;
            assert(k * slot >= slot) by (nonlinear_arith)
                requires
                    k >= 1,
                    slot > 0,
            ;
            assert(before.contains_key(base + k * slot));
        }
        let tracked more = join_slots(perms, base + slot, slot, m, p);
        let tracked run = one.join(more);
        assert(run.dom() =~= Set::range(base, base + n * slot));
        assert forall|a: int| #[trigger] perms.contains_key(a) implies before.contains_key(a) && perms[a]
            == before[a] by {
            assert(mid.contains_key(a));
        }
        assert forall|a: int| #[trigger] before.contains_key(a) implies perms.contains_key(a) || (base <= a
            < base + n * slot && (a - base) % slot == 0) by {
            if a == base {
                lemma_mod_multiples_basic(0, slot);
            } else {
                assert(mid.contains_key(a));
                lemma_mod_add_multiples_vanish(a - base - slot, slot);
            }
        }
        assert forall|a: int| base <= a < base + n * slot && (a - base) % slot == 0 implies !#[trigger] perms.contains_key(
            a,
        ) by {
            if a == base {
                assert(!mid.contains_key(a));
            } else {
                lemma_offset(a - base, slot);
                lemma_mod_add_multiples_vanish(a - base - slot, slot);
                assert(base + slot <= a < base + slot + m * slot);
            }
        }
        run
    }
}

/// One slab's record: its run, its slots and which of them are free.
pub struct Slab {
    /// The start of the run, with the provenance of the permission to it.
    base: *mut u8,
    /// The run's length.
    bytes: usize,
    /// The bytes of one slot.
    slot: usize,
    /// The slots: the whole slots the run holds.
    count: usize,
    /// The free slots.
    free: usize,
    /// Bit i set exactly when slot i is live or i is not a slot.
    map: [u64; MAP_WORDS],
}

impl Slab {
    /// The start of the run.
    pub closed spec fn base(&self) -> *mut u8 {
        self.base
    }

    /// The run's length.
    pub closed spec fn bytes(&self) -> nat {
        self.bytes as nat
    }

    /// The bytes of one slot.
    pub closed spec fn slot(&self) -> nat {
        self.slot as nat
    }

    /// The slots the run holds.
    pub closed spec fn count(&self) -> nat {
        self.count as nat
    }

    /// The free slots, by index.
    pub closed spec fn free_slots(&self) -> Set<int> {
        Set::range(0, self.count as int).filter(|i: int| !bit(self.map@, i))
    }

    /// The address of slot `i`, or of the tail when `i` is the count.
    pub open spec fn addr(&self, i: int) -> int {
        self.base()@.addr + i * self.slot()
    }

    /// The slot the address `a` of the run falls in.
    pub open spec fn index(&self, a: int) -> int {
        (a - self.base()@.addr) / self.slot() as int
    }

    /// The bytes of the run after the last slot.
    pub open spec fn tail(&self) -> int {
        self.bytes() - self.count() * self.slot()
    }

    /// The address `a` is in the run.
    pub open spec fn within(&self, a: int) -> bool {
        self.base()@.addr <= a < self.base()@.addr + self.bytes()
    }

    /// The live slots, by index.
    pub open spec fn live(&self) -> Set<int> {
        Set::range(0, self.count() as int).difference(self.free_slots())
    }

    /// `a` is the address of a live slot.
    pub open spec fn holds(&self, a: int) -> bool {
        &&& self.within(a)
        &&& a == self.addr(self.index(a))
        &&& self.live().contains(self.index(a))
    }

    /// The record is consistent: the slot is a multiple of the smallest slot and the base aligned
    /// to it, the run holds between one slot and MAP_SLOTS, every bit past the last slot is set and
    /// the free count counts the clear bits.
    pub closed spec fn wf(&self) -> bool {
        &&& SLOT_MIN <= self.slot
        &&& self.slot % SLOT_MIN == 0
        &&& self.base@.addr % SLOT_MIN == 0
        &&& self.base@.addr + self.bytes <= usize::MAX + 1
        &&& self.count == self.bytes / self.slot
        &&& 0 < self.count <= MAP_SLOTS
        &&& self.map@.len() == MAP_WORDS
        &&& forall|i: int| self.count <= i < MAP_SLOTS ==> #[trigger] bit(self.map@, i)
        &&& self.free == self.free_slots().len()
    }

    /// The map `perms` holds the bytes of each free slot at its address and nothing at a live
    /// slot's address, with the run's provenance; the tail at the address after the last slot when
    /// the run has one; and nothing else inside the run.
    pub open spec fn owns(&self, perms: Map<int, PointsToRaw>) -> bool {
        let p = self.base()@.provenance;
        &&& forall|i: int|
            0 <= i < self.count() ==> (#[trigger] perms.contains_key(self.addr(i)) <==> self.free_slots().contains(i))
        &&& forall|i: int| #[trigger]
            self.free_slots().contains(i) ==> {
                &&& perms[self.addr(i)].is_range(self.addr(i), self.slot() as int)
                &&& perms[self.addr(i)].provenance() == p
            }
        &&& self.tail() > 0 ==> {
            &&& perms.contains_key(self.addr(self.count() as int))
            &&& perms[self.addr(self.count() as int)].is_range(self.addr(self.count() as int), self.tail())
            &&& perms[self.addr(self.count() as int)].provenance() == p
        }
        &&& forall|a: int| #[trigger]
            perms.contains_key(a) && self.within(a) ==> {
                &&& a == self.addr(self.index(a))
                &&& 0 <= self.index(a) <= self.count()
                &&& self.index(a) == self.count() ==> self.tail() > 0
            }
    }

    /// `after` holds what `before` holds at every address outside the run.
    pub open spec fn outside(&self, before: Map<int, PointsToRaw>, after: Map<int, PointsToRaw>) -> bool {
        forall|a: int|
            #![trigger after.contains_key(a)]
            #![trigger before.contains_key(a)]
            !self.within(a) ==> (after.contains_key(a) <==> before.contains_key(a)) && (before.contains_key(a)
                ==> after[a] == before[a])
    }

    /// The record's facts about its slots: each lies in the run, aligned to the smallest slot, and is
    /// the slot its address names; the free slots are slots; and the free count is their number.
    pub proof fn lemma_slots(&self)
        requires
            self.wf(),
        ensures
            SLOT_MIN <= self.slot(),
            0 < self.count() <= MAP_SLOTS,
            self.count() == self.bytes() / self.slot(),
            0 <= self.tail() < self.slot(),
            self.tail() > 0 ==> self.within(self.addr(self.count() as int)),
            self.base()@.addr + self.bytes() <= usize::MAX + 1,
            self.free_slots().subset_of(Set::range(0, self.count() as int)),
            forall|i: int|
                0 <= i <= self.count() ==> {
                    &&& self.within(#[trigger] self.addr(i)) || i == self.count()
                    &&& self.addr(i) % SLOT_MIN as int == 0
                    &&& self.index(self.addr(i)) == i
                    &&& self.addr(i) + self.slot() <= self.base()@.addr + self.bytes() || i == self.count()
                    &&& !self.within(self.addr(i)) ==> i == self.count()
                },
    {
        let b = self.base@.addr as int;
        let s = self.slot as int;
        assert forall|i: int| 0 <= i <= self.count() implies {
            &&& self.within(#[trigger] self.addr(i)) || i == self.count()
            &&& self.addr(i) % SLOT_MIN as int == 0
            &&& self.index(self.addr(i)) == i
            &&& self.addr(i) + self.slot() <= self.base()@.addr + self.bytes() || i == self.count()
            &&& !self.within(self.addr(i)) ==> i == self.count()
        } by {
            lemma_slot(b, self.bytes as int, s, self.count as int, i);
            lemma_slot(b, self.bytes as int, s, self.count as int, 0);
        }
        lemma_slot(b, self.bytes as int, s, self.count as int, 0);
    }

    /// A map that holds what `before` holds at every address inside the run is one the record owns
    /// as well: an operation on another slab over the same map, which changes the map only inside
    /// its own run, leaves this slab's ownership as it was.
    pub proof fn lemma_owns_frame(&self, before: Map<int, PointsToRaw>, after: Map<int, PointsToRaw>)
        requires
            self.wf(),
            self.owns(before),
            forall|a: int|
                #![trigger after.contains_key(a)]
                #![trigger before.contains_key(a)]
                self.within(a) ==> (after.contains_key(a) <==> before.contains_key(a)) && (before.contains_key(a)
                    ==> after[a] == before[a]),
        ensures
            self.owns(after),
    {
        self.lemma_slots();
        assert forall|i: int| 0 <= i < self.count() implies (#[trigger] after.contains_key(self.addr(i))
            <==> self.free_slots().contains(i)) by {
            assert(self.within(self.addr(i)));
            assert(before.contains_key(self.addr(i)) <==> self.free_slots().contains(i));
        }
        assert forall|i: int| #[trigger] self.free_slots().contains(i) implies {
            &&& after[self.addr(i)].is_range(self.addr(i), self.slot() as int)
            &&& after[self.addr(i)].provenance() == self.base()@.provenance
        } by {
            assert(Set::range(0, self.count() as int).contains(i));
            assert(self.within(self.addr(i)));
            assert(before.contains_key(self.addr(i)));
        }
        if self.tail() > 0 {
            assert(before.contains_key(self.addr(self.count() as int)));
        }
        assert forall|a: int| #[trigger] after.contains_key(a) && self.within(a) implies {
            &&& a == self.addr(self.index(a))
            &&& 0 <= self.index(a) <= self.count()
            &&& self.index(a) == self.count() ==> self.tail() > 0
        } by {
            assert(before.contains_key(a));
        }
    }

    /// A slot whose entry in `perms` alone changed, from free to live or from live to free, as the
    /// record changed: the new record owns the new map.
    proof fn lemma_owns_toggle(
        s0: Slab,
        s: Slab,
        p0: Map<int, PointsToRaw>,
        p: Map<int, PointsToRaw>,
        i: int,
    )
        requires
            s0.wf(),
            s.wf(),
            s0.owns(p0),
            s.base() == s0.base(),
            s.bytes() == s0.bytes(),
            s.slot() == s0.slot(),
            s.count() == s0.count(),
            0 <= i < s0.count(),
            s.free_slots().contains(i) ==> {
                &&& p.contains_key(s0.addr(i))
                &&& p[s0.addr(i)].is_range(s0.addr(i), s0.slot() as int)
                &&& p[s0.addr(i)].provenance() == s0.base()@.provenance
            },
            !s.free_slots().contains(i) ==> !p.contains_key(s0.addr(i)),
            forall|k: int| k != i ==> (s.free_slots().contains(k) <==> s0.free_slots().contains(k)),
            forall|a: int|
                #![trigger p.contains_key(a)]
                #![trigger p0.contains_key(a)]
                a != s0.addr(i) ==> (p.contains_key(a) <==> p0.contains_key(a)) && (p0.contains_key(a) ==> p[a]
                    == p0[a]),
        ensures
            s.owns(p),
    {
        s0.lemma_slots();
        assert(s0.index(s0.addr(i)) == i);
        assert forall|k: int| 0 <= k < s.count() implies (#[trigger] p.contains_key(s.addr(k))
            <==> s.free_slots().contains(k)) by {
            assert(s.addr(k) == s0.addr(k));
            if k != i {
                assert(s0.index(s0.addr(k)) == k);
                assert(p0.contains_key(s0.addr(k)) <==> s0.free_slots().contains(k));
            }
        }
        assert forall|k: int| #[trigger] s.free_slots().contains(k) implies {
            &&& p[s.addr(k)].is_range(s.addr(k), s.slot() as int)
            &&& p[s.addr(k)].provenance() == s.base()@.provenance
        } by {
            assert(s.addr(k) == s0.addr(k));
            if k != i {
                assert(s0.free_slots().contains(k));
                assert(s0.index(s0.addr(k)) == k);
                assert(p0.contains_key(s0.addr(k)));
            }
        }
        if s.tail() > 0 {
            let c = s0.count() as int;
            assert(s0.index(s0.addr(c)) == c);
            assert(s.addr(c) == s0.addr(c));
            assert(p0.contains_key(s0.addr(c)));
        }
        assert forall|a: int| #[trigger] p.contains_key(a) && s.within(a) implies {
            &&& a == s.addr(s.index(a))
            &&& 0 <= s.index(a) <= s.count()
            &&& s.index(a) == s.count() ==> s.tail() > 0
        } by {
            if a != s0.addr(i) {
                assert(p0.contains_key(a));
            }
        }
    }

    /// A slab over the run of `bytes` bytes at `base`, cut into slots of `slot` bytes, every slot
    /// free: the permission to the run goes into `perms`, a slot's bytes at the slot's address and
    /// the tail at the address after the last slot.
    pub fn new(
        base: *mut u8,
        bytes: usize,
        slot: usize,
        run: Tracked<PointsToRaw>,
        Tracked(perms): Tracked<&mut Map<int, PointsToRaw>>,
    ) -> (r: Self)
        requires
            SLOT_MIN <= slot,
            slot % SLOT_MIN == 0,
            base@.addr % SLOT_MIN == 0,
            base@.addr + bytes <= usize::MAX + 1,
            slot <= bytes,
            bytes / slot <= MAP_SLOTS,
            run@.is_range(base@.addr as int, bytes as int),
            run@.provenance() == base@.provenance,
            forall|a: int| base@.addr <= a < base@.addr + bytes ==> !old(perms).contains_key(a),
        ensures
            r.wf(),
            r.base() == base,
            r.bytes() == bytes,
            r.slot() == slot,
            r.count() == bytes / slot,
            r.free_slots() == Set::range(0, r.count() as int),
            r.owns(*final(perms)),
            r.outside(*old(perms), *final(perms)),
    {
        let count = bytes / slot;
        proof {
            lemma_div_non_zero(bytes as int, slot as int);
            assert(count > 0);
        }
        let mut map = [0u64;MAP_WORDS];
        let mut w: usize = 0;
        while w < MAP_WORDS
            invariant
                w <= MAP_WORDS,
                map@.len() == MAP_WORDS,
                0 < count <= MAP_SLOTS,
                forall|i: int| 0 <= i < w * WORD_BITS ==> (#[trigger] bit(map@, i) <==> i >= count),
            decreases MAP_WORDS - w,
        {
            let lo = w * WORD_BITS;
            let word = if lo + WORD_BITS <= count {
                0u64
            } else if lo >= count {
                u64::MAX
            } else {
                u64::MAX << ((count - lo) as u64)
            };
            let ghost before = map@;
            map[w] = word;
            proof {
                assert forall|i: int| 0 <= i < (w + 1) * WORD_BITS implies (#[trigger] bit(map@, i) <==> i
                    >= count) by {
                    lemma_word(i, w as int);
                    let q = i / WORD_BITS as int;
                    let j = i % WORD_BITS as int;
                    if q < w {
                        assert(map@[q] == before[q]);
                        assert(bit(before, i) <==> i >= count);
                    } else {
                        assert(q == w);
                        assert(map@[q] == word);
                        if lo + WORD_BITS <= count {
                            lemma_fill(0, j as u64);
                        } else if lo >= count {
                            lemma_fill(0, j as u64);
                        } else {
                            lemma_fill((count - lo) as u64, j as u64);
                        }
                    }
                }
            }
            w += 1;
        }
        let ghost b = base@.addr as int;
        let ghost s = slot as int;
        let ghost n = count as nat;
        let ghost start = *perms;
        proof {
            lemma_slot(b, bytes as int, s, count as int, count as int);
            assert forall|x: int| Set::range(b, b + n * s).contains(x) implies run@.dom().contains(x) by {
                assert(Set::range(b, b + bytes).contains(x));
            }
        }
        let tracked rest = split_slots(run.get(), perms, b, s, n);
        let ghost mid = *perms;
        let ghost tail = bytes as int - count as int * slot as int;
        let ghost t = b + n * s;
        proof {
            if tail > 0 {
                assert(rest.dom() =~= Set::range(t, t + tail));
                perms.tracked_insert(t, rest);
            }
        }
        let r = Slab { base, bytes, slot, count, free: count, map };
        proof {
            let fin = *perms;
            let pv = base@.provenance;
            assert forall|i: int| count <= i < MAP_SLOTS implies #[trigger] bit(r.map@, i) by {
                assert(i < MAP_WORDS * WORD_BITS);
            }
            assert(r.free_slots() =~= Set::range(0, count as int));
            assert(r.wf());
            r.lemma_slots();
            assert(r.tail() == tail);
            assert(r.addr(count as int) == t);
            assert forall|i: int| 0 <= i < n implies {
                &&& fin.contains_key(#[trigger] r.addr(i))
                &&& fin[r.addr(i)].is_range(r.addr(i), s)
                &&& fin[r.addr(i)].provenance() == pv
            } by {
                assert(r.addr(i) == b + i * s);
                assert(mid.contains_key(b + i * s));
                lemma_slot(b, bytes as int, s, count as int, i);
                assert(b + i * s < t);
            }
            assert forall|i: int| 0 <= i < r.count() implies (#[trigger] fin.contains_key(r.addr(i))
                <==> r.free_slots().contains(i)) by {
                assert(fin.contains_key(r.addr(i)));
            }
            assert forall|i: int| #[trigger] r.free_slots().contains(i) implies {
                &&& fin[r.addr(i)].is_range(r.addr(i), r.slot() as int)
                &&& fin[r.addr(i)].provenance() == pv
            } by {
                assert(fin.contains_key(r.addr(i)));
            }
            assert forall|a: int| #[trigger] fin.contains_key(a) && r.within(a) implies {
                &&& a == r.addr(r.index(a))
                &&& 0 <= r.index(a) <= r.count()
                &&& r.index(a) == r.count() ==> r.tail() > 0
            } by {
                if a == t && tail > 0 {
                    assert(r.index(t) == count);
                } else {
                    assert(mid.contains_key(a));
                    assert(!start.contains_key(a));
                    assert(b <= a < t && (a - b) % s == 0);
                    lemma_offset(a - b, s);
                    let k = (a - b) / s;
                    assert(k < n) by {
                        if k >= n {
                            assert(k * s >= n * s) by (nonlinear_arith)
                                requires
                                    k >= n,
                                    s > 0,
                            ;
                        }
                    }
                    assert(r.index(a) == k);
                }
            }
            assert(r.owns(fin));
            assert forall|a: int|
                #![trigger fin.contains_key(a)]
                #![trigger start.contains_key(a)]
                !r.within(a) implies (fin.contains_key(a) <==> start.contains_key(a)) && (start.contains_key(a)
                ==> fin[a] == start[a]) by {
                assert(a != t || tail == 0);
                if fin.contains_key(a) {
                    assert(mid.contains_key(a));
                }
                if start.contains_key(a) {
                    assert(mid.contains_key(a));
                }
            }
        }
        r
    }

    /// A free slot, now live: its pointer, with the run's provenance, and the permission to its
    /// bytes, taken out of `perms`; or None, changing nothing, exactly when no slot is free.
    pub fn alloc(&mut self, Tracked(perms): Tracked<&mut Map<int, PointsToRaw>>) -> (r: Option<
        (*mut u8, Tracked<PointsToRaw>),
    >)
        requires
            old(self).wf(),
            old(self).owns(*old(perms)),
        ensures
            final(self).wf(),
            final(self).base() == old(self).base(),
            final(self).bytes() == old(self).bytes(),
            final(self).slot() == old(self).slot(),
            final(self).count() == old(self).count(),
            final(self).owns(*final(perms)),
            match r {
                None => {
                    &&& old(self).free_slots() == Set::<int>::empty()
                    &&& *final(self) == *old(self)
                    &&& *final(perms) == *old(perms)
                },
                Some((p, perm)) => {
                    let i = old(self).index(p@.addr as int);
                    &&& old(self).free_slots().contains(i)
                    &&& p@.addr == old(self).addr(i)
                    &&& p@.provenance == old(self).base()@.provenance
                    &&& p@.addr % SLOT_MIN == 0
                    &&& perm@.is_range(p@.addr as int, old(self).slot() as int)
                    &&& perm@.provenance() == old(self).base()@.provenance
                    &&& final(self).free_slots() == old(self).free_slots().remove(i)
                    &&& final(self).holds(p@.addr as int)
                    &&& *final(perms) == old(perms).remove(p@.addr as int)
                },
            },
    {
        let ghost s0 = *self;
        let ghost p0 = *perms;
        proof {
            self.lemma_slots();
            vstd::set_lib::lemma_set_empty_equivalency_len(self.free_slots());
        }
        if self.free == 0 {
            return None;
        }
        let ghost some = choose|i: int| self.free_slots().contains(i);
        let mut w: usize = 0;
        while self.map[w] == u64::MAX
            invariant
                w < MAP_WORDS,
                *self == s0,
                s0.wf(),
                s0.free_slots().contains(some),
                0 <= some < s0.count(),
                forall|i: int| 0 <= i < w * WORD_BITS ==> #[trigger] bit(self.map@, i),
            decreases MAP_WORDS - w,
        {
            proof {
                assert forall|i: int| 0 <= i < (w + 1) * WORD_BITS implies #[trigger] bit(self.map@, i) by {
                    lemma_word(i, w as int);
                    if i >= w * WORD_BITS {
                        assert(i / WORD_BITS as int == w);
                        lemma_fill(0, (i % WORD_BITS as int) as u64);
                    }
                }
                if w + 1 >= MAP_WORDS {
                    assert(some < MAP_SLOTS);
                    assert(bit(self.map@, some));
                    assert(!s0.free_slots().contains(some));
                }
            }
            w += 1;
        }
        let word = self.map[w];
        let j = word.trailing_ones() as usize;
        proof {
            axiom_u64_trailing_ones(word);
        }
        let i = w * WORD_BITS + j;
        proof {
            lemma_word(i as int, w as int);
            assert(i / WORD_BITS == w);
            assert(i % WORD_BITS == j);
            assert(!bit(self.map@, i as int));
            assert(i < self.count);
            assert(s0.free_slots().contains(i as int));
            lemma_slot(self.base@.addr as int, self.bytes as int, self.slot as int, self.count as int, i as int);
        }
        let ghost old_map = self.map@;
        self.map[w] = word | (1u64 << (j as u64));
        self.free = self.free - 1;
        proof {
            assert forall|k: int| 0 <= k < MAP_SLOTS implies #[trigger] bit(self.map@, k) == (bit(old_map, k)
                || k == i) by {
                lemma_word(k, w as int);
                if k / WORD_BITS as int == w {
                    lemma_flip(word, j as u64, (k % WORD_BITS as int) as u64);
                } else {
                    assert(self.map@[k / WORD_BITS as int] == old_map[k / WORD_BITS as int]);
                }
            }
            assert(self.free_slots() =~= s0.free_slots().remove(i as int));
            assert forall|k: int| self.count <= k < MAP_SLOTS implies #[trigger] bit(self.map@, k) by {
                assert(bit(old_map, k));
            }
            assert(self.wf());
        }
        let a = self.base.addr() + i * self.slot;
        proof {
            assert(a as int == s0.addr(i as int));
            assert(p0.contains_key(s0.addr(i as int)));
        }
        let tracked perm = perms.tracked_remove(a as int);
        proof {
            Slab::lemma_owns_toggle(s0, *self, p0, *perms, i as int);
            assert(s0.index(a as int) == i);
            self.lemma_slots();
            assert(self.index(a as int) == i);
            assert(self.live().contains(i as int));
        }
        Some((self.base.with_addr(a), Tracked(perm)))
    }

    /// Takes back the permission to the live slot at `a`; the slot is free again.
    pub fn free(
        &mut self,
        a: usize,
        perm: Tracked<PointsToRaw>,
        Tracked(perms): Tracked<&mut Map<int, PointsToRaw>>,
    )
        requires
            old(self).wf(),
            old(self).owns(*old(perms)),
            old(self).holds(a as int),
            perm@.is_range(a as int, old(self).slot() as int),
            perm@.provenance() == old(self).base()@.provenance,
        ensures
            final(self).wf(),
            final(self).base() == old(self).base(),
            final(self).bytes() == old(self).bytes(),
            final(self).slot() == old(self).slot(),
            final(self).count() == old(self).count(),
            final(self).owns(*final(perms)),
            final(self).free_slots() == old(self).free_slots().insert(old(self).index(a as int)),
            *final(perms) == old(perms).insert(a as int, perm@),
    {
        let ghost s0 = *self;
        let ghost p0 = *perms;
        proof {
            self.lemma_slots();
            lemma_div_pos_is_pos(a as int - self.base@.addr as int, self.slot as int);
        }
        let i = (a - self.base.addr()) / self.slot;
        let w = i / WORD_BITS;
        let j = i % WORD_BITS;
        proof {
            assert(i as int == s0.index(a as int));
            assert(0 <= i < self.count);
            lemma_word(i as int, w as int);
            assert(!s0.free_slots().contains(i as int));
            assert(bit(self.map@, i as int));
            assert(s0.free_slots().subset_of(Set::range(0, self.count as int).remove(i as int)));
            vstd::set_lib::lemma_len_subset(s0.free_slots(), Set::range(0, self.count as int).remove(i as int));
        }
        let word = self.map[w];
        let ghost old_map = self.map@;
        self.map[w] = word & !(1u64 << (j as u64));
        self.free = self.free + 1;
        proof {
            assert forall|k: int| 0 <= k < MAP_SLOTS implies #[trigger] bit(self.map@, k) == (bit(old_map, k)
                && k != i) by {
                lemma_word(k, w as int);
                if k / WORD_BITS as int == w {
                    lemma_flip(word, j as u64, (k % WORD_BITS as int) as u64);
                } else {
                    assert(self.map@[k / WORD_BITS as int] == old_map[k / WORD_BITS as int]);
                }
            }
            assert(self.free_slots() =~= s0.free_slots().insert(i as int));
            assert forall|k: int| self.count <= k < MAP_SLOTS implies #[trigger] bit(self.map@, k) by {
                assert(bit(old_map, k));
            }
            assert(self.wf());
            assert(a as int == s0.addr(i as int));
            assert(!p0.contains_key(a as int));
            perms.tracked_insert(a as int, perm.get());
            Slab::lemma_owns_toggle(s0, *self, p0, *perms, i as int);
        }
    }

    /// No slot is free.
    pub fn is_full(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == (self.free_slots() == Set::<int>::empty()),
    {
        proof {
            vstd::set_lib::lemma_set_empty_equivalency_len(self.free_slots());
        }
        self.free == 0
    }

    /// Every slot is free.
    pub fn is_empty(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == (self.free_slots() == Set::range(0, self.count() as int)),
    {
        proof {
            self.lemma_slots();
            if self.free == self.count {
                vstd::set_lib::lemma_subset_equality(self.free_slots(), Set::range(0, self.count as int));
            }
        }
        self.free == self.count
    }

    /// The start of the run.
    pub fn start(&self) -> (r: *mut u8)
        ensures
            r == self.base(),
    {
        self.base
    }

    /// The address `a` is in the run.
    pub fn holds_address(&self, a: usize) -> (r: bool)
        ensures
            r == self.within(a as int),
    {
        let base = self.base.addr();
        base <= a && a - base < self.bytes
    }

    /// Takes the permission to the whole run out of `perms`, every slot being free.
    pub fn retire(&self, Tracked(perms): Tracked<&mut Map<int, PointsToRaw>>) -> (run: Tracked<
        PointsToRaw,
    >)
        requires
            self.wf(),
            self.owns(*old(perms)),
            self.free_slots() == Set::range(0, self.count() as int),
        ensures
            run@.is_range(self.base()@.addr as int, self.bytes() as int),
            run@.provenance() == self.base()@.provenance,
            self.outside(*old(perms), *final(perms)),
            forall|a: int| self.within(a) ==> !#[trigger] final(perms).contains_key(a),
    {
        let ghost b = self.base@.addr as int;
        let ghost s = self.slot as int;
        let ghost n = self.count as nat;
        let ghost p = self.base@.provenance;
        let ghost start = *perms;
        let ghost t = self.addr(self.count() as int);
        proof {
            self.lemma_slots();
            lemma_slot(b, self.bytes as int, s, n as int, n as int);
            assert(t == b + n * s);
            assert forall|j: int| 0 <= j < n implies {
                &&& #[trigger] start.contains_key(b + j * s)
                &&& start[b + j * s].is_range(b + j * s, s)
                &&& start[b + j * s].provenance() == p
            } by {
                assert(self.free_slots().contains(j));
                assert(self.addr(j) == b + j * s);
                assert(start.contains_key(self.addr(j)));
            }
        }
        let tracked mut run = join_slots(perms, b, s, n, p);
        let ghost mid = *perms;
        proof {
            if self.tail() > 0 {
                assert(start.contains_key(t));
                assert(mid.contains_key(t));
                let tracked last = perms.tracked_remove(t);
                run = run.join(last);
            }
            assert(run.dom() =~= Set::range(b, b + self.bytes()));
            let fin = *perms;
            assert forall|a: int| self.within(a) implies !#[trigger] fin.contains_key(a) by {
                if fin.contains_key(a) {
                    assert(mid.contains_key(a));
                    assert(start.contains_key(a));
                    let k = self.index(a);
                    lemma_slot(b, self.bytes as int, s, n as int, k);
                    assert(a == b + k * s);
                    if k < n {
                        assert((a - b) % s == 0);
                        assert(a < b + n * s);
                        assert(!mid.contains_key(a));
                    } else {
                        assert(a == t);
                    }
                }
            }
            assert forall|a: int|
                #![trigger fin.contains_key(a)]
                #![trigger start.contains_key(a)]
                !self.within(a) implies (fin.contains_key(a) <==> start.contains_key(a)) && (start.contains_key(
                a,
            ) ==> fin[a] == start[a]) by {
                if fin.contains_key(a) {
                    assert(mid.contains_key(a));
                }
                if start.contains_key(a) {
                    assert(mid.contains_key(a));
                }
            }
        }
        Tracked(run)
    }
}

} // verus!
