use vstd::prelude::*;
verus! {

use crate::arch::{MEM_2M_MASK, MEM_4K_MASK};
#[cfg(verus_keep_ghost)]
use crate::arch::{MEM_1G_MASK, MEM_MASK};
use crate::define::*;

pub open spec fn mem_valid(v: PAddr) -> bool {
    v & (!MEM_MASK) as usize == 0
}

#[verifier(when_used_as_spec(spec_va_4k_valid))]
pub fn va_4k_valid(va: usize) -> (ret: bool)
    ensures
        ret == spec_va_4k_valid(va),
{
    (va & (!MEM_4K_MASK) as usize == 0) && (va as u64 >> L4_SHIFT as u64 & INDEX_MASK as u64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_va_4k_valid(va: usize) -> bool {
    (va & (!MEM_4K_MASK) as usize == 0) && (va as u64 >> L4_SHIFT as u64 & INDEX_MASK as u64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

#[verifier(when_used_as_spec(spec_va_2m_valid))]
pub fn va_2m_valid(va: usize) -> (ret: bool)
    ensures
        ret == spec_va_2m_valid(va),
{
    (va & (!MEM_2M_MASK) as usize == 0) && (va as u64 >> L4_SHIFT as u64 & INDEX_MASK as u64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_va_2m_valid(va: usize) -> bool {
    (va & (!MEM_2M_MASK) as usize == 0) && (va as u64 >> L4_SHIFT as u64 & INDEX_MASK as u64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_va_1g_valid(va: usize) -> bool {
    (va & (!MEM_1G_MASK) as usize == 0) && (va as u64 >> L4_SHIFT as u64 & INDEX_MASK as u64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_v2l1index(va: usize) -> L1Index {
    (va >> L1_SHIFT & INDEX_MASK) as usize
}

pub open spec fn spec_v2l2index(va: usize) -> L2Index {
    (va >> L2_SHIFT & INDEX_MASK) as usize
}

pub open spec fn spec_v2l3index(va: usize) -> L3Index {
    (va >> L3_SHIFT & INDEX_MASK) as usize
}

pub open spec fn spec_v2l4index(va: usize) -> L4Index {
    (va >> L4_SHIFT & INDEX_MASK) as usize
}

pub open spec fn spec_va2index(va: usize) -> (L4Index, L3Index, L2Index, L1Index) {
    (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))
}

pub open spec fn spec_index2va(i: (L4Index, L3Index, L2Index, L1Index)) -> usize
    recommends
        i.0 <= INDEX_MASK,
        i.1 <= INDEX_MASK,
        i.2 <= INDEX_MASK,
        i.3 <= INDEX_MASK,
{
    (i.0 as usize) << L4_SHIFT | (i.1 as usize) << L3_SHIFT | (i.2 as usize) << L2_SHIFT | (i.3 as usize) << L1_SHIFT
}

/// The address of an in-range index tuple whose L4 index is at or past the kernel's is a
/// valid 4k user address: page aligned, canonical and outside the kernel's L4 entries.
pub proof fn lemma_index2va_4k_valid(l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index)
    requires
        KERNEL_MEM_END_L4INDEX <= l4i < ENTRIES,
        0 <= l3i < ENTRIES,
        0 <= l2i < ENTRIES,
        0 <= l1i < ENTRIES,
    ensures
        spec_va_4k_valid(spec_index2va((l4i, l3i, l2i, l1i))),
{
    let va = spec_index2va((l4i, l3i, l2i, l1i));
    assert(va == l4i << L4_SHIFT | l3i << L3_SHIFT | l2i << L2_SHIFT | l1i << L1_SHIFT);
    assert(1 <= l4i < ENTRIES && l3i < ENTRIES && l2i < ENTRIES && l1i < ENTRIES ==> ((l4i << L4_SHIFT | l3i << L3_SHIFT
        | l2i << L2_SHIFT | l1i << L1_SHIFT) & (!MEM_4K_MASK) as usize == 0) && ((l4i << L4_SHIFT | l3i
        << L3_SHIFT | l2i << L2_SHIFT | l1i << L1_SHIFT) as u64 >> L4_SHIFT as u64 & INDEX_MASK as u64) >= 1u64) by (bit_vector);
    assert(KERNEL_MEM_END_L4INDEX as u64 == 1u64);
}

/// The address of an in-range index tuple with L1 index 0 whose L4 index is at or past the
/// kernel's is a valid 2m user address: 2m aligned, canonical and outside the kernel's L4 entries.
pub proof fn lemma_index2va_2m_valid(l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        KERNEL_MEM_END_L4INDEX <= l4i < ENTRIES,
        0 <= l3i < ENTRIES,
        0 <= l2i < ENTRIES,
    ensures
        spec_va_2m_valid(spec_index2va((l4i, l3i, l2i, 0))),
{
    let va = spec_index2va((l4i, l3i, l2i, 0));
    assert(va == l4i << L4_SHIFT | l3i << L3_SHIFT | l2i << L2_SHIFT | 0usize << L1_SHIFT);
    assert(1 <= l4i < ENTRIES && l3i < ENTRIES && l2i < ENTRIES ==> ((l4i << L4_SHIFT | l3i << L3_SHIFT | l2i << L2_SHIFT
        | 0usize << L1_SHIFT) & (!MEM_2M_MASK) as usize == 0) && ((l4i << L4_SHIFT | l3i << L3_SHIFT
        | l2i << L2_SHIFT | 0usize << L1_SHIFT) as u64 >> L4_SHIFT as u64 & INDEX_MASK as u64) >= 1u64) by (bit_vector);
    assert(KERNEL_MEM_END_L4INDEX as u64 == 1u64);
}

/// Two in-range index tuples name the same address only when they are equal. One instance of
/// va_lemma's pairwise clause, so a caller can instantiate it for one pair instead of carrying
/// the eight-variable quantifier.
pub proof fn lemma_index2va_injective(
    l4i: L4Index,
    l3i: L3Index,
    l2i: L2Index,
    l1i: L1Index,
    l4j: L4Index,
    l3j: L3Index,
    l2j: L2Index,
    l1j: L1Index,
)
    requires
        0 <= l4i < ENTRIES,
        0 <= l3i < ENTRIES,
        0 <= l2i < ENTRIES,
        0 <= l1i < ENTRIES,
        0 <= l4j < ENTRIES,
        0 <= l3j < ENTRIES,
        0 <= l2j < ENTRIES,
        0 <= l1j < ENTRIES,
    ensures
        ((l4i, l3i, l2i, l1i) =~= (l4j, l3j, l2j, l1j)) <==> spec_index2va((l4i, l3i, l2i, l1i))
            == spec_index2va((l4j, l3j, l2j, l1j)),
{
    lemma_index2va_fields(l4i, l3i, l2i, l1i);
    lemma_index2va_fields(l4j, l3j, l2j, l1j);
}

/// Each page table index of an address is nine bits.
pub proof fn lemma_va_index_bounds(va: usize)
    ensures
        spec_v2l4index(va) < ENTRIES,
        spec_v2l3index(va) < ENTRIES,
        spec_v2l2index(va) < ENTRIES,
        spec_v2l1index(va) < ENTRIES,
{
    assert((va >> L4_SHIFT & INDEX_MASK) < ENTRIES && (va >> L3_SHIFT & INDEX_MASK) < ENTRIES && (va >> L2_SHIFT & INDEX_MASK) < ENTRIES && (
    va >> L1_SHIFT & INDEX_MASK) < ENTRIES) by (bit_vector);
}

/// A valid 4k address is outside the kernel's L4 entries.
pub proof fn lemma_va_4k_valid_l4index(va: usize)
    requires
        spec_va_4k_valid(va),
    ensures
        KERNEL_MEM_END_L4INDEX <= spec_v2l4index(va),
{
    assert((va as u64 >> L4_SHIFT as u64 & INDEX_MASK as u64) >= 1u64 ==> (va >> L4_SHIFT & INDEX_MASK) >= 1) by (bit_vector);
    assert(KERNEL_MEM_END_L4INDEX as u64 == 1u64);
}

/// A valid 2m address has L1 index zero.
pub proof fn lemma_va_2m_valid_l1index(va: usize)
    requires
        spec_va_2m_valid(va),
    ensures
        spec_v2l1index(va) == 0,
{
    assert(va & (!MEM_2M_MASK) as usize == 0 ==> (va >> L1_SHIFT & INDEX_MASK) == 0)
        by (bit_vector);
}

/// A valid 1g address has L2 and L1 index zero.
pub proof fn lemma_va_1g_valid_indices(va: usize)
    requires
        spec_va_1g_valid(va),
    ensures
        spec_v2l2index(va) == 0,
        spec_v2l1index(va) == 0,
{
    assert(va & (!MEM_1G_MASK) as usize == 0 ==> (va >> L2_SHIFT & INDEX_MASK) == 0 && (va
        >> L1_SHIFT & INDEX_MASK) == 0) by (bit_vector);
}

/// The address of an in-range index tuple decomposes back into that tuple.
pub proof fn lemma_index2va_fields(l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index)
    requires
        0 <= l4i < ENTRIES,
        0 <= l3i < ENTRIES,
        0 <= l2i < ENTRIES,
        0 <= l1i < ENTRIES,
    ensures
        spec_va2index(spec_index2va((l4i, l3i, l2i, l1i))) == (l4i, l3i, l2i, l1i),
{
    assert(l4i < ENTRIES && l3i < ENTRIES && l2i < ENTRIES && l1i < ENTRIES ==> ((l4i << L4_SHIFT | l3i << L3_SHIFT | l2i
        << L2_SHIFT | l1i << L1_SHIFT) >> L4_SHIFT & INDEX_MASK) == l4i && ((l4i << L4_SHIFT | l3i << L3_SHIFT | l2i << L2_SHIFT | l1i
        << L1_SHIFT) >> L3_SHIFT & INDEX_MASK) == l3i && ((l4i << L4_SHIFT | l3i << L3_SHIFT | l2i << L2_SHIFT | l1i << L1_SHIFT) >> L2_SHIFT
        & INDEX_MASK) == l2i && ((l4i << L4_SHIFT | l3i << L3_SHIFT | l2i << L2_SHIFT | l1i << L1_SHIFT) >> L1_SHIFT & INDEX_MASK)
        == l1i) by (bit_vector);
}

/// A valid 4k address is the address of its own index tuple: it has no bits outside them.
pub proof fn lemma_va2index_index2va(va: usize)
    requires
        spec_va_4k_valid(va),
    ensures
        spec_index2va(spec_va2index(va)) == va,
{
    assert(va & (!MEM_4K_MASK) as usize == 0 ==> ((va >> L4_SHIFT & INDEX_MASK) << L4_SHIFT | (va
        >> L3_SHIFT & INDEX_MASK) << L3_SHIFT | (va >> L2_SHIFT & INDEX_MASK) << L2_SHIFT | (va >> L1_SHIFT & INDEX_MASK) << L1_SHIFT) == va)
        by (bit_vector);
}

pub proof fn va_lemma()
    ensures
        forall|va: VAddr|
            #![trigger spec_va_4k_valid(va), spec_v2l4index(va)]
            #![trigger spec_va_4k_valid(va), spec_v2l3index(va)]
            #![trigger spec_va_4k_valid(va), spec_v2l2index(va)]
            #![trigger spec_va_4k_valid(va), spec_v2l1index(va)]
            spec_va_4k_valid(va) ==> 0 <= spec_v2l4index(va) < ENTRIES && 0 <= spec_v2l3index(va) < ENTRIES
                && 0 <= spec_v2l2index(va) < ENTRIES && 0 <= spec_v2l1index(va) < ENTRIES,
        forall|va: VAddr|
            #![trigger spec_va_2m_valid(va), spec_v2l4index(va)]
            #![trigger spec_va_2m_valid(va), spec_v2l3index(va)]
            #![trigger spec_va_2m_valid(va), spec_v2l2index(va)]
            #![trigger spec_va_2m_valid(va), spec_v2l1index(va)]
            spec_va_2m_valid(va) ==> 0 <= spec_v2l4index(va) < ENTRIES && 0 <= spec_v2l3index(va) < ENTRIES
                && 0 <= spec_v2l2index(va) < ENTRIES && 0 == spec_v2l1index(va),
        forall|va: VAddr|
            #![trigger spec_va_1g_valid(va), spec_v2l4index(va)]
            #![trigger spec_va_1g_valid(va), spec_v2l3index(va)]
            #![trigger spec_va_1g_valid(va), spec_v2l2index(va)]
            #![trigger spec_va_1g_valid(va), spec_v2l1index(va)]
            spec_va_1g_valid(va) ==> 0 <= spec_v2l4index(va) < ENTRIES && 0 <= spec_v2l3index(va) < ENTRIES
                && 0 == spec_v2l2index(va) && 0 == spec_v2l1index(va),
        forall|
            l4i: L4Index,
            l3i: L3Index,
            l2i: L2Index,
            l1i: L1Index,
            l4j: L4Index,
            l3j: L3Index,
            l2j: L2Index,
            l1j: L1Index,
        |
            #![trigger spec_index2va((l4i,l3i,l2i,l1i)), spec_index2va((l4j,l3j,l2j,l1j))]
            0 <= l4i < ENTRIES && 0 <= l3i < ENTRIES && 0 <= l2i < ENTRIES && 0 <= l1i < ENTRIES && 0 <= l4j < ENTRIES
                && 0 <= l3j < ENTRIES && 0 <= l2j < ENTRIES && 0 <= l1j < ENTRIES ==> ((l4i, l3i, l2i, l1i) =~= (
                l4j,
                l3j,
                l2j,
                l1j,
            ) <==> spec_index2va((l4i, l3i, l2i, l1i)) == spec_index2va((l4j, l3j, l2j, l1j))),
        forall|
            l4i: L4Index,
            l3i: L3Index,
            l2i: L2Index,
            l1i: L1Index,
            l4j: L4Index,
            l3j: L3Index,
            l2j: L2Index,
            l1j: L1Index,
        |
            #![trigger spec_index2va((l4i,l3i,l2i,l1i)), spec_index2va((l4j,l3j,l2j,l1j))]
            0 <= l4i < ENTRIES && 0 <= l3i < ENTRIES && 0 <= l2i < ENTRIES && 0 <= l1i < ENTRIES && 0 <= l4j < ENTRIES
                && 0 <= l3j < ENTRIES && 0 <= l2j < ENTRIES && 0 <= l1j < ENTRIES ==> (((l4i, l3i, l2i, l1i) =~= (
                l4j,
                l3j,
                l2j,
                l1j,
            )) == false <==> spec_index2va((l4i, l3i, l2i, l1i)) != spec_index2va(
                (l4j, l3j, l2j, l1j),
            )),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger va_4k_valid(spec_index2va((l4i,l3i,l2i,l1i)))]
            KERNEL_MEM_END_L4INDEX <= l4i < ENTRIES && 0 <= l3i < ENTRIES && 0 <= l2i < ENTRIES && 0 <= l1i < ENTRIES ==> va_4k_valid(
                spec_index2va((l4i, l3i, l2i, l1i)),
            ),
        forall|va: VAddr, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger spec_index2va((l4i,l3i,l2i,l1i)), spec_va2index(va)]
            va_4k_valid(va) && spec_va2index(va) == (l4i, l3i, l2i, l1i) <==> KERNEL_MEM_END_L4INDEX
                <= l4i < ENTRIES && 0 <= l3i < ENTRIES && 0 <= l2i < ENTRIES && 0 <= l1i < ENTRIES && spec_index2va(
                (l4i, l3i, l2i, l1i),
            ) == va,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger va_2m_valid(spec_index2va((l4i,l3i,l2i,0)))]
            KERNEL_MEM_END_L4INDEX <= l4i < ENTRIES && 0 <= l3i < ENTRIES && 0 <= l2i < ENTRIES ==> va_2m_valid(
                spec_index2va((l4i, l3i, l2i, 0)),
            ),
{
    assert forall|va: VAddr|
        #![trigger spec_va_4k_valid(va), spec_v2l4index(va)]
        #![trigger spec_va_4k_valid(va), spec_v2l3index(va)]
        #![trigger spec_va_4k_valid(va), spec_v2l2index(va)]
        #![trigger spec_va_4k_valid(va), spec_v2l1index(va)]
        spec_va_4k_valid(va) implies 0 <= spec_v2l4index(va) < ENTRIES && 0 <= spec_v2l3index(va)
        < ENTRIES && 0 <= spec_v2l2index(va) < ENTRIES && 0 <= spec_v2l1index(va) < ENTRIES by {
        lemma_va_index_bounds(va);
    }
    assert forall|va: VAddr|
        #![trigger spec_va_2m_valid(va), spec_v2l4index(va)]
        #![trigger spec_va_2m_valid(va), spec_v2l3index(va)]
        #![trigger spec_va_2m_valid(va), spec_v2l2index(va)]
        #![trigger spec_va_2m_valid(va), spec_v2l1index(va)]
        spec_va_2m_valid(va) implies 0 <= spec_v2l4index(va) < ENTRIES && 0 <= spec_v2l3index(va)
        < ENTRIES && 0 <= spec_v2l2index(va) < ENTRIES && 0 == spec_v2l1index(va) by {
        lemma_va_index_bounds(va);
        lemma_va_2m_valid_l1index(va);
    }
    assert forall|va: VAddr|
        #![trigger spec_va_1g_valid(va), spec_v2l4index(va)]
        #![trigger spec_va_1g_valid(va), spec_v2l3index(va)]
        #![trigger spec_va_1g_valid(va), spec_v2l2index(va)]
        #![trigger spec_va_1g_valid(va), spec_v2l1index(va)]
        spec_va_1g_valid(va) implies 0 <= spec_v2l4index(va) < ENTRIES && 0 <= spec_v2l3index(va)
        < ENTRIES && 0 == spec_v2l2index(va) && 0 == spec_v2l1index(va) by {
        lemma_va_index_bounds(va);
        lemma_va_1g_valid_indices(va);
    }
    assert forall|
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
        l1i: L1Index,
        l4j: L4Index,
        l3j: L3Index,
        l2j: L2Index,
        l1j: L1Index,
    |
        #![trigger spec_index2va((l4i,l3i,l2i,l1i)), spec_index2va((l4j,l3j,l2j,l1j))]
        0 <= l4i < ENTRIES && 0 <= l3i < ENTRIES && 0 <= l2i < ENTRIES && 0 <= l1i < ENTRIES && 0 <= l4j < ENTRIES
            && 0 <= l3j < ENTRIES && 0 <= l2j < ENTRIES && 0 <= l1j < ENTRIES implies ((l4i, l3i, l2i, l1i)
            =~= (l4j, l3j, l2j, l1j) <==> spec_index2va((l4i, l3i, l2i, l1i)) == spec_index2va(
            (l4j, l3j, l2j, l1j),
        )) && (((l4i, l3i, l2i, l1i) =~= (l4j, l3j, l2j, l1j)) == false <==> spec_index2va(
            (l4i, l3i, l2i, l1i),
        ) != spec_index2va((l4j, l3j, l2j, l1j))) by {
        lemma_index2va_injective(l4i, l3i, l2i, l1i, l4j, l3j, l2j, l1j);
    }
    assert forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
        #![trigger va_4k_valid(spec_index2va((l4i,l3i,l2i,l1i)))]
        KERNEL_MEM_END_L4INDEX <= l4i < ENTRIES && 0 <= l3i < ENTRIES && 0 <= l2i < ENTRIES && 0 <= l1i
            < ENTRIES implies va_4k_valid(spec_index2va((l4i, l3i, l2i, l1i))) by {
        lemma_index2va_4k_valid(l4i, l3i, l2i, l1i);
    }
    assert forall|va: VAddr, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
        #![trigger spec_index2va((l4i,l3i,l2i,l1i)), spec_va2index(va)]
        (va_4k_valid(va) && spec_va2index(va) == (l4i, l3i, l2i, l1i)) <==> (
        KERNEL_MEM_END_L4INDEX <= l4i < ENTRIES && 0 <= l3i < ENTRIES && 0 <= l2i < ENTRIES && 0 <= l1i < ENTRIES
            && spec_index2va((l4i, l3i, l2i, l1i)) == va) by {
        if spec_va_4k_valid(va) {
            lemma_va_index_bounds(va);
            lemma_va_4k_valid_l4index(va);
            lemma_va2index_index2va(va);
        }
        if KERNEL_MEM_END_L4INDEX <= l4i < ENTRIES && l3i < ENTRIES && l2i < ENTRIES && l1i < ENTRIES {
            lemma_index2va_4k_valid(l4i, l3i, l2i, l1i);
            lemma_index2va_fields(l4i, l3i, l2i, l1i);
        }
    }
    assert forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
        #![trigger va_2m_valid(spec_index2va((l4i,l3i,l2i,0)))]
        KERNEL_MEM_END_L4INDEX <= l4i < ENTRIES && 0 <= l3i < ENTRIES && 0 <= l2i < ENTRIES implies va_2m_valid(
        spec_index2va((l4i, l3i, l2i, 0)),
    ) by {
        lemma_index2va_2m_valid(l4i, l3i, l2i);
    }
}

} // verus!
