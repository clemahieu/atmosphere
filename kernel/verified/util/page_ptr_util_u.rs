use vstd::prelude::*;
verus! {

use crate::arch::{MEM_2M_MASK, MEM_4K_MASK};
#[cfg(verus_keep_ghost)]
use crate::arch::{MEM_1G_MASK, MEM_MASK};
use crate::define::*;

pub open spec fn MEM_valid(v: PAddr) -> bool {
    v & (!MEM_MASK) as usize == 0
}

#[verifier(when_used_as_spec(spec_va_4k_valid))]
pub fn va_4k_valid(va: usize) -> (ret: bool)
    ensures
        ret == spec_va_4k_valid(va),
{
    (va & (!MEM_4K_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_va_4k_valid(va: usize) -> bool {
    (va & (!MEM_4K_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

#[verifier(when_used_as_spec(spec_va_2m_valid))]
pub fn va_2m_valid(va: usize) -> (ret: bool)
    ensures
        ret == spec_va_2m_valid(va),
{
    (va & (!MEM_2M_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_va_2m_valid(va: usize) -> bool {
    (va & (!MEM_2M_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_va_1g_valid(va: usize) -> bool {
    (va & (!MEM_1G_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_v2l1index(va: usize) -> L1Index {
    (va >> 12 & 0x1ff) as usize
}

pub open spec fn spec_v2l2index(va: usize) -> L2Index {
    (va >> 21 & 0x1ff) as usize
}

pub open spec fn spec_v2l3index(va: usize) -> L3Index {
    (va >> 30 & 0x1ff) as usize
}

pub open spec fn spec_v2l4index(va: usize) -> L4Index {
    (va >> 39 & 0x1ff) as usize
}

pub open spec fn spec_va2index(va: usize) -> (L4Index, L3Index, L2Index, L1Index) {
    (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))
}

pub open spec fn spec_index2va(i: (L4Index, L3Index, L2Index, L1Index)) -> usize
    recommends
        i.0 <= 0x1ff,
        i.1 <= 0x1ff,
        i.2 <= 0x1ff,
        i.3 <= 0x1ff,
{
    (i.0 as usize) << 39 | (i.1 as usize) << 30 | (i.2 as usize) << 21 | (i.3 as usize) << 12
}

/// The address of an in-range index tuple whose L4 index is at or past the kernel's is a
/// valid 4k user address: page aligned, canonical and outside the kernel's L4 entries.
pub proof fn lemma_index2va_4k_valid(l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index)
    requires
        KERNEL_MEM_END_L4INDEX <= l4i < 512,
        0 <= l3i < 512,
        0 <= l2i < 512,
        0 <= l1i < 512,
    ensures
        spec_va_4k_valid(spec_index2va((l4i, l3i, l2i, l1i))),
{
    let va = spec_index2va((l4i, l3i, l2i, l1i));
    assert(va == l4i << 39 | l3i << 30 | l2i << 21 | l1i << 12);
    assert(1 <= l4i < 512 && l3i < 512 && l2i < 512 && l1i < 512 ==> ((l4i << 39 | l3i << 30
        | l2i << 21 | l1i << 12) & (!0x0000_ffff_ffff_f000u64) as usize == 0) && ((l4i << 39 | l3i
        << 30 | l2i << 21 | l1i << 12) as u64 >> 39u64 & 0x1ffu64) >= 1u64) by (bit_vector);
    assert((!MEM_4K_MASK) as usize == (!0x0000_ffff_ffff_f000u64) as usize);
    assert(KERNEL_MEM_END_L4INDEX as u64 == 1u64);
}

/// The address of an in-range index tuple with L1 index 0 whose L4 index is at or past the
/// kernel's is a valid 2m user address: 2m aligned, canonical and outside the kernel's L4 entries.
pub proof fn lemma_index2va_2m_valid(l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        KERNEL_MEM_END_L4INDEX <= l4i < 512,
        0 <= l3i < 512,
        0 <= l2i < 512,
    ensures
        spec_va_2m_valid(spec_index2va((l4i, l3i, l2i, 0))),
{
    let va = spec_index2va((l4i, l3i, l2i, 0));
    assert(va == l4i << 39 | l3i << 30 | l2i << 21 | 0usize << 12);
    assert(1 <= l4i < 512 && l3i < 512 && l2i < 512 ==> ((l4i << 39 | l3i << 30 | l2i << 21
        | 0usize << 12) & (!0x0000_ffff_ffe0_0000u64) as usize == 0) && ((l4i << 39 | l3i << 30
        | l2i << 21 | 0usize << 12) as u64 >> 39u64 & 0x1ffu64) >= 1u64) by (bit_vector);
    assert((!MEM_2M_MASK) as usize == (!0x0000_ffff_ffe0_0000u64) as usize);
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
        0 <= l4i < 512,
        0 <= l3i < 512,
        0 <= l2i < 512,
        0 <= l1i < 512,
        0 <= l4j < 512,
        0 <= l3j < 512,
        0 <= l2j < 512,
        0 <= l1j < 512,
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
        spec_v2l4index(va) < 512,
        spec_v2l3index(va) < 512,
        spec_v2l2index(va) < 512,
        spec_v2l1index(va) < 512,
{
    assert((va >> 39 & 0x1ff) < 512 && (va >> 30 & 0x1ff) < 512 && (va >> 21 & 0x1ff) < 512 && (
    va >> 12 & 0x1ff) < 512) by (bit_vector);
}

/// A valid 4k address is outside the kernel's L4 entries.
pub proof fn lemma_va_4k_valid_l4index(va: usize)
    requires
        spec_va_4k_valid(va),
    ensures
        KERNEL_MEM_END_L4INDEX <= spec_v2l4index(va),
{
    assert((va as u64 >> 39u64 & 0x1ffu64) >= 1u64 ==> (va >> 39 & 0x1ff) >= 1) by (bit_vector);
    assert(KERNEL_MEM_END_L4INDEX as u64 == 1u64);
}

/// A valid 2m address has L1 index zero.
pub proof fn lemma_va_2m_valid_l1index(va: usize)
    requires
        spec_va_2m_valid(va),
    ensures
        spec_v2l1index(va) == 0,
{
    assert((!MEM_2M_MASK) as usize == (!0x0000_ffff_ffe0_0000u64) as usize);
    assert(va & (!0x0000_ffff_ffe0_0000u64) as usize == 0 ==> (va >> 12 & 0x1ff) == 0)
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
    assert((!MEM_1G_MASK) as usize == (!0x0000_ffff_c000_0000u64) as usize);
    assert(va & (!0x0000_ffff_c000_0000u64) as usize == 0 ==> (va >> 21 & 0x1ff) == 0 && (va
        >> 12 & 0x1ff) == 0) by (bit_vector);
}

/// The address of an in-range index tuple decomposes back into that tuple.
pub proof fn lemma_index2va_fields(l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index)
    requires
        0 <= l4i < 512,
        0 <= l3i < 512,
        0 <= l2i < 512,
        0 <= l1i < 512,
    ensures
        spec_va2index(spec_index2va((l4i, l3i, l2i, l1i))) == (l4i, l3i, l2i, l1i),
{
    assert(l4i < 512 && l3i < 512 && l2i < 512 && l1i < 512 ==> ((l4i << 39 | l3i << 30 | l2i
        << 21 | l1i << 12) >> 39 & 0x1ff) == l4i && ((l4i << 39 | l3i << 30 | l2i << 21 | l1i
        << 12) >> 30 & 0x1ff) == l3i && ((l4i << 39 | l3i << 30 | l2i << 21 | l1i << 12) >> 21
        & 0x1ff) == l2i && ((l4i << 39 | l3i << 30 | l2i << 21 | l1i << 12) >> 12 & 0x1ff)
        == l1i) by (bit_vector);
}

/// A valid 4k address is the address of its own index tuple: it has no bits outside them.
pub proof fn lemma_va2index_index2va(va: usize)
    requires
        spec_va_4k_valid(va),
    ensures
        spec_index2va(spec_va2index(va)) == va,
{
    assert((!MEM_4K_MASK) as usize == (!0x0000_ffff_ffff_f000u64) as usize);
    assert(va & (!0x0000_ffff_ffff_f000u64) as usize == 0 ==> ((va >> 39 & 0x1ff) << 39 | (va
        >> 30 & 0x1ff) << 30 | (va >> 21 & 0x1ff) << 21 | (va >> 12 & 0x1ff) << 12) == va)
        by (bit_vector);
}

pub proof fn va_lemma()
    ensures
        forall|va: VAddr|
            #![trigger spec_va_4k_valid(va), spec_v2l4index(va)]
            #![trigger spec_va_4k_valid(va), spec_v2l3index(va)]
            #![trigger spec_va_4k_valid(va), spec_v2l2index(va)]
            #![trigger spec_va_4k_valid(va), spec_v2l1index(va)]
            spec_va_4k_valid(va) ==> 0 <= spec_v2l4index(va) < 512 && 0 <= spec_v2l3index(va) < 512
                && 0 <= spec_v2l2index(va) < 512 && 0 <= spec_v2l1index(va) < 512,
        forall|va: VAddr|
            #![trigger spec_va_2m_valid(va), spec_v2l4index(va)]
            #![trigger spec_va_2m_valid(va), spec_v2l3index(va)]
            #![trigger spec_va_2m_valid(va), spec_v2l2index(va)]
            #![trigger spec_va_2m_valid(va), spec_v2l1index(va)]
            spec_va_2m_valid(va) ==> 0 <= spec_v2l4index(va) < 512 && 0 <= spec_v2l3index(va) < 512
                && 0 <= spec_v2l2index(va) < 512 && 0 == spec_v2l1index(va),
        forall|va: VAddr|
            #![trigger spec_va_1g_valid(va), spec_v2l4index(va)]
            #![trigger spec_va_1g_valid(va), spec_v2l3index(va)]
            #![trigger spec_va_1g_valid(va), spec_v2l2index(va)]
            #![trigger spec_va_1g_valid(va), spec_v2l1index(va)]
            spec_va_1g_valid(va) ==> 0 <= spec_v2l4index(va) < 512 && 0 <= spec_v2l3index(va) < 512
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
            0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 && 0 <= l4j < 512
                && 0 <= l3j < 512 && 0 <= l2j < 512 && 0 <= l1j < 512 ==> ((l4i, l3i, l2i, l1i) =~= (
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
            0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 && 0 <= l4j < 512
                && 0 <= l3j < 512 && 0 <= l2j < 512 && 0 <= l1j < 512 ==> (((l4i, l3i, l2i, l1i) =~= (
                l4j,
                l3j,
                l2j,
                l1j,
            )) == false <==> spec_index2va((l4i, l3i, l2i, l1i)) != spec_index2va(
                (l4j, l3j, l2j, l1j),
            )),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger va_4k_valid(spec_index2va((l4i,l3i,l2i,l1i)))]
            KERNEL_MEM_END_L4INDEX <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 ==> va_4k_valid(
                spec_index2va((l4i, l3i, l2i, l1i)),
            ),
        forall|va: VAddr, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger spec_index2va((l4i,l3i,l2i,l1i)), spec_va2index(va)]
            va_4k_valid(va) && spec_va2index(va) == (l4i, l3i, l2i, l1i) <==> KERNEL_MEM_END_L4INDEX
                <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 && spec_index2va(
                (l4i, l3i, l2i, l1i),
            ) == va,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger va_2m_valid(spec_index2va((l4i,l3i,l2i,0)))]
            KERNEL_MEM_END_L4INDEX <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 ==> va_2m_valid(
                spec_index2va((l4i, l3i, l2i, 0)),
            ),
{
    assert forall|va: VAddr|
        #![trigger spec_va_4k_valid(va), spec_v2l4index(va)]
        #![trigger spec_va_4k_valid(va), spec_v2l3index(va)]
        #![trigger spec_va_4k_valid(va), spec_v2l2index(va)]
        #![trigger spec_va_4k_valid(va), spec_v2l1index(va)]
        spec_va_4k_valid(va) implies 0 <= spec_v2l4index(va) < 512 && 0 <= spec_v2l3index(va)
        < 512 && 0 <= spec_v2l2index(va) < 512 && 0 <= spec_v2l1index(va) < 512 by {
        lemma_va_index_bounds(va);
    }
    assert forall|va: VAddr|
        #![trigger spec_va_2m_valid(va), spec_v2l4index(va)]
        #![trigger spec_va_2m_valid(va), spec_v2l3index(va)]
        #![trigger spec_va_2m_valid(va), spec_v2l2index(va)]
        #![trigger spec_va_2m_valid(va), spec_v2l1index(va)]
        spec_va_2m_valid(va) implies 0 <= spec_v2l4index(va) < 512 && 0 <= spec_v2l3index(va)
        < 512 && 0 <= spec_v2l2index(va) < 512 && 0 == spec_v2l1index(va) by {
        lemma_va_index_bounds(va);
        lemma_va_2m_valid_l1index(va);
    }
    assert forall|va: VAddr|
        #![trigger spec_va_1g_valid(va), spec_v2l4index(va)]
        #![trigger spec_va_1g_valid(va), spec_v2l3index(va)]
        #![trigger spec_va_1g_valid(va), spec_v2l2index(va)]
        #![trigger spec_va_1g_valid(va), spec_v2l1index(va)]
        spec_va_1g_valid(va) implies 0 <= spec_v2l4index(va) < 512 && 0 <= spec_v2l3index(va)
        < 512 && 0 == spec_v2l2index(va) && 0 == spec_v2l1index(va) by {
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
        0 <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 && 0 <= l4j < 512
            && 0 <= l3j < 512 && 0 <= l2j < 512 && 0 <= l1j < 512 implies ((l4i, l3i, l2i, l1i)
            =~= (l4j, l3j, l2j, l1j) <==> spec_index2va((l4i, l3i, l2i, l1i)) == spec_index2va(
            (l4j, l3j, l2j, l1j),
        )) && (((l4i, l3i, l2i, l1i) =~= (l4j, l3j, l2j, l1j)) == false <==> spec_index2va(
            (l4i, l3i, l2i, l1i),
        ) != spec_index2va((l4j, l3j, l2j, l1j))) by {
        lemma_index2va_injective(l4i, l3i, l2i, l1i, l4j, l3j, l2j, l1j);
    }
    assert forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
        #![trigger va_4k_valid(spec_index2va((l4i,l3i,l2i,l1i)))]
        KERNEL_MEM_END_L4INDEX <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i
            < 512 implies va_4k_valid(spec_index2va((l4i, l3i, l2i, l1i))) by {
        lemma_index2va_4k_valid(l4i, l3i, l2i, l1i);
    }
    assert forall|va: VAddr, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
        #![trigger spec_index2va((l4i,l3i,l2i,l1i)), spec_va2index(va)]
        (va_4k_valid(va) && spec_va2index(va) == (l4i, l3i, l2i, l1i)) <==> (
        KERNEL_MEM_END_L4INDEX <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512
            && spec_index2va((l4i, l3i, l2i, l1i)) == va) by {
        if spec_va_4k_valid(va) {
            lemma_va_index_bounds(va);
            lemma_va_4k_valid_l4index(va);
            lemma_va2index_index2va(va);
        }
        if KERNEL_MEM_END_L4INDEX <= l4i < 512 && l3i < 512 && l2i < 512 && l1i < 512 {
            lemma_index2va_4k_valid(l4i, l3i, l2i, l1i);
            lemma_index2va_fields(l4i, l3i, l2i, l1i);
        }
    }
    assert forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
        #![trigger va_2m_valid(spec_index2va((l4i,l3i,l2i,0)))]
        KERNEL_MEM_END_L4INDEX <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 implies va_2m_valid(
        spec_index2va((l4i, l3i, l2i, 0)),
    ) by {
        lemma_index2va_2m_valid(l4i, l3i, l2i);
    }
}

} // verus!
