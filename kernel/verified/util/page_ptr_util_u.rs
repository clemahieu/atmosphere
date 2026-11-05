use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::lemma::lemma_t::*;

pub open spec fn spec_page_index_merge_2m_vaild(i: usize, j: usize) -> bool
    recommends
        page_index_2m_valid(i),
{
    i < j < i + 0x200
}

pub open spec fn spec_page_index_merge_1g_vaild(i: usize, j: usize) -> bool
    recommends
        page_index_1g_valid(i),
{
    i < j < i + 0x40000
}

pub open spec fn spec_page_ptr2page_index(ptr: usize) -> usize
    recommends
        page_ptr_valid(ptr),
{
    (ptr / 4096usize) as usize
}

pub open spec fn spec_page_index2page_ptr(i: usize) -> usize
    recommends
        page_index_valid(i),
{
    (i * 4096) as usize
}

#[verifier(when_used_as_spec(spec_page_ptr2page_index))]
pub fn page_ptr2page_index(ptr: usize) -> (ret: usize)
    requires
        ptr % 0x1000 == 0,
    ensures
        ret == spec_page_ptr2page_index(ptr),
{
    return ptr / 4096usize;
}

#[verifier(when_used_as_spec(spec_page_index2page_ptr))]
pub fn page_index2page_ptr(i: usize) -> (ret: usize)
    requires
        0 <= i < NUM_PAGES,
    ensures
        ret == spec_page_index2page_ptr(i),
{
    proof {
        lemma_usize_u64(MAX_USIZE);
    }
    i * 4096usize
}

pub open spec fn page_index_2m_valid(i: usize) -> bool {
    &&& i % 512 == 0
    &&& 0 <= i < NUM_PAGES
}

pub open spec fn page_index_1g_valid(i: usize) -> bool {
    &&& i % (512 * 512) as usize == 0
    &&& 0 <= i < NUM_PAGES
}

pub open spec fn MEM_valid(v: PAddr) -> bool {
    v & (!MEM_MASK) as usize == 0
}

pub open spec fn page_ptr_valid(ptr: usize) -> bool {
    &&& ptr % 0x1000 == 0
    &&& ptr / 0x1000 < NUM_PAGES
}

pub open spec fn page_index_valid(index: usize) -> bool {
    (0 <= index < NUM_PAGES)
}

pub open spec fn spec_page_index_truncate_2m(index: usize) -> usize {
    (index / 512usize * 512usize) as usize
}

pub open spec fn spec_page_index_truncate_1g(index: usize) -> usize {
    (index / 512usize / 512usize * 512usize * 512usize) as usize
}

pub open spec fn page_ptr_2m_valid(ptr: usize) -> bool {
    ((ptr % (0x200000)) == 0) && ((ptr / 4096) < NUM_PAGES)
}

pub open spec fn page_ptr_1g_valid(ptr: usize) -> bool {
    ((ptr % (0x40000000)) == 0) && ((ptr / 4096) < NUM_PAGES)
}

#[verifier(when_used_as_spec(spec_va_4k_valid))]
pub fn va_4k_valid(va: usize) -> (ret: bool)
    ensures
        ret == spec_va_4k_valid(va),
{
    (va & (!MEM_4k_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_va_4k_range_valid(va: usize, len: usize) -> bool {
    forall|i: usize|
        #![trigger spec_va_add_range(va, i)]
        0 <= i < len ==> spec_va_4k_valid(spec_va_add_range(va, i))
}

#[verifier(when_used_as_spec(spec_va_4k_range_valid))]
pub fn va_4k_range_valid(va: usize, len: usize) -> (ret: bool)
    requires
        va_4k_valid(va),
    ensures
        spec_va_4k_range_valid(va, len) == ret,
{
    for idx in iter: 0..len
        invariant
            va_4k_valid(va),
            forall|i: usize|
                #![trigger spec_va_add_range(va, i)]
                0 <= i < idx ==> spec_va_4k_valid(spec_va_add_range(va, i)),
    {
        proof {
            lemma_va_4k_range_bound(va, idx);
        }
        if va_4k_valid(va_add_range(va, idx)) == false {
            return false;
        }
    }
    true
}

pub open spec fn spec_va_4k_valid(va: usize) -> bool {
    (va & (!MEM_4k_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

#[verifier(when_used_as_spec(spec_va_2m_valid))]
pub fn va_2m_valid(va: usize) -> (ret: bool)
    ensures
        ret == spec_va_2m_valid(va),
{
    (va & (!MEM_2m_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_va_2m_valid(va: usize) -> bool {
    (va & (!MEM_2m_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

#[verifier(when_used_as_spec(spec_va_1g_valid))]
pub fn va_1g_valid(va: usize) -> (ret: bool)
    ensures
        ret == spec_va_1g_valid(va),
{
    (va & (!MEM_1g_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_va_1g_valid(va: usize) -> bool {
    (va & (!MEM_1g_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
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

pub open spec fn spec_va22mindex(va: usize) -> (L4Index, L3Index, L2Index) {
    (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
}

pub open spec fn spec_va21gindex(va: usize) -> (L4Index, L3Index) {
    (spec_v2l4index(va), spec_v2l3index(va))
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
    assert((!MEM_4k_MASK) as usize == (!0x0000_ffff_ffff_f000u64) as usize);
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
    assert((!MEM_2m_MASK) as usize == (!0x0000_ffff_ffe0_0000u64) as usize);
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
    assert((!MEM_2m_MASK) as usize == (!0x0000_ffff_ffe0_0000u64) as usize);
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
    assert((!MEM_1g_MASK) as usize == (!0x0000_fffc_0000_0000u64) as usize);
    assert(va & (!0x0000_fffc_0000_0000u64) as usize == 0 ==> (va >> 21 & 0x1ff) == 0 && (va
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
    assert((!MEM_4k_MASK) as usize == (!0x0000_ffff_ffff_f000u64) as usize);
    assert(va & (!0x0000_ffff_ffff_f000u64) as usize == 0 ==> ((va >> 39 & 0x1ff) << 39 | (va
        >> 30 & 0x1ff) << 30 | (va >> 21 & 0x1ff) << 21 | (va >> 12 & 0x1ff) << 12) == va)
        by (bit_vector);
}

#[verifier(when_used_as_spec(spec_v2l1index))]
pub fn v2l1index(va: usize) -> (ret: L1Index)
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret == spec_v2l1index(va),
        ret <= 0x1ff,
{
    assert((va as u64 >> 12u64 & 0x1ffu64) as usize <= 0x1ff) by (bit_vector);
    (va as u64 >> 12u64 & 0x1ffu64) as usize
}

#[verifier(when_used_as_spec(spec_v2l2index))]
pub fn v2l2index(va: usize) -> (ret: L2Index)
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret == spec_v2l2index(va),
        ret <= 0x1ff,
{
    assert((va as u64 >> 21u64 & 0x1ffu64) as usize <= 0x1ff) by (bit_vector);
    (va as u64 >> 21u64 & 0x1ffu64) as usize
}

#[verifier(when_used_as_spec(spec_v2l3index))]
pub fn v2l3index(va: usize) -> (ret: L3Index)
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret == spec_v2l3index(va),
        ret <= 0x1ff,
{
    assert((va as u64 >> 30u64 & 0x1ffu64) as usize <= 0x1ff) by (bit_vector);
    (va as u64 >> 30u64 & 0x1ffu64) as usize
}

#[verifier(when_used_as_spec(spec_v2l4index))]
pub fn v2l4index(va: usize) -> (ret: L4Index)
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret == spec_v2l4index(va),
        KERNEL_MEM_END_L4INDEX <= ret <= 0x1ff,
{
    assert((va as u64 >> 39u64 & 0x1ffu64) as usize <= 0x1ff) by (bit_vector);
    (va as u64 >> 39u64 & 0x1ffu64) as usize
}

pub fn va21gindex(va: usize) -> (ret: (L4Index, L3Index))
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret.0 == spec_v2l4index(va) && KERNEL_MEM_END_L4INDEX <= ret.0 <= 0x1ff,
        ret.1 == spec_v2l3index(va) && ret.1 <= 0x1ff,
        ret == spec_va21gindex(va),
{
    (v2l4index(va), v2l3index(va))
}

pub fn va22mindex(va: usize) -> (ret: (L4Index, L3Index, L2Index))
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret.0 == spec_v2l4index(va) && KERNEL_MEM_END_L4INDEX <= ret.0 <= 0x1ff,
        ret.1 == spec_v2l3index(va) && ret.1 <= 0x1ff,
        ret.2 == spec_v2l2index(va) && ret.2 <= 0x1ff,
        ret == spec_va22mindex(va),
{
    (v2l4index(va), v2l3index(va), v2l2index(va))
}

pub fn va2index(va: usize) -> (ret: (L4Index, L3Index, L2Index, L1Index))
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret.0 == spec_v2l4index(va) && KERNEL_MEM_END_L4INDEX <= ret.0 <= 0x1ff,
        ret.1 == spec_v2l3index(va) && ret.1 <= 0x1ff,
        ret.2 == spec_v2l2index(va) && ret.2 <= 0x1ff,
        ret.3 == spec_v2l1index(va) && ret.3 <= 0x1ff,
        ret == spec_va2index(va),
{
    (v2l4index(va), v2l3index(va), v2l2index(va), v2l1index(va))
}

pub open spec fn spec_va_add_range(va: usize, i: usize) -> usize {
    (va + (i * 4096)) as usize
}

pub fn va_add_range(va: usize, i: usize) -> (ret: usize)
    requires
        va + i * 4096 <= usize::MAX,
    ensures
        ret == spec_va_add_range(va, i),
        i != 0 ==> ret != va,
{
    (va + (i * 4096)) as usize
}

/// A valid 4k address is page aligned and below the 48-bit boundary.
pub proof fn lemma_va_4k_valid_bounds(va: usize)
    requires
        spec_va_4k_valid(va),
    ensures
        va % 4096 == 0,
        va < 0x1_0000_0000_0000,
{
    assert((!MEM_4k_MASK) as usize == (!0x0000_ffff_ffff_f000u64) as usize);
    assert(va & (!0x0000_ffff_ffff_f000u64) as usize == 0 ==> va % 4096 == 0 && va
        < 0x1_0000_0000_0000) by (bit_vector);
}

/// A valid 4k range of len pages from a valid 4k address ends at or before the 48-bit
/// boundary: the page at that boundary is not a valid address, so no page of the range is
/// it or past it, and no page of the range wraps.
pub proof fn lemma_va_4k_range_bound(va: usize, len: usize)
    requires
        spec_va_4k_valid(va),
        spec_va_4k_range_valid(va, len),
    ensures
        va + len * 4096 <= 0x1_0000_0000_0000,
{
    lemma_va_4k_valid_bounds(va);
    if va + len * 4096 > 0x1_0000_0000_0000 {
        let k = ((0x1_0000_0000_0000 - va) / 4096) as usize;
        assert(k * 4096 == 0x1_0000_0000_0000 - va);
        assert(k < len);
        assert(spec_va_add_range(va, k) == 0x1_0000_0000_0000usize);
        assert(0x1_0000_0000_0000usize & (!0x0000_ffff_ffff_f000u64) as usize != 0)
            by (bit_vector);
        assert((!MEM_4k_MASK) as usize == (!0x0000_ffff_ffff_f000u64) as usize);
        assert(!spec_va_4k_valid(0x1_0000_0000_0000usize));
    }
}

/// The converse of lemma_va_4k_range_bound: a valid start whose range ends at or before the 48-bit
/// boundary has every page valid.
pub proof fn lemma_va_4k_range_fits(va: usize, len: usize)
    requires
        spec_va_4k_valid(va),
        va + len * 4096 <= 0x1_0000_0000_0000,
    ensures
        spec_va_4k_range_valid(va, len),
{
    lemma_va_4k_valid_bounds(va);
    assert((!MEM_4k_MASK) as usize == (!0x0000_ffff_ffff_f000u64) as usize);
    assert(KERNEL_MEM_END_L4INDEX as u64 == 1u64);
    assert forall|i: usize|
        #![trigger spec_va_add_range(va, i)]
        0 <= i < len implies spec_va_4k_valid(spec_va_add_range(va, i)) by {
        assert(i * 4096 < len * 4096);
        let page = spec_va_add_range(va, i);
        assert(page == va + i * 4096);
        assert(page % 4096 == 0 && va <= page && page < 0x1_0000_0000_0000);
        assert(va & (!0x0000_ffff_ffff_f000u64) as usize == 0
            && (va as u64 >> 39u64 & 0x1ffu64) >= 1u64
            && page % 4096 == 0 && va <= page && page < 0x1_0000_0000_0000usize
            ==> page & (!0x0000_ffff_ffff_f000u64) as usize == 0
            && (page as u64 >> 39u64 & 0x1ffu64) >= 1u64) by (bit_vector);
    }
}

pub proof fn va_range_lemma()
    ensures
        forall|va: VAddr, len: usize, i: usize, j: usize|
            #![trigger spec_va_4k_range_valid(va,len), spec_va_add_range(va, i), spec_va_add_range(va, j)]
            va_4k_valid(va) && spec_va_4k_range_valid(va, len) && 0 <= i < len && 0 <= j < len ==> (
            (i == j) == (spec_va_add_range(va, i) == spec_va_add_range(va, j))),
{
    assert forall|va: VAddr, len: usize, i: usize, j: usize|
        #![trigger spec_va_4k_range_valid(va,len), spec_va_add_range(va, i), spec_va_add_range(va, j)]
        va_4k_valid(va) && spec_va_4k_range_valid(va, len) && 0 <= i < len && 0 <= j
            < len implies ((i == j) == (spec_va_add_range(va, i) == spec_va_add_range(
        va,
        j,
    ))) by {
        lemma_va_4k_range_bound(va, len);
        assert(spec_va_add_range(va, i) == va + i * 4096);
        assert(spec_va_add_range(va, j) == va + j * 4096);
    }
}

pub proof fn page_index_lemma()
    ensures
        forall|i: usize, j: usize|
            #![trigger spec_page_index_merge_2m_vaild(i, j)]
            #![trigger page_index_2m_valid(i), page_index_valid(j)]
            page_index_2m_valid(i) && spec_page_index_merge_2m_vaild(i, j) ==> page_index_valid(j),
        forall|i: usize, j: usize|
            #![trigger spec_page_index_merge_1g_vaild(i, j)]
            #![trigger page_index_2m_valid(i), page_index_valid(j)]
            page_index_1g_valid(i) && spec_page_index_merge_1g_vaild(i, j) ==> page_index_valid(j),
{
    assert forall|i: usize, j: usize|
        #![trigger spec_page_index_merge_1g_vaild(i, j)]
        #![trigger page_index_2m_valid(i), page_index_valid(j)]
        page_index_1g_valid(i) && spec_page_index_merge_1g_vaild(i, j) implies page_index_valid(
        j,
    ) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i as int, 0x40000);
        assert(i as int / 0x40000 < 8);
    }
}

pub proof fn page_ptr_page_index_truncate_lemma()
    ensures
        forall|pi: usize, i: usize|
            #![trigger page_index_1g_valid(pi), spec_page_index_truncate_1g(i)]
            page_index_1g_valid(pi) ==> ((pi <= i < pi + 0x40000) <==> spec_page_index_truncate_1g(i)
                == spec_page_index_truncate_1g(pi)),
        forall|pi: usize, i: usize|
            #![trigger page_index_1g_valid(pi), spec_page_index_truncate_1g(i)]
            page_index_1g_valid(pi) && (pi <= i < pi + 0x40000) ==> page_index_1g_valid(
                spec_page_index_truncate_1g(i),
            ),
        forall|pi: usize, i: usize|
            #![trigger page_index_2m_valid(pi), spec_page_index_truncate_2m(i)]
            page_index_2m_valid(pi) ==> ((pi <= i < pi + 0x200) <==> spec_page_index_truncate_2m(i)
                == spec_page_index_truncate_2m(pi)),
        forall|pi: usize, i: usize|
            #![trigger page_index_2m_valid(pi), spec_page_index_truncate_2m(i)]
            page_index_2m_valid(pi) && (pi <= i < pi + 0x200) ==> page_index_2m_valid(
                spec_page_index_truncate_2m(i),
            ),
        forall|i: usize, j: usize|
            #![trigger spec_page_index_truncate_1g(i), spec_page_index_truncate_1g(j)]
            spec_page_index_truncate_1g(i) != spec_page_index_truncate_1g(j) ==> i != j,
        forall|i: usize, j: usize|
            #![trigger spec_page_index_truncate_2m(i), spec_page_index_truncate_2m(j)]
            spec_page_index_truncate_2m(i) != spec_page_index_truncate_2m(j) ==> i != j,
{
    assert forall|pi: usize, i: usize|
        #![trigger page_index_1g_valid(pi), spec_page_index_truncate_1g(i)]
        page_index_1g_valid(pi) implies ((pi <= i < pi + 0x40000) <==> spec_page_index_truncate_1g(
        i,
    ) == spec_page_index_truncate_1g(pi)) by {
        lemma_page_index_truncate_1g_is_div(i);
        lemma_page_index_truncate_1g_is_div(pi);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i as int, 0x40000);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(pi as int, 0x40000);
    }
}

proof fn lemma_page_index_truncate_1g_is_div(i: usize)
    ensures
        spec_page_index_truncate_1g(i) == (i as int / 0x40000) * 0x40000,
        (i as int / 0x40000) * 0x40000 <= i,
{
    vstd::arithmetic::div_mod::lemma_div_denominator(i as int, 512, 512);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i as int, 0x40000);
}

pub proof fn page_ptr_lemma1()
    ensures
        forall|pa: PagePtr|
            #![trigger page_ptr_valid(pa)]
            #![trigger page_ptr2page_index(pa)]
            page_ptr_valid(pa) ==> page_index_valid(page_ptr2page_index(pa)),
        forall|pa: PagePtr|
            #![trigger page_ptr_valid(pa)]
            #![trigger page_ptr2page_index(pa)]
            page_ptr_valid(pa) ==> pa == page_index2page_ptr(page_ptr2page_index(pa)),
        forall|i: usize|
            #![trigger page_index_valid(i)]
            #![trigger page_index2page_ptr(i)]
            page_index_valid(i) ==> i == page_ptr2page_index(page_index2page_ptr(i)),
        forall|pi: usize, pj: usize|
            #![trigger page_ptr_valid(pi), page_ptr_valid(pj), page_ptr2page_index(pi), page_ptr2page_index(pj)]
            page_ptr_valid(pi) && page_ptr_valid(pj) && pi != pj ==> page_ptr2page_index(pi)
                != page_ptr2page_index(pj),
        forall|i: usize, j: usize|
            #![trigger page_index2page_ptr(i), page_index2page_ptr(j)]
            0 < i < NUM_PAGES && 0 < j < NUM_PAGES && i != j ==> page_index2page_ptr(i)
                != page_index2page_ptr(j),
{
}

pub proof fn page_ptr_2m_lemma()
    ensures
        forall|pa: PagePtr|
            #![trigger page_ptr_2m_valid(pa)]
            #![trigger page_ptr_valid(pa)]
            page_ptr_2m_valid(pa) ==> page_ptr_valid(pa),
        forall|i: usize|
            #![trigger page_index_2m_valid(i)]
            #![trigger page_index_valid(i)]
            page_index_2m_valid(i) ==> page_index_valid(i),
        forall|pa: PagePtr|
            #![trigger page_ptr_2m_valid(pa)]
            #![trigger page_ptr2page_index(pa)]
            page_ptr_2m_valid(pa) ==> page_index_2m_valid(page_ptr2page_index(pa)),
{
}

pub proof fn page_ptr_1g_lemma()
    ensures
        forall|pa: PagePtr|
            #![trigger page_ptr_valid(pa)]
            #![trigger page_ptr_1g_valid(pa)]
            page_ptr_1g_valid(pa) ==> page_ptr_valid(pa),
        forall|i: usize|
            #![trigger page_index_1g_valid(i)]
            #![trigger page_index_valid(i)]
            page_index_1g_valid(i) ==> page_index_valid(i),
        forall|pa: PagePtr|
            #![trigger page_ptr_1g_valid(pa)]
            #![trigger page_ptr2page_index(pa)]
            page_ptr_1g_valid(pa) ==> page_index_1g_valid(page_ptr2page_index(pa)),
{
    assert forall|pa: PagePtr|
        #![trigger page_ptr_1g_valid(pa)]
        #![trigger page_ptr2page_index(pa)]
        page_ptr_1g_valid(pa) implies page_index_1g_valid(page_ptr2page_index(pa)) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(pa as int, 0x40000000);
        let q = pa as int / 0x40000000;
        assert(pa as int == 4096 * (0x40000 * q));
        vstd::arithmetic::div_mod::lemma_div_multiples_vanish(0x40000 * q, 4096);
        assert(pa as int / 4096 == 0x40000 * q);
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q, 0x40000);
    }
}

// #[verifier(external_body)]
// pub proof fn page_ptr_2m_lemma()
//     ensures
//         forall|pa:PagePtr|
//             #![trigger page_ptr_2m_valid(pa)]
//             #![trigger page_ptr_valid(pa)]
//             page_ptr_2m_valid(pa) ==> page_ptr_valid(pa),
//         forall|i:usize|
//             #![trigger page_index_2m_valid(i)]
//             #![trigger page_index_valid(i)]
//             page_index_2m_valid(i) ==> page_index_valid(i),
//         forall|pa:PagePtr|
//             #![trigger page_ptr_2m_valid(pa)]
//             #![trigger page_ptr2page_index(pa)]
//             page_ptr_2m_valid(pa) ==> page_index_2m_valid(page_ptr2page_index(pa)),
// {
// }
// #[verifier(external_body)]
// pub proof fn page_ptr_lemma()
//     ensures
//         forall|pa:PagePtr|
//             #![trigger page_ptr_2m_valid(pa)]
//             #![trigger page_ptr_1g_valid(pa)]
//             page_ptr_1g_valid(pa) ==> page_ptr_2m_valid(pa),
//         forall|pa:PagePtr|
//             #![trigger page_ptr_2m_valid(pa)]
//             #![trigger page_ptr_valid(pa)]
//             page_ptr_2m_valid(pa) ==> page_ptr_valid(pa),
//         forall|i:usize|
//             #![trigger page_index_1g_valid(i)]
//             #![trigger page_index_2m_valid(i)]
//             page_index_1g_valid(i) ==> page_index_2m_valid(i),
//         forall|i:usize|
//             #![trigger page_index_2m_valid(i)]
//             #![trigger page_index_valid(i)]
//             page_index_2m_valid(i) ==> page_index_valid(i),
//         forall|pa:PagePtr|
//             #![trigger page_ptr_1g_valid(pa)]
//             #![trigger page_ptr2page_index(pa)]
//             page_ptr_1g_valid(pa) ==> page_index_1g_valid(page_ptr2page_index(pa)),
//         forall|pa:PagePtr|
//             #![trigger page_ptr_2m_valid(pa)]
//             #![trigger page_ptr2page_index(pa)]
//             page_ptr_2m_valid(pa) ==> page_index_2m_valid(page_ptr2page_index(pa)),
//         forall|pa:PagePtr|
//             #![trigger page_ptr_valid(pa)]
//             #![trigger page_ptr2page_index(pa)]
//             page_ptr_valid(pa) ==> page_index_valid(page_ptr2page_index(pa)),
//         forall|pa:PagePtr|
//             #![trigger page_ptr_valid(pa)]
//             #![trigger page_ptr2page_index(pa)]
//             page_ptr_valid(pa) ==> pa == page_index2page_ptr(page_ptr2page_index(pa)),
//         forall|i:usize|
//             #![trigger page_index_valid(i)]
//             #![trigger page_index2page_ptr(i)]
//             page_index_valid(i) ==> i == page_ptr2page_index(page_index2page_ptr(i)),
//         forall|i:usize, j:usize|
//             #![trigger page_index2page_ptr(i), page_index2page_ptr(j)]
//             0<i<NUM_PAGES && 0<j<NUM_PAGES && i != j
//             ==>
//                 page_index2page_ptr(i) != page_index2page_ptr(j),
// {
// }
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
