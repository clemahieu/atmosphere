// SPDX-License-Identifier: MIT

use vstd::prelude::*;

verus! {

use crate::pptr::*;

pub type PagePtr = usize;

pub type PagePerm4k = PointsTo<[u8; PAGE_SZ]>;

pub type VAddr = usize;

pub type PAddr = usize;

pub type PageMapPtr = usize;

//1 for now
pub const KERNEL_MEM_END_L4INDEX: usize = 1;

/// Pages the compile-time tables cover. design/page-metadata-sized-from-the-memory-map/.
pub const NUM_PAGES: usize = 1024 * 1024;

/// Bytes in a page. Every page-shaped size below is written from this and ENTRIES, so the granule is
/// one definition. design/arch-module/.
pub const PAGE_SZ: usize = 4096;

/// Entries in one page table level: a table is one page of 8-byte entries.
pub const ENTRIES: usize = 512;

/// The offset of an address within its page.
pub const PAGE_MASK: usize = PAGE_SZ - 1;

/// A table index's bits: an index is at most this.
pub const INDEX_MASK: usize = ENTRIES - 1;

/// The bits of an address below its page: PAGE_SZ is 1 << PAGE_SHIFT (lemma_shifts).
pub const PAGE_SHIFT: usize = 12;

/// The bits of one table index: ENTRIES is 1 << INDEX_BITS (lemma_shifts).
pub const INDEX_BITS: usize = 9;

/// Where each level's index starts in an address, the level-1 table's lowest.
pub const L1_SHIFT: usize = PAGE_SHIFT;
pub const L2_SHIFT: usize = L1_SHIFT + INDEX_BITS;
pub const L3_SHIFT: usize = L2_SHIFT + INDEX_BITS;
pub const L4_SHIFT: usize = L3_SHIFT + INDEX_BITS;

/// The pages a level-2 entry maps: a 2M region at the 4K granule.
pub const PAGES_PER_2M: usize = ENTRIES;

/// The pages a level-3 entry maps: a 1G region at the 4K granule.
pub const PAGES_PER_1G: usize = ENTRIES * ENTRIES;

/// The bytes a level-2, level-3 and level-4 entry map.
pub const SIZE_2M: usize = PAGE_SZ * PAGES_PER_2M;
pub const SIZE_1G: usize = PAGE_SZ * PAGES_PER_1G;
pub const SIZE_512G: usize = SIZE_1G * ENTRIES;

/// The shifts and the sizes name the same numbers.
pub proof fn lemma_shifts()
    ensures
        PAGE_SZ == 1usize << PAGE_SHIFT,
        ENTRIES == 1usize << INDEX_BITS,
        SIZE_2M == 1usize << L2_SHIFT,
        SIZE_1G == 1usize << L3_SHIFT,
        SIZE_512G == 1usize << L4_SHIFT,
{
    assert(PAGE_SZ == 1usize << PAGE_SHIFT) by (compute_only);
    assert(ENTRIES == 1usize << INDEX_BITS) by (compute_only);
    assert(SIZE_2M == 1usize << L2_SHIFT) by (compute_only);
    assert(SIZE_1G == 1usize << L3_SHIFT) by (compute_only);
    assert(SIZE_512G == 1usize << L4_SHIFT) by (compute_only);
}

pub const PCID_MAX: usize = 4096;

pub const NUM_CPUS: usize = 32;
pub const NUM_IOMMUS: usize = 8;

} // verus!
