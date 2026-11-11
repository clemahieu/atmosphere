// SPDX-License-Identifier: MIT

//! aarch64's page and block with the 4K granule: the 4 KiB page a level 3 descriptor maps and the
//! 2 MiB block a level 2 descriptor maps, Arm ARM D8.2 and D8.3.1.
use vstd::prelude::*;

use crate::large::LargeNode;
use crate::page::Node;
use crate::record::{PageHeader, Record};

verus! {

/// The smallest page the translation maps.
pub const PAGE_BYTES: usize = 4096;

/// The pages one block holds: the descriptors of one table.
pub const BLOCK_PAGES: usize = 512;

/// The order of a block: BLOCK_PAGES is two to this power.
pub const BLOCK_ORDER: usize = 9;

/// The size one entry of the level above the leaf maps, which a span is a whole number of.
pub const BLOCK_BYTES: usize = PAGE_BYTES * BLOCK_PAGES;

// A run span's node: the base of the next span, and its two block buddies' records of one tag byte
// per page of a block each.
global layout Node is size == 1032, align == 8;

/// A run span's node is a word and two bytes per page of a block, word-aligned, which the layout
/// directive above states only to this module.
pub proof fn lemma_node_layout()
    ensures
        vstd::layout::size_of::<Node>() == 2 * BLOCK_PAGES + 8,
        vstd::layout::align_of::<Node>() == 8,
{
}

// A large object's node: the record page of the next large object, the object's base and its pages.
global layout LargeNode is size == 24, align == 8;

/// A large object's node is three words, word-aligned, which the layout directive above states only
/// to this module.
pub proof fn lemma_large_node_layout()
    ensures
        vstd::layout::size_of::<LargeNode>() == 24,
        vstd::layout::align_of::<LargeNode>() == 8,
{
}

/// The size classes the heap's slabs are cut into: eight multiples of the smallest slot, then four
/// for each doubling of the slot size up to the page; lemma_class shows the last is the page.
pub const CLASSES: usize = 28;

/// The bytes of a record page's header: the next record page and the bitmap of its records in use.
pub const HEADER_BYTES: usize = 16;

/// The bytes of one slab's record: the slab and the links of its class's list.
pub const RECORD_BYTES: usize = 88;

/// The records one record page holds after its header.
pub const PAGE_RECORDS: usize = 46;

// A record page's header: the next record page, and one bit per record of the page in use.
global layout PageHeader is size == 16, align == 8;

// A slab's record: the slab, of a pointer, four words and a bitmap of four words, and two links.
global layout Record is size == 88, align == 8;

/// A record page's header and a record are two and eleven words, word-aligned, which the layout
/// directives above state only to this module, and a page holds the header and PAGE_RECORDS records,
/// no more than its header's bitmap has bits for.
pub proof fn lemma_record_layout()
    ensures
        vstd::layout::size_of::<PageHeader>() == HEADER_BYTES,
        vstd::layout::align_of::<PageHeader>() == 8,
        vstd::layout::size_of::<Record>() == RECORD_BYTES,
        vstd::layout::align_of::<Record>() == 8,
        HEADER_BYTES + PAGE_RECORDS * RECORD_BYTES <= PAGE_BYTES,
        0 < PAGE_RECORDS <= 64,
{
}

} // verus!
