// SPDX-License-Identifier: MIT

//! aarch64's page and block with the 4K granule: the 4 KiB page a level 3 descriptor maps and the
//! 2 MiB block a level 2 descriptor maps, Arm ARM D8.2 and D8.3.1.
use vstd::prelude::*;

use crate::large::LargeNode;
use crate::page::Node;

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

} // verus!
