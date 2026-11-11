// SPDX-License-Identifier: MIT

//! x86_64's page and block: the 4 KiB page and the 2 MiB page a page-directory entry maps, Intel SDM
//! Volume 3A, section 4.5, and AMD APM Volume 2, section 5.3.
use vstd::prelude::*;

use crate::page::Node;

verus! {

/// The smallest page the translation maps.
pub const PAGE_BYTES: usize = 4096;

/// The pages one block holds: the entries of one table.
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

} // verus!
