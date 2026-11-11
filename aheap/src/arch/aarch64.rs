// SPDX-License-Identifier: MIT

//! aarch64's page and block with the 4K granule: the 4 KiB page a level 3 descriptor maps and the
//! 2 MiB block a level 2 descriptor maps, Arm ARM D8.2 and D8.3.1.
use vstd::prelude::*;

use crate::buddy::BlockBuddy;

verus! {

/// The smallest page the translation maps.
pub const PAGE_BYTES: usize = 4096;

/// The pages one block holds: the descriptors of one table.
pub const BLOCK_PAGES: usize = 512;

/// The order of a block: BLOCK_PAGES is two to this power.
pub const BLOCK_ORDER: usize = 9;

/// The size one entry of the level above the leaf maps, which a span is a whole number of.
pub const BLOCK_BYTES: usize = PAGE_BYTES * BLOCK_PAGES;

// The block buddy's record: one tag byte per page of a block, and ghost state only.
global layout BlockBuddy is size == 512, align == 1;

/// The block buddy's record is a byte per page of a block, which the layout directive above states
/// only to this module.
pub proof fn lemma_block_buddy_layout()
    ensures
        vstd::layout::size_of::<BlockBuddy>() == BLOCK_PAGES,
        vstd::layout::align_of::<BlockBuddy>() == 1,
{
}

} // verus!
