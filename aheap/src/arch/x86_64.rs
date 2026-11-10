//! x86_64's page and block: the 4 KiB page and the 2 MiB page a page-directory entry maps, Intel SDM
//! Volume 3A, section 4.5, and AMD APM Volume 2, section 5.3.
use vstd::prelude::*;

verus! {

/// The smallest page the translation maps.
pub const PAGE_BYTES: usize = 4096;

/// The pages one block holds: the entries of one table.
pub const BLOCK_PAGES: usize = 512;

/// The size one entry of the level above the leaf maps, which a span is a whole number of.
pub const BLOCK_BYTES: usize = PAGE_BYTES * BLOCK_PAGES;

} // verus!
