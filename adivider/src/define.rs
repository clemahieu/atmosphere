//! The sizes and bounds the divider counts in, written once, where tools/check-page-literals.py
//! allows a page-shaped literal.

use vstd::prelude::*;

verus! {

/// A page, the unit a block counts in, as kernel/verified/define.rs's PAGE_SZ.
pub const PAGE_BYTES: u64 = 4096;

/// Memory is the pages below 2^48, and device d is the page at DEVICE_OBJECTS + d pages, as in
/// reach.rs.
pub const DEVICE_OBJECTS: u64 = 0x1_0000_0000_0000;

/// Every object is below this: memory, the devices' 2^36 pages, the console's and power's.
pub const OBJECT_SPACE: u64 = 0x4_0000_0000_0000;

} // verus!
