use vstd::prelude::*;

verus! {

use crate::pptr::*;

pub type CpuId = usize;

pub type PagePtr = usize;

pub type PagePerm4k = PointsTo<[u8; PAGE_SZ_4k]>;

pub type VAddr = usize;

pub type PAddr = usize;

pub type PageMapPtr = usize;

pub type IOid = usize;

pub type L4Index = usize;

pub type L3Index = usize;

pub type L2Index = usize;

pub type L1Index = usize;

//1 for now
pub const KERNEL_MEM_END_L4INDEX: usize = 1;

/// Pages the kernel tracks: 1 GiB, the loader's page list. design/test-guest-memory/.
pub const NUM_PAGES: usize = 256 * 1024;

pub const PAGE_SZ_4k: usize = 4096;

pub const PCID_MAX: usize = 4096;

pub const NUM_CPUS: usize = 32;
pub const NUM_IOMMUS: usize = 8;

} // verus!
