#![no_std]

pub const DATA_BUFFER_ADDR: u64 = 0xF0_0000_0000;
pub const USERSPACE_BASE: u64 = 0x80_0000_0000;

pub const IOMMU_TEST_ADDR: u64 = 0xF0_0000_0000;

const COM1: usize = 0x3f8;

pub const SPORT_ADDR: usize = COM1;
