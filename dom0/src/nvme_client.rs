extern crate nvme_driver;
extern crate ring_buffer;
use core::mem::MaybeUninit;
use libtime::rdtsc;
use libtime::sys_ns_loopsleep;
use nvme_driver::device::NvmeDevice;
use nvme_driver::nvme_test::{run_blocktest_blkreq, run_blocktest_raw_with_delay};
use pcid::utils::PciBarAddr;
use crate::ring_buffer::{RingBuffer, SIZE_OF_BUFFER, SIZE_OF_QUEUE};
use nvme_driver::*;
use core::arch::asm;
use crate::DATA_BUFFER_ADDR;
use ring_buffer::*;
use core::arch::x86_64::_rdtsc;
use constants::*;

pub fn test_nvme_driver() {
    unsafe {
        asys::sys_set_device_iommu(NVME_PCI_DEV.0, NVME_PCI_DEV.1, NVME_PCI_DEV.2);
    }

    let mut nvme_dev =
        unsafe { NvmeDevice::new(PciBarAddr::new(USERSPACE_BASE + NVME_BAR_BASE, NVME_BAR_SIZE)) };

    log::info!("Initializing Nvme driver...");

    nvme_dev.init();

    log::info!("Running Nvme Read/write tests!");

    run_blocktest_raw_with_delay(&mut nvme_dev, 30, 32, true, false, 0);
    run_blocktest_raw_with_delay(&mut nvme_dev, 30, 32, false, false, 0);

}

/// | MSG_TYPE | PAYLOAD |
/// MSG_TYPE == STOP
///     quit polling

struct Rand {
    seed: u64,
    pow: u64,
}

impl Rand {
    fn new() -> Rand {
        Rand {
            seed: 123456789,
            pow: 2u64.pow(31),
        }
    }

    #[inline(always)]
    fn get_rand_u64(&mut self) -> u64 {
        self.seed = (1103515245 * self.seed + 12345) % self.pow;
        self.seed
    }
}
