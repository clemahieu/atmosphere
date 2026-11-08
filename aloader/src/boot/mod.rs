//! Boot loader integration.

#[cfg(any(target_os = "uefi", test))]
mod efi_memory;
#[cfg(not(target_os = "uefi"))]
mod hvm;
#[cfg(not(target_os = "uefi"))]
mod multiboot2;
#[cfg(target_os = "uefi")]
mod uefi;

#[cfg(not(target_os = "uefi"))]
use core::ptr;

use crate::memory::init_physical_memory_map;
use crate::memory::{AcpiMemoryType, MemoryRange};
use astd::sync::Mutex;

/// The kernel image passed by the bootloader.
static KERNEL_IMAGE: Mutex<Option<MemoryRange>> = Mutex::new(None);

#[cfg(all(not(test), not(target_os = "uefi")))]
extern "C" {
    static bootinfo: u64;
    static __loader_start: u8;
    static __loader_end: u8;
}

#[cfg(test)]
static mut bootinfo: u64 = 0;

#[cfg(test)]
static mut __loader_start: u8 = 0;

#[cfg(test)]
static mut __loader_end: u8 = 0;

/// A type of bootloader.
#[cfg(not(target_os = "uefi"))]
#[derive(Debug)]
enum Bootloader {
    /// Multiboot 2.
    Multiboot2,

    /// Xen x86/HVM direct boot ABI.
    Hvm,
}

trait StartInfo {
    /// Creates an iterator through all memory regions.
    fn iter_memory_regions(
        &self,
    ) -> impl Iterator<Item = (MemoryRange, Option<AcpiMemoryType>)> + '_;

    /// Creates an iterator through the module list entries.
    fn iter_modlist(&self) -> impl Iterator<Item = MemoryRange> + '_;

    /// Dumps the physical memory map to the log.
    fn dump_memmap(&self) {
        log::info!("Physical memory map:");
        for (region, ty) in self.iter_memory_regions() {
            log::info!(
                "[mem {:#016x}-{:#016x}] {:?}",
                region.base(),
                region.end_inclusive(),
                ty.unwrap(),
            );
        }
    }

    /// Dumps the module list to the log.
    fn dump_modlist(&self) {
        log::info!("Module list:");
        for module in self.iter_modlist() {
            log::info!(
                "[mod {:#016x}-{:#016x}] ({} bytes)",
                module.base(),
                module.end_inclusive(),
                module.size(),
            );
        }
    }
}

/// Returns the range of the loader itself.
#[cfg(not(target_os = "uefi"))]
pub fn get_loader_image_range() -> MemoryRange {
    let start = unsafe { &__loader_start as *const _ as u64 };
    let end_exclusive = unsafe { &__loader_end as *const _ as u64 };
    let size = end_exclusive - start;

    MemoryRange::new(start, size)
}

/// Returns the range of the kernel image.
pub fn get_kernel_image_range() -> Option<MemoryRange> {
    KERNEL_IMAGE.lock().clone()
}

/// Records the memory map and the kernel image a boot path found.
fn consume_start_info<S: StartInfo>(start_info: S, loader_range: MemoryRange) {
    log::info!(
        "[ldr {:#016x}-{:#016x}]",
        loader_range.base(),
        loader_range.end_inclusive()
    );
    start_info.dump_memmap();
    start_info.dump_modlist();

    let regions = start_info
        .iter_memory_regions()
        .map(|(r, t)| (r, t.expect("Unknown memory type")));
    let image_ranges = start_info.iter_modlist();

    init_physical_memory_map(regions, loader_range, image_ranges);

    if let Some(module) = start_info.iter_modlist().next() {
        let mut kernel_image = KERNEL_IMAGE.lock();
        *kernel_image = Some(module);
    };
}

/// Initializes the boot loader information from what the multiboot2 or PVH entry in crt0.asm saved.
#[cfg(not(target_os = "uefi"))]
pub unsafe fn init() {
    let start_info_ptr = bootinfo as *const u8;
    match detect_bootloader() {
        Some(Bootloader::Hvm) => {
            log::info!("Booted via Xen x86/HVM");
            let start_info =
                unsafe { hvm::HvmStartInfo::load(start_info_ptr).expect("Invalid Xen x86/HVM start info") };
            consume_start_info(start_info, get_loader_image_range());
        }
        Some(Bootloader::Multiboot2) => {
            log::info!("Booted via Multiboot2");
            let start_info =
                unsafe { multiboot2::Multiboot2StartInfo::load(start_info_ptr).expect("Invalid Multiboot2 start info") };
            consume_start_info(start_info, get_loader_image_range());
        }
        _ => {
            panic!("Failed to detect bootloader, cannot continue");
        }
    }
}

#[cfg(not(target_os = "uefi"))]
fn detect_bootloader() -> Option<Bootloader> {
    let bootinfo_addr = unsafe { bootinfo };

    if bootinfo_addr == 0 {
        return None;
    }

    let magic4 = {
        let magic_ptr = bootinfo_addr as *const u32;
        unsafe { ptr::read_unaligned(magic_ptr) }
    };

    if magic4 == hvm::HVM_START_INFO_MAGIC {
        Some(Bootloader::Hvm)
    } else {
        Some(Bootloader::Multiboot2)
    }
}
