//! Boot loader integration.

pub mod command_line;
mod efi_memory;
mod uefi;

use crate::memory::init_physical_memory_map;
use crate::memory::{AcpiMemoryType, MemoryRange};
use astd::string::ArrayString;
use astd::sync::Mutex;

/// The kernel image passed by the bootloader.
static KERNEL_IMAGE: Mutex<Option<MemoryRange>> = Mutex::new(None);

/// The kernel's command line as the boot path read it.
static COMMAND_LINE: Mutex<ArrayString<{ command_line::CAPACITY }>> = Mutex::new(ArrayString::empty());

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

/// Returns the range of the kernel image.
pub fn get_kernel_image_range() -> Option<MemoryRange> {
    KERNEL_IMAGE.lock().clone()
}

/// Returns the kernel's command line.
pub fn get_command_line() -> ArrayString<{ command_line::CAPACITY }> {
    COMMAND_LINE.lock().clone()
}

/// Records the memory map, the kernel image and the kernel's command line a boot path found.
fn consume_start_info<S: StartInfo>(
    start_info: S,
    loader_range: MemoryRange,
    command_line: ArrayString<{ command_line::CAPACITY }>,
) {
    *COMMAND_LINE.lock() = command_line;

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
