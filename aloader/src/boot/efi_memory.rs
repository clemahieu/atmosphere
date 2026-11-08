//! UEFI memory types.

use crate::memory::AcpiMemoryType;

/// The address range type the loader gives a UEFI memory map entry, by its `EFI_MEMORY_TYPE`
/// (UEFI 2.11, section 7.2.1).
///
/// Only conventional memory is free. Boot services memory stays reserved with the loader's own
/// allocations: the loader runs on the firmware's GDT and on its own stack until the kernel takes
/// over, and the kernel is handed less memory rather than memory something still uses.
pub fn region_type(efi_type: u32) -> AcpiMemoryType {
    match efi_type {
        EFI_CONVENTIONAL_MEMORY => AcpiMemoryType::Memory,
        EFI_UNUSABLE_MEMORY => AcpiMemoryType::Unusable,
        EFI_ACPI_RECLAIM_MEMORY => AcpiMemoryType::Acpi,
        EFI_ACPI_MEMORY_NVS => AcpiMemoryType::Nvs,
        _ => AcpiMemoryType::Reserved,
    }
}

const EFI_CONVENTIONAL_MEMORY: u32 = 7;
const EFI_UNUSABLE_MEMORY: u32 = 8;
const EFI_ACPI_RECLAIM_MEMORY: u32 = 9;
const EFI_ACPI_MEMORY_NVS: u32 = 10;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conventional_memory_is_free() {
        assert_eq!(region_type(7), AcpiMemoryType::Memory);
    }

    /// Loader code and data, boot services code and data, runtime services, MMIO and the
    /// reserved type are all kept from the kernel's free pages.
    #[test]
    fn firmware_and_loader_memory_is_reserved() {
        for efi_type in [0, 1, 2, 3, 4, 5, 6, 11, 12, 13, 14, 15] {
            assert_eq!(region_type(efi_type), AcpiMemoryType::Reserved, "type {}", efi_type);
        }
    }

    #[test]
    fn acpi_and_unusable_memory_keep_their_type() {
        assert_eq!(region_type(8), AcpiMemoryType::Unusable);
        assert_eq!(region_type(9), AcpiMemoryType::Acpi);
        assert_eq!(region_type(10), AcpiMemoryType::Nvs);
    }
}
