//! The UEFI entry.
//!
//! OVMF, or a machine's firmware, starts the loader as an application from the EFI system
//! partition. The loader reads the initrd (kernel, dom0 and payload, as tools/run.py concatenates
//! them) from the same partition, takes the ACPI RSDP from the configuration tables, leaves boot
//! services, and runs the load on a stack of its own.

use core::arch::asm;
use core::ffi::c_void;
use core::ptr;
use core::slice;

use uefi_raw::protocol::file_system::{FileAttribute, FileMode, FileProtocolV1, SimpleFileSystemProtocol};
use uefi_raw::protocol::loaded_image::LoadedImageProtocol;
use uefi_raw::table::boot::{AllocateType, BootServices, MemoryDescriptor, MemoryType};
use uefi_raw::table::system::SystemTable;
use uefi_raw::{guid, Guid, Handle, Status};

use super::efi_memory::region_type;
use super::{consume_start_info, StartInfo};
use crate::memory::{AcpiMemoryType, MemoryRange, BOOTSTRAP_SIZE, PAGE_SIZE};

/// The initrd's path on the partition the loader was started from, as UCS-2 with its terminator;
/// tools/run.py puts it there.
static INITRD_PATH: [u16; 7] = [
    b'i' as u16, b'n' as u16, b'i' as u16, b't' as u16, b'r' as u16, b'd' as u16, 0,
];

/// The configuration table entry of the ACPI 2.0 RSDP (UEFI 2.11, section 4.6.1.1).
const ACPI_20_TABLE_GUID: Guid = guid!("8868e871-e4f1-11d3-bc22-0080c73c8881");

/// The loader's stack. `main::load` keeps the kernel's BootInfo on it, and that alone is 64 MiB.
const STACK_SIZE: usize = 256 * 1024 * 1024;

/// Allocations the loader keeps stay below 4 GiB: inside the identity map the loader builds, and
/// for the page tables, where the AP trampoline's 32-bit CR3 load reaches.
const ALLOCATION_LIMIT: u64 = 0xffff_ffff;

/// Descriptors of room the memory map buffer leaves for the entries its own allocation adds.
const MEMORY_MAP_SLACK: usize = 16;

/// The firmware's entry into the loader.
#[no_mangle]
extern "efiapi" fn efi_main(image: Handle, system_table: *const SystemTable) -> Status {
    unsafe {
        crate::console::init();
        crate::logging::init();
    }

    log::info!("** Atmosphere Loader (UEFI) **");

    // The firmware passes a valid system table, whose boot services stay valid until
    // exit_boot_services.
    let system_table = unsafe { &*system_table };
    let boot_services = unsafe { &*system_table.boot_services };

    let loader_range = loader_image_range(boot_services, image);
    let initrd = read_initrd(boot_services, image);
    let rsdp = find_rsdp(system_table);
    log::info!("ACPI RSDP at {:#x}", rsdp);
    let stack = allocate(boot_services, STACK_SIZE);
    unsafe {
        crate::memory::set_bootstrap_region(allocate(boot_services, BOOTSTRAP_SIZE));
    }

    let memory_map = exit_boot_services(boot_services, image);
    unsafe {
        asm!("cli");
    }

    consume_start_info(
        UefiStartInfo {
            memory_map,
            initrd,
        },
        loader_range,
    );

    unsafe {
        crate::memory::init();

        asm!(
            "mov rsp, {stack_top}",
            "call {load}",
            stack_top = in(reg) stack as u64 + STACK_SIZE as u64,
            load = sym load,
            in("rdi") rsdp,
            options(noreturn),
        );
    }
}

/// Called on the loader's stack with the RSDP in rdi. The target's C convention is Microsoft's,
/// which passes it in rcx.
extern "sysv64" fn load(rsdp: u64) -> ! {
    crate::load(rsdp)
}

/// Panics unless `status` is success.
fn check(status: Status, what: &str) {
    assert!(status.is_success(), "{}: {:?}", what, status);
}

/// The protocol `guid` names on `handle`.
fn protocol<T>(boot_services: &BootServices, handle: Handle, guid: &Guid) -> *mut T {
    let mut interface: *mut c_void = ptr::null_mut();
    let status = unsafe { (boot_services.handle_protocol)(handle, guid, &mut interface) };
    check(status, "handle_protocol");
    interface.cast()
}

/// The range the firmware loaded the loader's image at.
fn loader_image_range(boot_services: &BootServices, image: Handle) -> MemoryRange {
    let loaded_image: *mut LoadedImageProtocol =
        protocol(boot_services, image, &LoadedImageProtocol::GUID);
    let loaded_image = unsafe { &*loaded_image };
    let range = MemoryRange::new(loaded_image.image_base as u64, loaded_image.image_size);
    // The firmware chooses where.
    assert!(
        range.end_inclusive() < crate::IDENTITY_MAP_END,
        "The loader was loaded at {}, above the memory it maps",
        range
    );
    range
}

/// Reads the initrd into memory the loader keeps.
fn read_initrd(boot_services: &BootServices, image: Handle) -> MemoryRange {
    let loaded_image: *mut LoadedImageProtocol =
        protocol(boot_services, image, &LoadedImageProtocol::GUID);
    let device = unsafe { (*loaded_image).device_handle };
    let file_system: *mut SimpleFileSystemProtocol =
        protocol(boot_services, device, &SimpleFileSystemProtocol::GUID);

    unsafe {
        let mut root: *mut FileProtocolV1 = ptr::null_mut();
        check(((*file_system).open_volume)(file_system, &mut root), "open_volume");

        let mut file: *mut FileProtocolV1 = ptr::null_mut();
        check(
            ((*root).open)(root, &mut file, INITRD_PATH.as_ptr(), FileMode::READ, FileAttribute::empty()),
            "open initrd",
        );

        check(((*file).set_position)(file, u64::MAX), "seek to the initrd's end");
        let mut size = 0;
        check(((*file).get_position)(file, &mut size), "size the initrd");
        let size = size as usize;
        check(((*file).set_position)(file, 0), "seek to the initrd's start");

        let base = allocate(boot_services, size);
        let buffer = slice::from_raw_parts_mut(base, size);
        let mut read = 0;
        while read < size {
            let mut n = size - read;
            check(
                ((*file).read)(file, &mut n, buffer[read..].as_mut_ptr().cast()),
                "read initrd",
            );
            assert!(n != 0, "The initrd ended after {} of {} bytes", read, size);
            read += n;
        }

        check(((*file).close)(file), "close initrd");
        check(((*root).close)(root), "close volume");

        log::info!("Read the initrd: {} bytes at {:#x}", size, base as u64);
        MemoryRange::new(base as u64, size as u64)
    }
}

/// The ACPI 2.0 RSDP from the configuration tables.
fn find_rsdp(system_table: &SystemTable) -> u64 {
    let tables = unsafe {
        slice::from_raw_parts(
            system_table.configuration_table,
            system_table.number_of_configuration_table_entries,
        )
    };
    tables
        .iter()
        .find(|table| table.vendor_guid == ACPI_20_TABLE_GUID)
        .map(|table| table.vendor_table as u64)
        .expect("No ACPI 2.0 table in the UEFI configuration tables")
}

/// Allocates pages the loader keeps, which the memory map then marks as loader data.
fn allocate(boot_services: &BootServices, size: usize) -> *mut u8 {
    let mut address = ALLOCATION_LIMIT;
    let status = unsafe {
        (boot_services.allocate_pages)(
            AllocateType::MAX_ADDRESS,
            MemoryType::LOADER_DATA,
            size.div_ceil(PAGE_SIZE),
            &mut address,
        )
    };
    check(status, "allocate below 4 GiB");
    address as *mut u8
}

/// The memory map as the firmware left it at ExitBootServices.
struct EfiMemoryMap {
    buffer: *const u8,
    size: usize,
    descriptor_size: usize,
}

impl EfiMemoryMap {
    fn descriptors(&self) -> impl Iterator<Item = &MemoryDescriptor> + '_ {
        (0..self.size / self.descriptor_size).map(move |i| {
            // The firmware wrote `size` bytes of descriptors `descriptor_size` apart.
            unsafe { &*self.buffer.add(i * self.descriptor_size).cast::<MemoryDescriptor>() }
        })
    }
}

/// Takes the memory map and leaves boot services.
///
/// The map's key changes with every allocation, so the buffer is allocated first with room for
/// the entries the allocation adds; if the firmware still reports the key stale, the map is read
/// again into the same buffer, as UEFI 2.11 section 7.4.6 allows.
fn exit_boot_services(boot_services: &BootServices, image: Handle) -> EfiMemoryMap {
    let mut size = 0;
    let mut key = 0;
    let mut descriptor_size = 0;
    let mut version = 0;
    let status = unsafe {
        (boot_services.get_memory_map)(
            &mut size,
            ptr::null_mut(),
            &mut key,
            &mut descriptor_size,
            &mut version,
        )
    };
    assert!(status == Status::BUFFER_TOO_SMALL, "get_memory_map: {:?}", status);

    let capacity = size + MEMORY_MAP_SLACK * descriptor_size;
    let buffer = allocate(boot_services, capacity);

    for _ in 0..2 {
        size = capacity;
        let status = unsafe {
            (boot_services.get_memory_map)(
                &mut size,
                buffer.cast(),
                &mut key,
                &mut descriptor_size,
                &mut version,
            )
        };
        check(status, "get_memory_map");

        if unsafe { (boot_services.exit_boot_services)(image, key) }.is_success() {
            return EfiMemoryMap {
                buffer,
                size,
                descriptor_size,
            };
        }
    }

    panic!("ExitBootServices refused the memory map twice");
}

/// The memory map and initrd for the loader's memory map.
struct UefiStartInfo {
    memory_map: EfiMemoryMap,
    initrd: MemoryRange,
}

impl StartInfo for UefiStartInfo {
    fn iter_memory_regions(
        &self,
    ) -> impl Iterator<Item = (MemoryRange, Option<AcpiMemoryType>)> + '_ {
        self.memory_map
            .descriptors()
            .filter(|entry| entry.page_count != 0)
            .map(|entry| {
                (
                    MemoryRange::new(entry.phys_start, entry.page_count * PAGE_SIZE as u64),
                    Some(region_type(entry.ty.0)),
                )
            })
    }

    fn iter_modlist(&self) -> impl Iterator<Item = MemoryRange> + '_ {
        core::iter::once(self.initrd.clone())
    }
}
