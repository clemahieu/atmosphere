//! The Atmosphere early loader.

#![cfg_attr(not(test), no_std, no_main)]
#![deny(
    asm_sub_register,
    deprecated,
    missing_abi,
    unused_macros,
    unused_must_use,
    unused_unsafe
)]
#![deny(clippy::from_over_into, clippy::needless_question_mark)]
#![deny(rustdoc::bare_urls, rustdoc::broken_intra_doc_links)]
#![cfg_attr(not(debug_assertions), deny(dead_code))]

pub mod acpi;
pub mod arch;
pub mod boot;
pub mod console;
pub mod debugger;
pub mod logging;
pub mod memory;

use core::slice;

#[cfg(not(test))]
use core::panic::PanicInfo;

use aelf::{ElfHandle, LoadSegment};
use astd::boot::{
    disjoint_page_runs, page_end, page_start, BootInfo, DomainMapping, MappedRun, Payload,
    SegmentSpan, DOM0_RESERVATION, DOM0_STACK, MAPPED_RUNS, PAGE_BYTES,
};
use astd::heapless::Vec as ArrayVec;
use astd::io::{Cursor, Read, Seek, SeekFrom};
use astd::memory::{USERSPACE_BASE, USERSPACE_PAYLOAD_BASE};
use constants::*;

use memory::{AddressSpace, BootMemoryType, Leaf, PhysicalAllocator, UserspaceMapper, BOOTSTRAP_SIZE};

/// The end of the physical memory the loader identity maps, for itself and for the kernel.
/// The test guest's RAM ends at 2.5 GiB. The 32-bit MMIO window sits just below 4 GiB, and the
/// loader only allocates below 4 GiB. The map is 2M leaves, but for the kernel's image and its
/// stack guard. design/test-guest-memory/.
pub const IDENTITY_MAP_END: u64 = 0x1_0000_0000; // 4 GiB

/// The kernel window: the image, then the stack's guard, then the stack. The loader's bump allocator
/// is sized from it (memory::ALLOCATOR_SIZE).
pub const KERNEL_RESERVATION: usize =
    (KERNEL_IMAGE_BOUND + KERNEL_STACK_GUARD_SIZE + KERNEL_STACK_SIZE) as usize;
// The most the kernel's image may take in memory. A debug image is 3.12 MiB and a release image
// 2.82 MiB, the end of the last LOAD segment in readelf -lW of
// target/x86_64-unknown-aloader/{debug,release}/kernel, so 2.88 MiB is room to grow.
// design/test-guest-memory/.
const KERNEL_IMAGE_BOUND: u64 = 6 * 1024 * 1024; // 6 MiB
// Unmapped below the kernel's stack. The kernel probes large frames, so an overflow cannot jump it.
const KERNEL_STACK_GUARD_SIZE: u64 = 1024 * 1024; // 1 MiB
// The kernel's boot reaches 48 KiB down it in a debug build and 16 KiB in release, and
// tools/check-boot-stack.py requires half of it unused. design/test-guest-memory/.
#[cfg(not(feature = "small_kernel_stack"))]
const KERNEL_STACK_SIZE: u64 = 1024 * 1024; // 1 MiB
// So check-boot-stack.py can force an overflow. Under the depth of the kernel's boot in either
// profile, and over what main uses before the IDT exists.
#[cfg(feature = "small_kernel_stack")]
const KERNEL_STACK_SIZE: u64 = 8 * 1024; // 8 KiB

/// Loads the kernel, dom0 and the payload from the memory map and kernel image the UEFI entry
/// recorded, and enters the kernel with the command line it read. `rsdp` is the ACPI RSDP from the UEFI configuration tables;
/// `wait_for_debugger` holds the kernel's entry until a debugger lets it go (debugger::wait).
fn load(rsdp: u64, wait_for_debugger: bool) -> ! {
    let bootstrap_allocator = memory::bootstrap_allocator();

    let mut address_space = AddressSpace::new(bootstrap_allocator);

    let mut address_space_iommu = AddressSpace::new(bootstrap_allocator);

    let mut cur = 0xFEBD4000;
    let virt_base = USERSPACE_BASE;
    while cur < 0xFEBD4000 + 0x4000 {
        unsafe {
            address_space_iommu.map(bootstrap_allocator, cur + virt_base, cur, true, Leaf::Small, true);
            cur = cur + PAGE_BYTES;
        }
    }

    log::info!("Mapping all physical memory");
    unsafe {
        address_space.map_identity(bootstrap_allocator, IDENTITY_MAP_END, arch::device);
    }

    let mut boot_info = BootInfo::empty(); // stays on stack
    boot_info.pcide = unsafe { arch::activate(address_space.pml4()) };
    boot_info.pml4 = address_space.pml4();
    boot_info.iommu_base = acpi::probe_iommu(rsdp);
    boot_info.command_line = boot::get_command_line();

    let (jumbo_file, jumbo_size) = {
        let range = boot::get_kernel_image_range().expect("No kernel image was passed");

        let f = unsafe { slice::from_raw_parts(range.base() as *const _, range.size() as usize) };
        (Cursor::new(f), f.len())
    };

    let kernel_elf = ElfHandle::parse(jumbo_file, 4096).unwrap();
    let kernel_end = kernel_elf.elf_len();

    let (kernel_base, mut kernel_allocator) =
        memory::reserve(KERNEL_RESERVATION, BootMemoryType::Kernel);
    let (kernel_map, mut jumbo_file) = kernel_elf.load(&mut kernel_allocator).unwrap();

    // Allocate kernel stack
    let guard_base = unsafe {
        kernel_allocator
            .allocate_physical((KERNEL_STACK_GUARD_SIZE + KERNEL_STACK_SIZE) as usize)
            .0
    };
    let stack_base = guard_base + KERNEL_STACK_GUARD_SIZE;
    // The image is everything the window holds below the guard. The kernel changes the protection
    // of single pages of its image (write_protect.rs in the kernel's arch module), and the 1 MiB guard is
    // less than a 2M stretch.
    unsafe {
        address_space.use_small_pages(bootstrap_allocator, kernel_base as u64, stack_base);
    }
    let mut cur = guard_base;
    while cur < stack_base {
        unsafe {
            address_space.unmap(cur);
        }
        cur += PAGE_BYTES;
    }
    // The TLB may hold the 2M leaves those stretches had, and the guard's pages.
    let mut cur = kernel_base as u64;
    while cur < stack_base {
        unsafe {
            arch::flush_page(cur);
        }
        cur += PAGE_BYTES;
    }
    log::info!("Kernel stack guard: {:x}-{:x}", guard_base, stack_base);

    debugger::loaded("kernel", kernel_map.load_bias);

    // Load dom0
    jumbo_file
        .seek(SeekFrom::Start(kernel_end as u64))
        .expect("Kernel file incomplete");

    log::info!("After parsing ELF:");
    memory::dump_physical_memory_map();

    match load_domain("dom0", jumbo_file, &mut address_space, bootstrap_allocator) {
        Ok(mut domain) => {
            // Copy payload as-is into dom0
            let payload_size = jumbo_size as u64 - domain.remaining_file.pos();
            if payload_size != 0 {
                log::info!("Loading payload ({})", payload_size);
                let phys_base =
                    unsafe { domain.allocator.allocate_physical(payload_size as usize).0 };
                let virt_base = USERSPACE_PAYLOAD_BASE;
                domain
                    .mapping
                    .runs
                    .push(MappedRun {
                        virt: virt_base,
                        phys: phys_base,
                        pages: page_end(payload_size) / PAGE_BYTES,
                        writable: true,
                        executable: false,
                    })
                    .expect("dom0 mapped runs do not fit");
                boot_info.payload = Some(Payload {
                    base: virt_base as *mut u8,
                    size: payload_size as usize,
                });
                let mut cur = virt_base;
                while cur < virt_base + payload_size {
                    unsafe {
                        let paddr = cur - virt_base + phys_base;
                        let page = slice::from_raw_parts_mut(paddr as *mut u8, PAGE_BYTES as usize);

                        address_space.map(bootstrap_allocator, cur, paddr, true, Leaf::Small, false);

                        domain
                            .remaining_file
                            .read(page)
                            .expect("Failed to copy payload page");
                    }
                    cur = cur + PAGE_BYTES;
                }
            }
            boot_info.dom0 = Some(domain.mapping);
        }
        Err(e) => {
            log::warn!("No valid Dom0: {:?}", e);
        }
    }

    log::info!("Recording the memory map");
    let free_page_count = memory::record_boot_ranges(
        &mut memory::get_physical_memory_map(),
        &mut boot_info.memory,
    );
    log::info!(
        "ALoader: {} memory ranges, {} free pages",
        boot_info.memory.len(),
        free_page_count
    );

    if wait_for_debugger {
        debugger::wait();
    }

    log::info!(
        "Page-table pool: {} of {} pages hold tables",
        memory::bootstrap_pages_used(),
        BOOTSTRAP_SIZE / PAGE_BYTES as usize
    );
    log::info!(
        "Kernel stack: {:x}-{:x}, boot info at {:x}",
        stack_base,
        stack_base + KERNEL_STACK_SIZE,
        &boot_info as *const _ as u64
    );
    log::info!("Calling into kernel @ {:x?}", kernel_map.entry_point);
    let ret = unsafe {
        arch::enter_kernel(kernel_map.entry_point, &boot_info, stack_base + KERNEL_STACK_SIZE)
    };

    log::info!("Returned from kernel: 0x{:x}", ret);

    loop {}
}

struct Domain<F, A> {
    mapping: DomainMapping,
    remaining_file: F,
    allocator: A,
}

fn load_domain<F, A>(
    name: &'static str,
    mut elf: F,
    address_space: &mut AddressSpace,
    page_table_allocator: &mut A,
) -> Result<Domain<F, impl PhysicalAllocator>, aelf::Error>
where
    F: Read + Seek,
    F::Error: Into<aelf::Error>,
    A: PhysicalAllocator,
{
    let dom_start = elf.stream_position().unwrap() as usize;
    let parsed = ElfHandle::parse(elf, PAGE_BYTES as usize)?;
    let dom_end = dom_start + parsed.elf_len();
    log::info!("Loading {}...", name);

    let mut raw_segments = [LoadSegment {
        vaddr: 0,
        memsz: 0,
        writable: false,
        executable: false,
    }; 20];
    let segment_count = parsed
        .loadable_segments(&mut raw_segments)
        .expect("dom0 mapped runs do not fit");

    let (reserved_start, mut allocator) =
        memory::reserve(DOM0_RESERVATION as usize, BootMemoryType::Domain); // FIXME: Use AddressSpace as allocator

    let mut userspace_mapper =
        UserspaceMapper::new(address_space, &mut allocator, page_table_allocator);
    let (dom_map, mut elf) = parsed
        .load(&mut userspace_mapper)
        .expect("Failed to map Dom0");

    // Allocate and map stack
    // FIXME: Use GNU_STACK
    let phys_base = unsafe { allocator.allocate_physical(DOM0_STACK as usize).0 };
    let virt_base = USERSPACE_BASE + DOM0_RESERVATION - DOM0_STACK;

    let mut cur = virt_base;
    while cur < virt_base + DOM0_STACK {
        unsafe {
            address_space.map(
                page_table_allocator,
                cur,
                cur - virt_base + phys_base,
                true,
                Leaf::Small,
                false,
            );
        }
        cur = cur + PAGE_BYTES;
    }

    elf.seek(SeekFrom::Start(dom_end as u64))
        .expect("dom0 incomplete");

    log::debug!("Dom0 end: {}", dom_end);

    debugger::loaded(name, dom_map.load_bias);

    let mut spans = [SegmentSpan {
        virt: 0,
        pages: 0,
        writable: false,
        executable: false,
    }; 20];
    for (index, segment) in raw_segments.iter().take(segment_count).enumerate() {
        let start = page_start(dom_map.load_bias as u64 + segment.vaddr);
        let end = page_end(dom_map.load_bias as u64 + segment.vaddr + segment.memsz);
        if end <= start {
            panic!("dom0 mapped runs do not fit");
        }
        spans[index] = SegmentSpan {
            virt: start,
            pages: (end - start) / PAGE_BYTES,
            writable: segment.writable,
            executable: segment.executable,
        };
    }
    let mut folded = [MappedRun {
        virt: 0,
        phys: 0,
        pages: 0,
        writable: false,
        executable: false,
    }; MAPPED_RUNS];
    let image_phys = dom_map.phys_base as u64;
    let image_virt = dom_map.load_addr as u64;
    let folded_count = disjoint_page_runs(
        &spans[..segment_count],
        |virt| image_phys + (virt - image_virt),
        &mut folded,
    )
    .expect("dom0 mapped runs do not fit");
    let mut runs = ArrayVec::<MappedRun, MAPPED_RUNS>::new();
    for run in folded.iter().take(folded_count) {
        runs.push(*run).expect("dom0 mapped runs do not fit");
    }
    runs.push(MappedRun {
        virt: virt_base,
        phys: phys_base,
        pages: DOM0_STACK / PAGE_BYTES,
        writable: true,
        executable: false,
    })
    .expect("dom0 mapped runs do not fit");

    let mapping = DomainMapping {
        reserved_start,
        reserved_size: DOM0_RESERVATION as usize,
        virt_start: USERSPACE_BASE as *mut u8,
        entry_point: dom_map.entry_point,
        load_bias: dom_map.load_bias,
        runs,
    };

    Ok(Domain {
        mapping,
        remaining_file: elf,
        allocator,
    })
}

/// The kernel panic handler.
#[cfg(not(test))]
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::info!("panic! {:?}", info);
    loop {}
}
