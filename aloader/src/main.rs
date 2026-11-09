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
pub mod boot;
pub mod console;
pub mod debugger;
pub mod logging;
pub mod memory;

use core::arch::asm;
use core::slice;

#[cfg(not(test))]
use core::panic::PanicInfo;

use core::arch::x86_64::__cpuid;

use aelf::{ElfHandle, LoadSegment};
use astd::boot::{
    disjoint_page_runs, page_end, page_start, BootInfo, DomainMapping, MappedRun, Payload,
    PhysicalMemoryType, SegmentSpan, DOM0_RESERVATION, DOM0_STACK, MAPPED_RUNS, PAGE_BYTES,
};
use astd::heapless::Vec as ArrayVec;
use astd::io::{Cursor, Read, Seek, SeekFrom};
use astd::memory::{USERSPACE_BASE, USERSPACE_PAYLOAD_BASE};
use constants::*;

use memory::{AddressSpace, BootMemoryType, PhysicalAllocator, UserspaceMapper, PAGE_SIZE};

/// The end of the physical memory the loader identity maps, for itself and for the kernel.
pub const IDENTITY_MAP_END: u64 = 0x240000000; // 9 GiB

const KERNEL_RESERVATION: usize = 1024 * 1024 * 1024; // 1 GiB
// The kernel reaches 192 MiB during init at opt-level 0 and 128 MiB in release, as measured by
// tools/check-boot-stack.py.
// Unmapped below the kernel's stack. The kernel probes large frames, so an overflow cannot jump it.
const KERNEL_STACK_GUARD_SIZE: u64 = 1024 * 1024; // 1 MiB
#[cfg(not(feature = "small_kernel_stack"))]
const KERNEL_STACK_SIZE: u64 = 256 * 1024 * 1024; // 256 MiB
// So check-boot-stack.py can force an overflow. boot::init's copy of BootInfo alone is 64 MiB however
// the optimiser arranges the kernel's frames, so this is below the kernel's depth in all of them.
#[cfg(feature = "small_kernel_stack")]
const KERNEL_STACK_SIZE: u64 = 16 * 1024 * 1024; // 16 MiB

/// Loads the kernel, dom0 and the payload from the memory map and kernel image the UEFI entry
/// recorded, and enters the kernel. `rsdp` is the ACPI RSDP from the UEFI configuration tables;
/// `wait_for_debugger` holds the kernel's entry until a debugger lets it go (debugger::wait).
fn load(rsdp: u64, wait_for_debugger: bool) -> ! {
    let bootstrap_allocator = memory::bootstrap_allocator();

    let mut address_space = AddressSpace::new(bootstrap_allocator);

    let mut address_space_iommu = AddressSpace::new(bootstrap_allocator);

    let mut cur = 0xFEBD4000;
    let virt_base = USERSPACE_BASE;
    while cur < 0xFEBD4000 + 0x4000 {
        unsafe {
            address_space_iommu.map(bootstrap_allocator, cur + virt_base, cur, true, false, true);
            cur = cur + PAGE_SIZE as u64;
        }
    }

    log::info!("Mapping all physical memory");
    let mut cur = 0;
    while cur < IDENTITY_MAP_END {
        // FIXME
        unsafe {
            address_space.map(bootstrap_allocator, cur, cur, false, false, false);
        }
        cur = cur + PAGE_SIZE as u64;
    }

    let mut boot_info = BootInfo::empty(); // stays on stack
    boot_info.pcide = cpu_has_pcid();

    if boot_info.pcide {
        log::info!("Enabling Tagged TLB");
        unsafe {
            asm!(
                "mov {cr4}, cr4",
                "or {cr4}, {cr4_pcide}",
                "mov cr4, {cr4}",
                cr4 = out(reg) _,
                cr4_pcide = const (1 << 17),
            );
        }
    } else {
        log::warn!("CPU does not support Tagged TLB");
    }

    log::info!("Switching to PML4 @ {:x?}", address_space.pml4());
    unsafe {
        asm!(
            "mov cr3, {pml4}",
            pml4 = inout(reg) address_space.pml4() => _,
        );
    }

    boot_info.pml4 = address_space.pml4();
    boot_info.iommu_base = acpi::probe_iommu(rsdp);

    let (jumbo_file, jumbo_size) = {
        let range = boot::get_kernel_image_range().expect("No kernel image was passed");

        let f = unsafe { slice::from_raw_parts(range.base() as *const _, range.size() as usize) };
        (Cursor::new(f), f.len())
    };

    let kernel_elf = ElfHandle::parse(jumbo_file, 4096).unwrap();
    let kernel_end = kernel_elf.elf_len();

    let (_, mut kernel_allocator) = memory::reserve(KERNEL_RESERVATION, BootMemoryType::Kernel);
    let (kernel_map, mut jumbo_file) = kernel_elf.load(&mut kernel_allocator).unwrap();

    // Allocate kernel stack
    let guard_base = unsafe {
        kernel_allocator
            .allocate_physical((KERNEL_STACK_GUARD_SIZE + KERNEL_STACK_SIZE) as usize)
            .0
    };
    let stack_base = guard_base + KERNEL_STACK_GUARD_SIZE;
    let mut cur = guard_base;
    while cur < stack_base {
        unsafe {
            address_space.unmap(cur);
        }
        cur += PAGE_SIZE as u64;
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
                        let page = slice::from_raw_parts_mut(paddr as *mut u8, PAGE_SIZE);

                        address_space.map(bootstrap_allocator, cur, paddr, true, false, false);

                        domain
                            .remaining_file
                            .read(page)
                            .expect("Failed to copy payload page");
                    }
                    cur = cur + PAGE_SIZE as u64;
                }
            }
            boot_info.dom0 = Some(domain.mapping);
        }
        Err(e) => {
            log::warn!("No valid Dom0: {:?}", e);
        }
    }

    let mut free_page_count = 0;
    let mut cur = 0;
    log::info!("Populating physical page list");
    for (region, label) in memory::get_physical_memory_map().regions.iter() {
        if boot_info.pages.is_full() {
            break;
        }

        let page_type: PhysicalMemoryType = (*label).into();
        log::info!(
            "region.base() {:x}, region.end_inclusive() {:x}, page_type {:?}, label {:?}",
            region.base(),
            region.end_inclusive(),
            page_type,
            *label
        );
        while cur < region.base() {
            if boot_info.pages.is_full() {
                break;
            }

            boot_info
                .pages
                .push((cur, PhysicalMemoryType::Reserved))
                .expect("Too many pages");
            cur += PAGE_SIZE as u64;
        }
        while cur < region.end_inclusive() {
            if boot_info.pages.is_full() {
                break;
            }

            if page_type == PhysicalMemoryType::Available {
                free_page_count = free_page_count + 1;
            }
            boot_info
                .pages
                .push((cur, page_type))
                .expect("Too many pages");
            cur += PAGE_SIZE as u64;
        }
    }
    while cur < 4 * 1024 * 1024 * 4096 {
        if boot_info.pages.is_full() {
            break;
        }

        boot_info
            .pages
            .push((cur, PhysicalMemoryType::Reserved))
            .expect("Too many pages");
        cur += PAGE_SIZE as u64;
    }

    log::info!("ALoader: Num of free pages --> {:?}", free_page_count);

    if wait_for_debugger {
        debugger::wait();
    }

    log::info!(
        "Kernel stack: {:x}-{:x}, boot info at {:x}",
        stack_base,
        stack_base + KERNEL_STACK_SIZE,
        &boot_info as *const _ as u64
    );
    log::info!("Calling into kernel @ {:x?}", kernel_map.entry_point);
    let ret: usize;
    unsafe {
        asm!(
            // save state
            "mov r15w, ds; push r15w",
            "mov r15w, fs; push r15w",
            "mov r15w, gs; push r15w",
            "mov r15w, ss; push r15w",

            // clear state
            // rdi = &boot_info
            "xor r15, r15",
            "mov ds, r15w",
            "mov fs, r15w",
            "mov gs, r15w",
            "mov ss, r15w",

            "push rsp",
            "mov rsp, rsi",
            "xor rsi, rsi",

            // call entry
            "call rax",

            // restore state
            "pop rsp",
            "pop r15w; mov ss, r15w",
            "pop r15w; mov gs, r15w",
            "pop r15w; mov fs, r15w",
            "pop r15w; mov ds, r15w",

            inout("rax") kernel_map.entry_point => ret,
            inout("rdi") &boot_info as *const _ => _,
            inout("rsi") stack_base + KERNEL_STACK_SIZE => _,
            out("r15") _,
        );
    }

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
    let parsed = ElfHandle::parse(elf, PAGE_SIZE)?;
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
                false,
                false,
            );
        }
        cur = cur + PAGE_SIZE as u64;
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

fn cpu_has_pcid() -> bool {
    let cpuid_1 = __cpuid(0x1);
    (cpuid_1.ecx & (1 << 17)) != 0
}

/// The kernel panic handler.
#[cfg(not(test))]
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::info!("panic! {:?}", info);
    loop {}
}
