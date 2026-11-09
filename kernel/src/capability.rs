//! The capability kernel: built at boot in memory boot sets aside, with dom0 as the root process.
//!
//! The loader's page list and dom0's runs cross the trust boundary here, and are checked by
//! boot/free_ranges.rs and boot/mapped_runs.rs before the verified boot step runs on them. The
//! permissions that step takes for the pages are this file's to vouch for: the pages it hands over
//! are the ones those checks passed, and nothing else in the kernel touches them. Why the boundary
//! is tier 3: design/trust-boundary/. What boot hands the root: design/root-process-at-boot/.

use core::mem::size_of;

use astd::boot::{BootInfo, PhysicalMemoryType, MAPPED_RUNS, PAGE_BYTES};
use verified::array::Array;
use verified::capability::boot::{
    ROOT_CONSOLE_SLOT, ROOT_FRAME_SLOT, ROOT_PROCESS_SLOT, ROOT_THREAD_SLOT, ROOT_UNTYPED_SLOT,
};
use verified::capability::boot_image::ImageRun;
use verified::capability::boot_memory::ROOT_UNTYPED_SLOTS;
use verified::capability::decompose::first_block;
use verified::capability::kernel::{CapKernel, CommandBuffers};
use verified::capability::space::SPACE_ROOT_PAGE;
use verified::capability::table::{CapKind, MAX_ORDER};
use verified::define::{KERNEL_MEM_END_L4INDEX, NUM_IOMMUS};
use vstd::prelude::Tracked;

use crate::boot::free_ranges::{free_page_ranges, ByteRange, PageRun, PAGE_SLOTS};
use crate::boot::mapped_runs::mapped_runs;
use crate::lock::Locked;

/// The one capability kernel, holding every core. Why one: design/one-kernel-instance/.
pub static CAP_KERNEL: Locked<Option<&'static mut CapKernel>> = Locked::new("capability kernel", None);

/// Pages of the stretch boot sets aside that hold the root's boot objects, before the kernel itself:
/// the process's block, its table's two leaves, its thread's block and the list's synthetic root, with
/// the stretch aligned to this many pages so the process's 8-page block is aligned.
const BOOT_OBJECT_PAGES: u64 = 16;
const PROCESS_PAGE: u64 = 0;
const LEAF_PAGE: u64 = 8;
const FRAMES_PAGE: u64 = 10;
const THREAD_PAGE: u64 = 12;
const LIST_ROOT_PAGE: u64 = 14;

/// The bytes of a 2M region. A region holding any of dom0's pages is typed as a large frame for them,
/// so no other page of it is free or set aside: design/root-process-at-boot/.
const REGION_BYTES: u64 = 512 * PAGE_BYTES;

/// The most maximal free runs and aligned free blocks boot keeps track of.
const MAX_FREE_RUNS: usize = 1024;
const MAX_FREE_BLOCKS: usize = 4096;

/// Boot's working memory, used once on CPU 0 before any other core starts.
struct Scratch {
    /// One byte per tracked page, for boot/free_ranges.rs.
    seen: [u8; PAGE_SLOTS],
    runs: [PageRun; MAX_FREE_RUNS],
    /// The free blocks, as first page and order.
    blocks: [(usize, u8); MAX_FREE_BLOCKS],
    /// The runs handed to the root, as first page and page count.
    free: [(usize, usize); ROOT_UNTYPED_SLOTS],
    image: [ImageRun; MAPPED_RUNS],
}

static mut SCRATCH: Scratch = Scratch {
    seen: [0; PAGE_SLOTS],
    runs: [PageRun { first: 0, count: 0 }; MAX_FREE_RUNS],
    blocks: [(0, 0); MAX_FREE_BLOCKS],
    free: [(0, 0); ROOT_UNTYPED_SLOTS],
    image: [const { ImageRun { virt: 0, phys: 0, pages: 0, writable: false, executable: false } }; MAPPED_RUNS],
};

// The kernel is built in a stretch boot zeroes, so zero must be a valid CapKernel. Const evaluation
// rejects a value holding an invalid bit pattern.
const _: CapKernel = unsafe { core::mem::MaybeUninit::zeroed().assume_init() };

unsafe extern "C" {
    /// The first and past-the-last bytes of the kernel's image, as the linker placed it.
    static __ehdr_start: u8;
    static _end: u8;
}

/// What user mode starts with on the root thread.
pub struct Entry {
    pub pc: *const core::ffi::c_void,
    pub sp: *mut core::ffi::c_void,
}

/// Builds the capability kernel and its root process from what the loader handed over, prints each
/// fixed slot of the root's table with its kind, loads the root's space on core 0 and makes the root's
/// thread core 0's current thread. Returns where dom0 starts. The root's thread is the only thread;
/// core 0 enters it next.
pub fn boot(boot_info: &BootInfo) -> Entry {
    let dom0 = boot_info.dom0.as_ref().expect("no dom0 to boot");
    let listed = &boot_info.pages[..boot_info.pages.len().min(PAGE_SLOTS)];
    let reserved = ByteRange { base: dom0.reserved_start as u64, size: dom0.reserved_size as u64 };
    let runs = &dom0.runs[..mapped_runs(&dom0.runs, reserved.base, reserved.size)];

    // Set aside: the stretch for the boot objects and the kernel, then each 2M region of dom0's runs.
    let mut aside = [ByteRange { base: 0, size: 0 }; 1 + MAPPED_RUNS];
    for (k, run) in runs.iter().enumerate() {
        let first = run.phys / REGION_BYTES * REGION_BYTES;
        let end = (run.phys + run.pages * PAGE_BYTES).div_ceil(REGION_BYTES) * REGION_BYTES;
        aside[1 + k] = ByteRange { base: first, size: end - first };
    }
    let regions = &aside[1..1 + runs.len()];
    let stretch_pages = BOOT_OBJECT_PAGES + size_of::<CapKernel>().div_ceil(PAGE_BYTES as usize) as u64;
    let stretch = available_stretch(listed, stretch_pages, BOOT_OBJECT_PAGES, regions)
        .expect("no free stretch for the capability kernel");
    aside[0] = ByteRange { base: stretch, size: stretch_pages * PAGE_BYTES };
    let aside = &aside[..1 + runs.len()];
    log::info!("capability kernel at {:#x}, {} pages with the root's boot objects", stretch, stretch_pages);

    let image_start = &raw const __ehdr_start as u64;
    let kernel_image = ByteRange { base: image_start, size: &raw const _end as u64 - image_start };

    // Only CPU 0 runs, and it runs this once.
    let scratch = unsafe { &mut *&raw mut SCRATCH };
    let run_count = free_page_ranges(listed, &mut scratch.seen, aside, kernel_image, Some(reserved), &mut scratch.runs);
    let free = largest_blocks(&scratch.runs[..run_count], &mut scratch.blocks, &mut scratch.free);
    for (k, run) in runs.iter().enumerate() {
        scratch.image[k] = ImageRun {
            virt: (run.virt / PAGE_BYTES) as usize,
            phys: (run.phys / PAGE_BYTES) as usize,
            pages: run.pages as usize,
            writable: run.writable,
            executable: run.executable,
        };
    }
    let image = &scratch.image[..runs.len()];

    // The stretch is free memory no one else holds; the kernel and the boot objects start from zero.
    unsafe { core::ptr::write_bytes(stretch as *mut u8, 0, (stretch_pages * PAGE_BYTES) as usize) };
    let page = |index: u64| (stretch + index * PAGE_BYTES) as usize;
    let process = page(PROCESS_PAGE);
    let kernel = unsafe { &mut *(page(BOOT_OBJECT_PAGES) as *mut CapKernel) };

    let mut kernel_entries = Array::<usize, KERNEL_MEM_END_L4INDEX>::new();
    for index in 0..KERNEL_MEM_END_L4INDEX {
        kernel_entries.set(index, unsafe { *(boot_info.pml4 as *const usize).add(index) });
    }
    let held = kernel.kernel_init(
        page(LIST_ROOT_PAGE),
        Tracked::assume_new(),
        kernel_entries,
        Array::<bool, NUM_IOMMUS>::new(),
        CommandBuffers { buffers: Array::new(), pages: Tracked::assume_new() },
        process,
        page(LEAF_PAGE),
        page(FRAMES_PAGE),
        page(THREAD_PAGE),
        free,
        image,
        Tracked::assume_new(),
    );
    let (untyped, frames) = held.expect("the capability kernel refused the boot memory or dom0's runs");

    log::info!("root holds {} untyped and {} frames", untyped, frames);
    let fixed = [ROOT_PROCESS_SLOT, ROOT_THREAD_SLOT, ROOT_CONSOLE_SLOT]
        .into_iter()
        .chain(ROOT_UNTYPED_SLOT..ROOT_UNTYPED_SLOT + untyped)
        .chain(ROOT_FRAME_SLOT..ROOT_FRAME_SLOT + frames);
    for index in fixed {
        let (node, payload) = kernel.tables.lookup(&kernel.list, process, index).expect("a fixed slot is a slot");
        assert!(kernel.list.get(node).live, "root slot {} is empty", index);
        log::info!(
            "root slot {}: {} base {:#x} order {} rights {:#x}",
            index,
            kind_name(payload.kind),
            payload.base,
            payload.order,
            payload.rights
        );
    }

    let pcid = kernel.load_space(0, process);
    crate::arch::switch_address_space(process + SPACE_ROOT_PAGE * PAGE_BYTES as usize, pcid);
    kernel.enter_boot_thread(0, page(THREAD_PAGE));
    *CAP_KERNEL.lock() = Some(kernel);

    Entry {
        pc: dom0.entry_point,
        sp: unsafe { dom0.virt_start.add(dom0.reserved_size - PAGE_BYTES as usize) }.cast(),
    }
}

/// The address of the first `count` available pages in a row in the loader's list, starting at a
/// multiple of `align` pages, none of them in `avoid`. The list holds one entry per page in address
/// order; an entry out of place breaks a stretch.
fn available_stretch(
    listed: &[(u64, PhysicalMemoryType)],
    count: u64,
    align: u64,
    avoid: &[ByteRange],
) -> Option<u64> {
    let mut run_start = 0;
    for (index, &(address, kind)) in listed.iter().enumerate() {
        let index = index as u64;
        let usable = kind == PhysicalMemoryType::Available
            && address == index * PAGE_BYTES
            && !avoid.iter().any(|range| range.overlaps_page(address));
        if !usable {
            run_start = index + 1;
            continue;
        }
        let start = run_start.next_multiple_of(align);
        if index + 1 == start + count {
            return Some(start * PAGE_BYTES);
        }
    }
    None
}

/// Splits the free runs into maximal aligned blocks, as the verified boot step does, and writes the
/// largest at `free`, largest first, one run per block, at most as many as the root has untyped
/// slots. The rest stay unused: design/root-process-at-boot/. The first is the largest, so the
/// root's first untyped pays for its space's tables.
fn largest_blocks<'a>(
    runs: &[PageRun],
    blocks: &mut [(usize, u8)],
    free: &'a mut [(usize, usize); ROOT_UNTYPED_SLOTS],
) -> &'a [(usize, usize)] {
    let mut count = 0;
    for run in runs {
        let mut first = (run.first / PAGE_BYTES) as usize;
        let mut left = run.count as usize;
        while left > 0 {
            let (order, size) = first_block(first, left, MAX_ORDER);
            assert!(count < blocks.len(), "free memory makes more than {} blocks", blocks.len());
            blocks[count] = (first, order);
            count += 1;
            first += size;
            left -= size;
        }
    }
    let mut taken = 0;
    for order in (0..=MAX_ORDER).rev() {
        for &(first, _) in blocks[..count].iter().filter(|block| block.1 == order) {
            if taken < free.len() {
                free[taken] = (first, 1usize << order);
                taken += 1;
            }
        }
    }
    log::info!("free memory: {} runs, {} aligned blocks, the root takes the {} largest", runs.len(), count, taken);
    &free[..taken]
}

/// The word the serial log names a capability's kind by.
fn kind_name(kind: CapKind) -> &'static str {
    match kind {
        CapKind::Untyped => "untyped",
        CapKind::Frame => "frame",
        CapKind::Process => "process",
        CapKind::Thread => "thread",
        CapKind::Endpoint => "endpoint",
        CapKind::Reply => "reply",
        CapKind::Notification => "notification",
        CapKind::Space => "space",
        CapKind::Device => "device",
        CapKind::Console => "console",
    }
}
