//! Boot manager handoff.

use core::ffi::c_void;
use core::ptr;

use crate::heapless::Vec as ArrayVec;
use crate::string::ArrayString;

/// The type of physical memory.
///
/// This is a simplified version of `BootMemoryType` in aloader.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
pub enum PhysicalMemoryType {
    /// Used by the kernel.
    Kernel,

    /// Used by page tables.
    PageTable,

    /// Used by a domain.
    Domain,

    /// Available to be allocated.
    Available,

    /// Reserved for other use.
    Reserved,
}

/// A stretch of physical memory of one type in the loader's memory map.
///
/// The base and the length are multiples of [`PAGE_BYTES`], and no two ranges of a map share a
/// page. The kernel checks both at the trust boundary. An address in no range is not memory the
/// kernel may use.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PhysicalRange {
    /// Physical address of the range's first byte.
    pub base: u64,
    /// Length of the range.
    pub bytes: u64,
    /// What the memory holds.
    pub kind: PhysicalMemoryType,
}

/// How many ranges [`BootInfo::memory`] holds. Firmware lists each of its allocations, more than
/// a hundred under OVMF; the loader merges neighbours of one type, which leaves the test guest
/// 21. design/test-guest-memory/.
pub const MEMORY_RANGES: usize = 256;

/// Boot manager handoff information.
#[repr(C)]
#[derive(Debug, Clone)]
pub struct BootInfo {
    /// The kernel command line.
    pub command_line: ArrayString<4096>,

    /// The page table.
    pub pml4: *const c_void,

    /// The initial domain.
    pub dom0: Option<DomainMapping>,

    /// The payload mapped into dom0.
    pub payload: Option<Payload>,

    /// The memory map: every range the loader knows of, with its type, in address order.
    pub memory: ArrayVec<PhysicalRange, MEMORY_RANGES>,

    /// Whether Tagged TLB is enabled.
    pub pcide: bool,

    /// The base of the IOMMU remapping hardware registers.
    pub iommu_base: Option<u64>,
}

/// A loaded domain.
///
/// The loader only loads and relocates the ELF in identity-mapped memory.
/// The kernel is responsible for setting up everything else.
#[repr(C)]
#[derive(Debug, Clone)]
pub struct DomainMapping {
    /// The beginning of the contiguous reserved space (physical).
    pub reserved_start: *mut u8,

    /// The size of the reserved space.
    pub reserved_size: usize,

    /// The beginning of the virtual address.
    pub virt_start: *mut u8,

    /// The load bias of the domain.
    ///
    /// load_addr = load_bias + vaddr
    pub load_bias: usize,

    /// The entry point.
    pub entry_point: *const c_void,

    /// The runs the loader mapped for this domain: each ELF segment, the stack and the payload.
    ///
    /// A page shared by two segments is one run, so the runs are page-disjoint. The kernel checks
    /// the list at the trust boundary before it builds the root's space from it.
    /// Why that check is tier 3: design/trust-boundary/.
    pub runs: ArrayVec<MappedRun, MAPPED_RUNS>,
}

/// Bytes in a page: the one definition outside the verified kernel, whose `PAGE_SZ` the kernel's
/// boot code checks it against. Runs and the loader's map are in these.
pub const PAGE_BYTES: u64 = 4096;

/// How many runs `DomainMapping` holds. Segments, the stack and the payload fit, including a
/// shared page split out of two segments.
pub const MAPPED_RUNS: usize = 64;

/// Bytes the loader reserves for dom0. The virtual reservation is this long, above the user base.
/// The test guest's dom0 image is under 1 MiB. design/test-guest-memory/.
pub const DOM0_RESERVATION: u64 = 16 * 1024 * 1024;

/// The stack the loader maps at the top of dom0's reservation.
pub const DOM0_STACK: u64 = 1024 * 1024;

/// One contiguous mapping the loader made for dom0.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MappedRun {
    /// Virtual address of the run's first page.
    pub virt: u64,
    /// Physical address of the run's first page.
    pub phys: u64,
    /// Number of pages in the run.
    pub pages: u64,
    /// The pages are writable.
    pub writable: bool,
    /// The pages are executable.
    pub executable: bool,
}

/// A segment's pages before runs that share a page are split apart.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SegmentSpan {
    /// Virtual address of the segment's first page.
    pub virt: u64,
    /// Number of pages the segment covers.
    pub pages: u64,
    /// The segment is writable.
    pub writable: bool,
    /// The segment is executable.
    pub executable: bool,
}

/// The first address of the page `address` falls in.
pub fn page_start(address: u64) -> u64 {
    address & !(PAGE_BYTES - 1)
}

/// The first address of the page after the one `address` falls in, or `address` when it is aligned.
pub fn page_end(address: u64) -> u64 {
    address.saturating_add(PAGE_BYTES - 1) & !(PAGE_BYTES - 1)
}

/// Folds segments into page-disjoint runs.
///
/// A page covered by more than one segment becomes one run whose rights are the union, which is
/// how the loader keeps two segments that meet inside a page from being two runs. `phys_of` is the
/// physical address of a virtual page. Returns how many runs were written, or `None` when they do
/// not fit in `out` or a span's end overflows.
pub fn disjoint_page_runs(
    segments: &[SegmentSpan],
    mut phys_of: impl FnMut(u64) -> u64,
    out: &mut [MappedRun],
) -> Option<usize> {
    const BOUNDS: usize = MAPPED_RUNS;
    let mut bounds = [0u64; BOUNDS];
    let mut nbounds = 0usize;
    for segment in segments {
        if segment.pages == 0 {
            continue;
        }
        let bytes = segment.pages.checked_mul(PAGE_BYTES)?;
        let end = segment.virt.checked_add(bytes)?;
        insert_bound(&mut bounds, &mut nbounds, segment.virt)?;
        insert_bound(&mut bounds, &mut nbounds, end)?;
    }

    let mut written = 0usize;
    let mut index = 0usize;
    while index + 1 < nbounds {
        let start = bounds[index];
        let end = bounds[index + 1];
        index += 1;
        if start >= end {
            continue;
        }
        let mut covered = false;
        let mut writable = false;
        let mut executable = false;
        for segment in segments {
            if segment.pages == 0 {
                continue;
            }
            let bytes = segment.pages.checked_mul(PAGE_BYTES)?;
            let segment_end = segment.virt.checked_add(bytes)?;
            if segment.virt <= start && end <= segment_end {
                covered = true;
                writable |= segment.writable;
                executable |= segment.executable;
            }
        }
        if !covered {
            continue;
        }
        let pages = (end - start) / PAGE_BYTES;
        let phys = phys_of(start);
        if written > 0 {
            let previous = &mut out[written - 1];
            let contiguous = previous.virt + previous.pages * PAGE_BYTES == start
                && previous.phys + previous.pages * PAGE_BYTES == phys
                && previous.writable == writable
                && previous.executable == executable;
            if contiguous {
                previous.pages += pages;
                continue;
            }
        }
        if written >= out.len() {
            return None;
        }
        out[written] = MappedRun {
            virt: start,
            phys,
            pages,
            writable,
            executable,
        };
        written += 1;
    }
    Some(written)
}

fn insert_bound(bounds: &mut [u64], count: &mut usize, value: u64) -> Option<()> {
    if bounds[..*count].contains(&value) {
        return Some(());
    }
    if *count >= bounds.len() {
        return None;
    }
    let mut index = *count;
    while index > 0 && bounds[index - 1] > value {
        bounds[index] = bounds[index - 1];
        index -= 1;
    }
    bounds[index] = value;
    *count += 1;
    Some(())
}

/// A payload.
#[repr(C)]
#[derive(Debug, Clone)]
pub struct Payload {
    /// The beginning of the binary in virtual memory.
    pub base: *mut u8,

    /// The size of the binary.
    pub size: usize,
}

impl BootInfo {
    /// Creates an empty BootInfo struct.
    pub const fn empty() -> Self {
        Self {
            command_line: ArrayString::empty(),
            dom0: None,
            payload: None,
            pml4: ptr::null(),
            memory: ArrayVec::new(),
            pcide: false,
            iommu_base: None,
        }
    }
}
