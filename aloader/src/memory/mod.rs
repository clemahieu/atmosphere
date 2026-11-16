// SPDX-License-Identifier: MIT

mod allocator;
mod map;
mod paging;
mod userspace;

/// The walk again, over the aarch64 entry, which is arithmetic alone: the host's tests run the walk
/// over both targets' entries. They call less of it than the loader does.
#[cfg(all(test, not(target_arch = "aarch64")))]
#[allow(dead_code)]
#[path = "."]
mod aarch64 {
    use crate::arch::aarch64::Entry;

    #[path = "paging.rs"]
    mod paging;
}

use core::num::NonZeroU64;
use core::{fmt, ops::DerefMut};

use aelf::PAddr;

use astd::boot::{page_end, PhysicalMemoryType, PhysicalRange, DOM0_RESERVATION, PAGE_BYTES};
use astd::heapless::Vec as ArrayVec;
use astd::memory::PageProtection;
use astd::sync::Mutex;
use aelf::{VirtualMapper, ContiguousMapping};

use crate::arch::Entry;

pub use allocator::{bootstrap_pages_used, set_bootstrap_region};
pub use map::MemoryMap;
pub use paging::AddressSpace;
pub use userspace::UserspaceMapper;

/// The most memory the loader keeps in its map: a region is cut here, so the identity map ends here
/// at the most.
pub const MAX_PHYSICAL_MEMORY: usize = 16 * 1024 * 1024 * 1024; // 16 GiB
/// The least the identity map covers: 4 GiB, which holds the 32-bit device window just below it.
/// design/test-guest-memory/.
pub const IDENTITY_MAP_FLOOR: u64 = 1 << 32;
/// The granule the kernel rounds the end of its tracked pages up to.
const GIB: u64 = 1 << 30;
/// The loader's page tables are at most 30 pages: 18 for an identity map of the 16 GiB the map
/// keeps, a PML4, a PDPT and a page directory a GiB, 5 for the 4K entries of a kernel image at its
/// bound and the stack's guard, 7 MiB wherever they start, and 7 for dom0's window and its payload.
/// The pool is 128 pages, so the upper half stays unwritten: tools/check-boot-stack.py.
/// design/test-guest-memory/.
pub const BOOTSTRAP_SIZE: usize = 512 * 1024; // 512 KiB
/// The kernel window and dom0's window, which are all the loader reserves from it: 12 MiB.
/// design/test-guest-memory/.
pub const ALLOCATOR_SIZE: usize = crate::KERNEL_RESERVATION + DOM0_RESERVATION as usize;

/// The physical memory map.
static PHYSICAL_MEMORY_MAP: Mutex<MemoryMap<BootMemoryType>> = Mutex::new(MemoryMap::empty());

/// The memory region reserved for the initial allocator.
static ALLOCATOR_MEMORY_REGION: Mutex<Option<MemoryRange>> = Mutex::new(None);

pub const LARGE_PAGE_SIZE: usize = 2 * 1024 * 1024;

/// The page a leaf entry maps.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Leaf {
    /// 4 KiB, by a page table's entry.
    Small,
    /// 2 MiB, by a page directory's entry.
    Large,
}

impl Leaf {
    pub const fn size(self) -> u64 {
        match self {
            Leaf::Small => PAGE_BYTES,
            Leaf::Large => LARGE_PAGE_SIZE as u64,
        }
    }

    /// The level of the table that holds the leaf, the PML4 being level 0.
    const fn level(self) -> usize {
        match self {
            Leaf::Small => 3,
            Leaf::Large => 2,
        }
    }
}

pub trait PhysicalAllocator {
    /// Allocates physical memory.
    unsafe fn allocate_physical(&mut self, size: usize) -> PAddr;
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BootMemoryType {
    Bios,
    Loader,
    LoaderAllocator,
    Kernel,
    Domain,
    DomainImage,
    Payload,
    PageTable,
    KernelPageTable,
    Pci,
    Other(AcpiMemoryType),
}

impl From<BootMemoryType> for PhysicalMemoryType {
    fn from(value: BootMemoryType) -> Self {
        use BootMemoryType as BMT;
        use PhysicalMemoryType as PMT;
        match value {
            // free up loader and domain image for unlimited use
            BMT::LoaderAllocator => PMT::Available,
            BMT::Loader => PMT::Available,
            BMT::DomainImage => PMT::Available,

            BMT::Kernel => PMT::Kernel,

            // Payloads are loaded onto dom0's address space
            BMT::Domain | BMT::Payload => PMT::Domain,
            BMT::PageTable => PMT::PageTable,

            BMT::Other(AcpiMemoryType::Memory) => PMT::Available,

            BMT::Bios => PMT::Reserved,
            _ => PMT::Reserved,
        }
    }
}

/// Type of a physical address range.
///
/// As defined in ACPI, Table 14-1 Address Range Types:
/// <https://uefi.org/sites/default/files/resources/ACPI_4_Errata_A.pdf>
#[repr(u32)]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[non_exhaustive]
pub enum AcpiMemoryType {
    /// This range is available RAM usable by the operating system.
    Memory = 1,

    /// This range of addresses is in use or reserved by the system and is not to be included in the allocatable memory pool of the operating system's memory manager.
    Reserved = 2,

    /// ACPI Reclaim Memory.
    ///
    /// This range is available RAM usable by the OS after it reads the ACPI tables.
    Acpi = 3,

    /// ACPI NVS Memory.
    ///
    /// This range of addresses is in use or reserve by the system and must not be used by the operating system. This range is required to be saved and restored across an NVS sleep.
    Nvs = 4,

    /// This range of addresses contains memory in which errors have been detected. This range must not be used by OSPM.
    Unusable = 5,

    /// This range of addresses contains memory that is not enabled. This range must not be used by OSPM.
    Disabled = 6,
}

/// A range of memory, denoted by the base address and size.
#[derive(Debug, Clone, PartialEq)]
pub struct MemoryRange {
    base: u64,
    size: NonZeroU64,
}

impl MemoryRange {
    pub fn new(base: u64, size: u64) -> Self {
        Self {
            base,
            size: NonZeroU64::new(size).unwrap(),
        }
    }

    pub fn set_size(&mut self, size: u64) {
        self.size = NonZeroU64::new(size).unwrap();
    }

    pub const fn base(&self) -> u64 {
        self.base
    }

    pub const fn size(&self) -> u64 {
        self.size.get()
    }

    pub const fn end_inclusive(&self) -> u64 {
        self.base + self.size.get() - 1
    }

    pub const fn intersects(&self, other: &MemoryRange) -> bool {
        (self.base <= other.end_inclusive()) && (self.end_inclusive() >= other.base)
    }

    pub const fn contains(&self, address: u64) -> bool {
        (self.base <= address) && (address <= self.end_inclusive())
    }

    pub const fn fully_contains(&self, other: &MemoryRange) -> bool {
        (self.base <= other.base) && (self.end_inclusive() >= other.end_inclusive())
    }
}

impl fmt::Display for MemoryRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:#016x}-{:#016x} ({:#x})",
            self.base(),
            self.end_inclusive(),
            self.size()
        )
    }
}

pub fn init_physical_memory_map(
    regions: impl Iterator<Item = (MemoryRange, AcpiMemoryType)>,
    loader_range: MemoryRange,
    image_ranges: impl Iterator<Item = MemoryRange>,
) {
    let mut map = PHYSICAL_MEMORY_MAP.lock();
    let kept_regions = regions.filter_map(|(r, t)| Some((kept(r)?, BootMemoryType::Other(t))));
    *map = MemoryMap::new(kept_regions);

    map.relabel(MemoryRange::new(0, 1024 * 1024), BootMemoryType::Bios);
    map.relabel(loader_range, BootMemoryType::Loader);
    map.relabel(allocator::get_bootstrap_range(), BootMemoryType::PageTable);

    for image in image_ranges {
        map.relabel(image, BootMemoryType::DomainImage);
    }

    map.sort();

    // Reserve region for bump allocator
    let mut reserved_region = ALLOCATOR_MEMORY_REGION.lock();
    let first_memory = map
        .regions
        .iter()
        .find(|(r, t)| {
            t == &BootMemoryType::Other(AcpiMemoryType::Memory) && r.size() > ALLOCATOR_SIZE as u64
        })
        .expect("No usable memory region");

    let allocator_region = MemoryRange::new(first_memory.0.base(), ALLOCATOR_SIZE as u64);
    map.relabel(allocator_region.clone(), BootMemoryType::LoaderAllocator);

    log::debug!(
        "Reserved region for dynamic allocator: {:#x?}",
        allocator_region,
    );
    *reserved_region = Some(allocator_region.clone());
}

/// `region` cut at `MAX_PHYSICAL_MEMORY`, or none when it starts there or past it.
fn kept(region: MemoryRange) -> Option<MemoryRange> {
    let max = MAX_PHYSICAL_MEMORY as u64;
    (region.base() < max)
        .then(|| MemoryRange::new(region.base(), region.size().min(max - region.base())))
}

/// Where the identity map ends: at the end of the highest RAM in `map`, a region of any kind the
/// kernel is handed as other than Reserved, rounded up to a GiB, and at `IDENTITY_MAP_FLOOR` at the
/// least. The kernel tracks every page below that rounded end and reads and writes them through
/// this map, so it maps every page the kernel tracks. Allocation and relabelling after this only
/// split RAM, and moving a range's edges out to pages stays inside its GiB, so the end the kernel
/// computes from the ranges it is handed is no higher. design/page-metadata-sized-from-the-memory-map/.
pub fn identity_map_end(map: &MemoryMap<BootMemoryType>) -> u64 {
    map.regions
        .iter()
        .filter(|(_, label)| PhysicalMemoryType::from(*label) != PhysicalMemoryType::Reserved)
        .map(|(region, _)| (region.base() + region.size()).next_multiple_of(GIB))
        .fold(IDENTITY_MAP_FLOOR, u64::max)
}

pub fn dump_physical_memory_map() {
    let mut map = PHYSICAL_MEMORY_MAP.lock();

    map.sort();

    for (region, label) in &map.regions {
        log::info!("{:<100} {:?}", region, label);
    }
}

pub unsafe fn init() {
    if let Some(reserved_region) = get_allocator_region() {
        allocator::init(
            reserved_region.base() as *mut u8,
            reserved_region.size() as usize,
        );
    } else {
        panic!("No region was reserved for the allocator");
    }
}

/// The allocator over the bootstrap region. The loader runs on one core and calls this once, from
/// `main`, so the reference it returns is the only one.
pub fn bootstrap_allocator() -> &'static mut (impl PhysicalAllocator + VirtualMapper) {
    // Exclusive: see above.
    unsafe { &mut *&raw mut allocator::BOOTSTRAP_ALLOCATOR }
}

pub fn reserve(
    size: usize,
    label: BootMemoryType,
) -> (*mut u8, impl PhysicalAllocator + VirtualMapper) {
    // Exclusive: the loader runs on one core, and the reference lives only for this call.
    let allocator = unsafe { (*&raw mut allocator::ALLOCATOR).reserve(size) };

    let mut map = PHYSICAL_MEMORY_MAP.lock();
    map.relabel(allocator.range(), label);

    (allocator.base(), allocator)
}

pub fn get_allocator_region() -> Option<MemoryRange> {
    ALLOCATOR_MEMORY_REGION.lock().clone()
}

pub fn get_physical_memory_map() -> impl DerefMut<Target = MemoryMap<BootMemoryType>> {
    PHYSICAL_MEMORY_MAP.lock()
}

/// The map as the ranges the kernel is handed, in address order: each region with its edges moved
/// to pages, and neighbours of one type merged. Returns how many pages are available.
///
/// A page two regions share goes to the lower one, and a page a region shares with a gap below it
/// goes to no range.
///
/// `relabel` appends the unsplit remainder of a region at the end of the map, out of address order.
/// The walk only moves forward, so it would step over that remainder on the way to a later region.
/// Sorting first keeps those pages.
pub fn record_boot_ranges<const N: usize>(
    map: &mut MemoryMap<BootMemoryType>,
    ranges: &mut ArrayVec<PhysicalRange, N>,
) -> u64 {
    map.sort();
    let mut free_page_count = 0;
    let mut cur = 0u64;
    for (region, label) in map.regions.iter() {
        let kind: PhysicalMemoryType = (*label).into();
        log::info!(
            "region.base() {:x}, region.end_inclusive() {:x}, page_type {:?}, label {:?}",
            region.base(),
            region.end_inclusive(),
            kind,
            *label
        );
        let start = page_end(region.base()).max(cur);
        let end = page_end(region.base() + region.size());
        if end <= start {
            continue;
        }
        cur = end;
        if kind == PhysicalMemoryType::Available {
            free_page_count += (end - start) / PAGE_BYTES;
        }
        match ranges.last_mut() {
            Some(last) if last.kind == kind && last.base + last.bytes == start => {
                last.bytes += end - start;
            }
            _ => ranges
                .push(PhysicalRange {
                    base: start,
                    bytes: end - start,
                    kind,
                })
                .expect("The memory map has more ranges than the kernel is handed"),
        }
    }
    free_page_count
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `reserve` relabels a span of the loader allocator. `relabel` appends the unsplit tail, so a
    /// higher region already in the map leaves that tail out of address order.
    #[test]
    fn allocator_remainder_out_of_order_is_not_dropped() {
        let page = PAGE_BYTES;
        let mut map = MemoryMap::new([
            (MemoryRange::new(0, page), BootMemoryType::Bios),
            (
                MemoryRange::new(page, 8 * page),
                BootMemoryType::Other(AcpiMemoryType::Memory),
            ),
            (
                MemoryRange::new(9 * page, page),
                BootMemoryType::Other(AcpiMemoryType::Reserved),
            ),
        ]);
        // The allocator carve, then the kernel window and dom0's window, each a prefix of what remains.
        map.relabel(
            MemoryRange::new(page, 6 * page),
            BootMemoryType::LoaderAllocator,
        );
        map.relabel(MemoryRange::new(page, 3 * page), BootMemoryType::Kernel);
        map.relabel(MemoryRange::new(4 * page, page), BootMemoryType::Domain);

        let (tail, tail_label) = map.regions.last().cloned().expect("map empty");
        assert_eq!(
            tail_label,
            BootMemoryType::LoaderAllocator,
            "{:?}",
            map.regions
        );
        assert_eq!(tail.base(), 5 * page, "{:?}", map.regions);
        assert_eq!(tail.size(), 2 * page, "{:?}", map.regions);
        assert!(
            map.regions
                .iter()
                .any(|(region, _)| region.base() > tail.base()),
            "remainder at {:#x} should sit behind a higher region: {:?}",
            tail.base(),
            map.regions
        );

        let mut ranges: ArrayVec<PhysicalRange, 16> = ArrayVec::new();
        let free = record_boot_ranges(&mut map, &mut ranges);
        let range = |base, pages, kind| PhysicalRange {
            base: base * page,
            bytes: pages * page,
            kind,
        };
        // The tail at pages 5 and 6 and the untouched memory at 7 and 8 are one available range.
        assert_eq!(
            ranges.as_slice(),
            [
                range(0, 1, PhysicalMemoryType::Reserved),
                range(1, 3, PhysicalMemoryType::Kernel),
                range(4, 1, PhysicalMemoryType::Domain),
                range(5, 4, PhysicalMemoryType::Available),
                range(9, 1, PhysicalMemoryType::Reserved),
            ]
        );
        assert_eq!(free, 4, "{ranges:?}");
    }

    /// The initrd's length is whatever the file's is, so its region ends inside a page and the
    /// rest of its allocation starts there. A region can also start inside a page after a gap.
    #[test]
    fn region_edges_inside_a_page_move_to_pages() {
        let page = PAGE_BYTES;
        let mut map = MemoryMap::new([
            (
                MemoryRange::new(0, page + 0x200),
                BootMemoryType::DomainImage,
            ),
            (
                MemoryRange::new(page + 0x200, page - 0x200),
                BootMemoryType::Other(AcpiMemoryType::Reserved),
            ),
            (
                MemoryRange::new(2 * page, page),
                BootMemoryType::Other(AcpiMemoryType::Reserved),
            ),
            (
                MemoryRange::new(5 * page + 0x800, page + 0x800),
                BootMemoryType::Other(AcpiMemoryType::Memory),
            ),
        ]);

        let mut ranges: ArrayVec<PhysicalRange, 16> = ArrayVec::new();
        let free = record_boot_ranges(&mut map, &mut ranges);
        assert_eq!(
            ranges.as_slice(),
            [
                PhysicalRange {
                    base: 0,
                    bytes: 2 * page,
                    kind: PhysicalMemoryType::Available,
                },
                PhysicalRange {
                    base: 2 * page,
                    bytes: page,
                    kind: PhysicalMemoryType::Reserved,
                },
                PhysicalRange {
                    base: 6 * page,
                    bytes: page,
                    kind: PhysicalMemoryType::Available,
                },
            ]
        );
        assert_eq!(free, 3, "{ranges:?}");
    }

    /// RAM that ends below 4 GiB leaves the map at 4 GiB, which holds the 32-bit device window.
    #[test]
    fn identity_map_reaches_four_gib_at_least() {
        let map = MemoryMap::new([
            (MemoryRange::new(0, 2 * GIB + GIB / 2), BootMemoryType::Other(AcpiMemoryType::Memory)),
            (MemoryRange::new(0xfec0_0000, 0x10_0000), BootMemoryType::Other(AcpiMemoryType::Reserved)),
        ]);
        assert_eq!(identity_map_end(&map), 4 * GIB);
    }

    /// RAM above 4 GiB, as q35 places what does not fit below its 32-bit window, moves the end to
    /// that RAM's end rounded up to a GiB, where the kernel's tracked pages end.
    #[test]
    fn identity_map_reaches_the_tracked_end_of_ram_above_four_gib() {
        let map = MemoryMap::new([
            (MemoryRange::new(0, 2 * GIB), BootMemoryType::Other(AcpiMemoryType::Memory)),
            (MemoryRange::new(4 * GIB, GIB + GIB / 2), BootMemoryType::Other(AcpiMemoryType::Memory)),
        ]);
        assert_eq!(identity_map_end(&map), 6 * GIB);
    }

    /// Every kind the kernel is handed as other than Reserved is RAM and moves the end; a Reserved
    /// range, such as a device window above RAM, does not.
    #[test]
    fn identity_map_end_follows_the_kinds_the_kernel_tracks() {
        let low = (MemoryRange::new(0, GIB), BootMemoryType::Other(AcpiMemoryType::Memory));
        for label in [
            BootMemoryType::Loader,
            BootMemoryType::LoaderAllocator,
            BootMemoryType::Kernel,
            BootMemoryType::Domain,
            BootMemoryType::DomainImage,
            BootMemoryType::Payload,
            BootMemoryType::PageTable,
            BootMemoryType::Other(AcpiMemoryType::Memory),
        ] {
            let map = MemoryMap::new([low.clone(), (MemoryRange::new(8 * GIB, PAGE_BYTES), label)]);
            assert_eq!(identity_map_end(&map), 9 * GIB, "{label:?}");
        }
        for label in [
            BootMemoryType::Bios,
            BootMemoryType::Pci,
            BootMemoryType::KernelPageTable,
            BootMemoryType::Other(AcpiMemoryType::Reserved),
            BootMemoryType::Other(AcpiMemoryType::Acpi),
            BootMemoryType::Other(AcpiMemoryType::Nvs),
        ] {
            let map = MemoryMap::new([low.clone(), (MemoryRange::new(8 * GIB, PAGE_BYTES), label)]);
            assert_eq!(identity_map_end(&map), 4 * GIB, "{label:?}");
        }
    }

    /// A region that crosses the most memory the loader keeps is cut there, and one wholly past it
    /// is dropped, so the identity map, and the page tables it takes, stop there.
    #[test]
    fn regions_past_the_most_memory_kept_are_cut() {
        let max = MAX_PHYSICAL_MEMORY as u64;
        assert_eq!(kept(MemoryRange::new(0, GIB)), Some(MemoryRange::new(0, GIB)));
        assert_eq!(kept(MemoryRange::new(max - GIB, 2 * GIB)), Some(MemoryRange::new(max - GIB, GIB)));
        assert_eq!(kept(MemoryRange::new(max, GIB)), None);
    }
}
