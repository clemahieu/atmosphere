mod allocator;
mod map;
mod paging;
mod userspace;

use core::num::NonZeroU64;
use core::{fmt, ops::DerefMut};

use aelf::PAddr;

use astd::boot::PhysicalMemoryType;
use astd::heapless::Vec as ArrayVec;
use astd::memory::PageProtection;
use astd::sync::Mutex;
use aelf::{VirtualMapper, ContiguousMapping};

pub use allocator::set_bootstrap_region;
pub use map::MemoryMap;
pub use paging::{AddressSpace, HUGE_PAGE_SIZE, PAGE_SIZE};
pub use userspace::UserspaceMapper;

pub const MAX_PHYSICAL_MEMORY: usize = 16 * 1024 * 1024 * 1024; // 16 GiB
/// Page tables for the 4 GiB identity map are about 8 MiB. The upper half of this pool must stay
/// unwritten: tools/check-boot-stack.py. design/test-guest-memory/.
pub const BOOTSTRAP_SIZE: usize = 32 * 1024 * 1024; // 32 MiB
/// Holds the kernel window and dom0's window. design/test-guest-memory/.
pub const ALLOCATOR_SIZE: usize = 128 * 1024 * 1024; // 128 MiB

/// The physical memory map.
static PHYSICAL_MEMORY_MAP: Mutex<MemoryMap<BootMemoryType>> = Mutex::new(MemoryMap::empty());

/// The memory region reserved for the initial allocator.
static ALLOCATOR_MEMORY_REGION: Mutex<Option<MemoryRange>> = Mutex::new(None);

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

impl AcpiMemoryType {
    /// The type a memory map entry's raw type field names, or `None` for a value the table does
    /// not define.
    pub fn from_u32(value: u32) -> Option<Self> {
        match value {
            1 => Some(Self::Memory),
            2 => Some(Self::Reserved),
            3 => Some(Self::Acpi),
            4 => Some(Self::Nvs),
            5 => Some(Self::Unusable),
            6 => Some(Self::Disabled),
            _ => None,
        }
    }
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
    let filtered_regions = regions.filter(|(r, _)| {
        r.base() < MAX_PHYSICAL_MEMORY as u64
    });
    *map = MemoryMap::new(filtered_regions.map(|(r, t)| (r, BootMemoryType::Other(t))));

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

/// One page entry per address from 0 up to `cover`. Returns how many of those pages are available.
///
/// `relabel` appends the unsplit remainder of a region at the end of the map, out of address order.
/// The walk only moves forward, so it would record that span as reserved on the way to a later
/// region and then skip the remainder. Sorting first keeps those pages.
pub fn record_boot_pages<const N: usize>(
    map: &mut MemoryMap<BootMemoryType>,
    pages: &mut ArrayVec<(u64, PhysicalMemoryType), N>,
    cover: u64,
) -> usize {
    map.sort();
    let mut free_page_count = 0;
    let mut cur = 0u64;
    for (region, label) in map.regions.iter() {
        if pages.is_full() {
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
            if pages.is_full() {
                break;
            }

            pages
                .push((cur, PhysicalMemoryType::Reserved))
                .expect("Too many pages");
            cur += PAGE_SIZE as u64;
        }
        while cur < region.end_inclusive() {
            if pages.is_full() {
                break;
            }

            if page_type == PhysicalMemoryType::Available {
                free_page_count = free_page_count + 1;
            }
            pages.push((cur, page_type)).expect("Too many pages");
            cur += PAGE_SIZE as u64;
        }
    }
    while cur < cover {
        if pages.is_full() {
            break;
        }

        pages
            .push((cur, PhysicalMemoryType::Reserved))
            .expect("Too many pages");
        cur += PAGE_SIZE as u64;
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
        let page = PAGE_SIZE as u64;
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

        let mut pages: ArrayVec<(u64, PhysicalMemoryType), 16> = ArrayVec::new();
        let free = record_boot_pages(&mut map, &mut pages, 10 * page);
        for offset in [5 * page, 6 * page] {
            let kind = pages
                .iter()
                .find(|(addr, _)| *addr == offset)
                .map(|(_, kind)| *kind);
            assert_eq!(
                kind,
                Some(PhysicalMemoryType::Available),
                "page {offset:#x} in {pages:?}"
            );
        }
        assert_eq!(free, 4, "{pages:?}");
    }
}
