//! Paging.

use core::ffi::c_void;
use core::mem::{self, MaybeUninit};
use core::ptr;

use bit_field::BitField;

use crate::memory::PhysicalAllocator;

pub const PAGE_SIZE: usize = 4096;
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
            Leaf::Small => PAGE_SIZE as u64,
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

const LEVEL_MASK: u64 = 0b1_1111_1111;

/// The number of bits in a physical address.
///
/// This is also called M in the Intel manual.
const MAXPHYADDR: u64 = 56;

/// The number of bits to represent offsets in a 4KiB page.
const PAGE_SHIFT: u64 = 12;

/// The size of a regular 4KiB page.
const PAGE_SZ: u64 = 4096;

/// Bitmask to get the page in a linear address.
const PAGE_MASK: u64 = !(PAGE_SZ - 1);

/// Bitmask to get the physical address.
const PHYSICAL_MASK: u64 = (1u64 << MAXPHYADDR) - 1u64;

/// Bitmask to get the physical page address.
const PHYSICAL_PAGE_MASK: u64 = PAGE_MASK & PHYSICAL_MASK;

pub struct AddressSpace {
    pml4: *mut PageTable,
}

#[repr(transparent)]
struct PageTable {
    entries: [MaybeUninit<Entry>; 512],
}

#[repr(transparent)]
#[derive(Clone, Copy)]
struct Entry(u64);

impl AddressSpace {
    pub fn new(allocator: &mut impl PhysicalAllocator) -> Self {
        let pml4 = unsafe { Self::allocate_page_table(allocator) };

        Self { pml4 }
    }

    pub fn pml4(&self) -> *const c_void {
        self.pml4 as *const _
    }

    pub unsafe fn map(
        &mut self,
        allocator: &mut impl PhysicalAllocator,
        vaddr: u64,
        paddr: u64,
        user: bool,
        leaf: Leaf,
        cache_disable: bool,
    ) {
        assert!(vaddr % leaf.size() == 0, "vaddr is unaligned");
        assert!(paddr % leaf.size() == 0, "paddr is unaligned");

        let mut cur = self.pml4;

        for level in 0..leaf.level() {
            let index = Self::index(vaddr, level);
            let mut entry = (*cur).read(index);

            if !entry.present() {
                let new_table = Self::allocate_page_table(allocator);
                entry = Entry::new()
                    .with_present(true)
                    .with_read_write(true)
                    .with_address(new_table as u64)
                    .with_user(user);
                (*cur).write(index, entry);
            }

            assert!(!entry.page_size_bit(), "a 2M leaf maps {:#x}", vaddr);

            cur = entry.address() as *mut PageTable;
        }

        let index = Self::index(vaddr, leaf.level());
        let entry = Entry::new()
            .with_present(true)
            .with_read_write(true)
            .with_address(paddr)
            .with_page_size_bit(leaf == Leaf::Large)
            .with_cache_disable(cache_disable)
            .with_user(user);

        (*cur).write(index, entry);
    }

    unsafe fn allocate_page_table(allocator: &mut impl PhysicalAllocator) -> *mut PageTable {
        let table =
            { allocator.allocate_physical(mem::size_of::<PageTable>()).0 } as *mut PageTable;

        if table as u64 & (1u64 << PAGE_SHIFT - 1) != 0 {
            panic!("Got unaligned page");
        }

        ptr::write_volatile(table, PageTable::zeroed());

        table
    }

    /// Maps `start` up to `end` with 4K entries: each 2M leaf that overlaps the range becomes a
    /// page table whose entries map the same addresses with the leaf's user and cache-disable bits.
    /// The TLB keeps the leaves until the caller flushes them.
    pub unsafe fn use_small_pages(
        &mut self,
        allocator: &mut impl PhysicalAllocator,
        start: u64,
        end: u64,
    ) {
        let mut vaddr = start - start % Leaf::Large.size();
        while vaddr < end {
            let mut cur = self.pml4;
            for level in 0..Leaf::Large.level() {
                let entry = (*cur).read(Self::index(vaddr, level));
                assert!(entry.present() && !entry.page_size_bit());
                cur = entry.address() as *mut PageTable;
            }
            let index = Self::index(vaddr, Leaf::Large.level());
            let leaf = (*cur).read(index);
            assert!(leaf.present());
            if leaf.page_size_bit() {
                let table = Self::allocate_page_table(allocator);
                for page in 0..512 {
                    let entry = Entry::new()
                        .with_present(true)
                        .with_read_write(true)
                        .with_address(leaf.address() + page as u64 * PAGE_SZ)
                        .with_cache_disable(leaf.cache_disable())
                        .with_user(leaf.user());
                    (*table).write(page, entry);
                }
                let entry = Entry::new()
                    .with_present(true)
                    .with_read_write(true)
                    .with_address(table as u64)
                    .with_user(leaf.user());
                (*cur).write(index, entry);
            }
            vaddr += Leaf::Large.size();
        }
    }

    /// Removes the mapping of a 4K page, so that any access to it faults once the caller has
    /// flushed its TLB entry.
    pub unsafe fn unmap(&mut self, vaddr: u64) {
        let mut cur = self.pml4;
        for level in 0..3 {
            let entry = (*cur).read(Self::index(vaddr, level));
            assert!(entry.present() && !entry.page_size_bit());
            cur = entry.address() as *mut PageTable;
        }
        (*cur).write(Self::index(vaddr, 3), Entry::new());
    }

    fn index(address: u64, level: usize) -> usize {
        match level {
            0 => ((address >> 39) & LEVEL_MASK) as usize,
            1 => ((address >> 30) & LEVEL_MASK) as usize,
            2 => ((address >> 21) & LEVEL_MASK) as usize,
            3 => ((address >> 12) & LEVEL_MASK) as usize,
            _ => panic!("Invalid level"),
        }
    }
}

impl PageTable {
    const fn zeroed() -> Self {
        unsafe { mem::transmute(MaybeUninit::<Self>::zeroed()) }
    }

    unsafe fn read(&self, index: usize) -> Entry {
        ptr::read_volatile(self.entry(index))
    }

    unsafe fn write(&self, index: usize, value: Entry) {
        ptr::write_volatile(self.entry(index), value)
    }

    const fn entry(&self, index: usize) -> *mut Entry {
        self.entries[index].as_ptr() as *mut Entry
    }
}

impl Entry {
    const fn new() -> Self {
        Self(0)
    }

    fn present(&self) -> bool {
        (self.0 & 0b1) == 1
    }

    fn address(&self) -> u64 {
        PHYSICAL_PAGE_MASK & self.0
    }

    fn page_size_bit(&self) -> bool {
        self.0.get_bit(7)
        //(self.0 & (1 << 7)) != 0
    }

    fn with_present(mut self, present: bool) -> Self {
        self.0 = (self.0 & !(0b1)) | (if present { 1 } else { 0 });
        self
    }

    fn with_read_write(mut self, read_write: bool) -> Self {
        self.0.set_bit(1, read_write);
        self
    }

    fn user(&self) -> bool {
        self.0.get_bit(2)
    }

    fn cache_disable(&self) -> bool {
        self.0.get_bit(4)
    }

    fn with_user(mut self, user: bool) -> Self {
        self.0.set_bit(2, user);
        self
    }

    fn with_cache_disable(mut self, cache_disable: bool) -> Self {
        self.0.set_bit(4, cache_disable);
        self
    }

    fn with_address(mut self, address: u64) -> Self {
        let masked = PHYSICAL_PAGE_MASK & address;
        self.0 = self.0 & !(PHYSICAL_PAGE_MASK) | masked;
        self
    }

    fn with_page_size_bit(mut self, page_size: bool) -> Self {
        self.0.set_bit(7, page_size);
        self
    }
}

#[cfg(test)]
mod tests {
    use std::alloc::{alloc_zeroed, Layout};

    use aelf::PAddr;

    use super::*;

    /// Hands out host pages and counts them. A table's address is then a pointer the walk can
    /// follow, as under the identity map.
    struct HostPages {
        count: usize,
    }

    impl PhysicalAllocator for HostPages {
        unsafe fn allocate_physical(&mut self, size: usize) -> PAddr {
            assert_eq!(size, PAGE_SIZE);
            self.count += 1;
            PAddr(alloc_zeroed(Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap()) as u64)
        }
    }

    /// What `vaddr` translates to, with its leaf's size and its user and cache-disable bits.
    fn translate(space: &AddressSpace, vaddr: u64) -> Option<(u64, Leaf, bool, bool)> {
        let mut cur = space.pml4;
        for level in 0..4 {
            let entry = unsafe { (*cur).read(AddressSpace::index(vaddr, level)) };
            if !entry.present() {
                return None;
            }
            let leaf = match (level, entry.page_size_bit()) {
                (2, true) => Leaf::Large,
                (3, _) => Leaf::Small,
                (_, false) => {
                    cur = entry.address() as *mut PageTable;
                    continue;
                }
                (_, true) => panic!("a leaf at level {level}"),
            };
            let paddr = entry.address() + vaddr % leaf.size();
            return Some((paddr, leaf, entry.user(), entry.cache_disable()));
        }
        unreachable!()
    }

    const LARGE: u64 = LARGE_PAGE_SIZE as u64;
    const SMALL: u64 = PAGE_SIZE as u64;

    /// 4 GiB of 2M leaves, as `load` maps them, and the tables they took.
    fn identity_map(pages: &mut HostPages) -> AddressSpace {
        let mut space = AddressSpace::new(pages);
        let mut cur = 0;
        while cur < 0x1_0000_0000 {
            unsafe { space.map(pages, cur, cur, false, Leaf::Large, false) };
            cur += LARGE;
        }
        space
    }

    #[test]
    fn large_leaves_map_4_gib_in_six_tables() {
        let mut pages = HostPages { count: 0 };
        let space = identity_map(&mut pages);
        // One PML4, one PDPT and four page directories.
        assert_eq!(pages.count, 6);
        for vaddr in [0, 0x1234_5678, 0xfee0_0000, 0xffff_ffff] {
            assert_eq!(translate(&space, vaddr), Some((vaddr, Leaf::Large, false, false)));
        }
        assert_eq!(translate(&space, 0x1_0000_0000), None);
    }

    #[test]
    fn small_pages_keep_the_translation_and_unmap_by_the_page() {
        let mut pages = HostPages { count: 0 };
        let mut space = identity_map(&mut pages);
        // A range that ends one page into the next 2M stretch takes both stretches' leaves.
        let (start, end) = (5 * LARGE - 3 * SMALL, 5 * LARGE + SMALL);
        unsafe { space.use_small_pages(&mut pages, start, end) };
        assert_eq!(pages.count, 8);
        for vaddr in [4 * LARGE, start, 5 * LARGE - 1, 5 * LARGE, 6 * LARGE - 1] {
            assert_eq!(translate(&space, vaddr), Some((vaddr, Leaf::Small, false, false)));
        }
        for vaddr in [4 * LARGE - 1, 6 * LARGE] {
            assert_eq!(translate(&space, vaddr), Some((vaddr, Leaf::Large, false, false)));
        }

        // A stretch that already has a page table takes no other.
        unsafe { space.use_small_pages(&mut pages, start, end) };
        assert_eq!(pages.count, 8);

        unsafe { space.unmap(start) };
        assert_eq!(translate(&space, start), None);
        for vaddr in [start - 1, start + SMALL] {
            assert_eq!(translate(&space, vaddr), Some((vaddr, Leaf::Small, false, false)));
        }
    }

    #[test]
    fn small_pages_keep_the_leaf_s_user_and_cache_disable_bits() {
        let mut pages = HostPages { count: 0 };
        let mut space = AddressSpace::new(&mut pages);
        let (virt, phys) = (0x80_0000_0000, 7 * LARGE);
        unsafe {
            space.map(&mut pages, virt, phys, true, Leaf::Large, true);
            space.use_small_pages(&mut pages, virt, virt + SMALL);
        }
        let last = LARGE - SMALL;
        assert_eq!(translate(&space, virt + last), Some((phys + last, Leaf::Small, true, true)));
    }

    #[test]
    #[should_panic(expected = "paddr is unaligned")]
    fn a_large_leaf_takes_a_2m_aligned_frame() {
        let mut pages = HostPages { count: 0 };
        let mut space = AddressSpace::new(&mut pages);
        unsafe { space.map(&mut pages, LARGE, LARGE + SMALL, false, Leaf::Large, false) };
    }

    #[test]
    #[should_panic(expected = "a 2M leaf maps")]
    fn a_small_page_does_not_map_under_a_large_leaf() {
        let mut pages = HostPages { count: 0 };
        let mut space = identity_map(&mut pages);
        unsafe { space.map(&mut pages, LARGE, LARGE, false, Leaf::Small, false) };
    }

    #[test]
    fn test_level_index() {
        let address: u64 = 0x7f2ec7045000;
        assert_eq!(AddressSpace::index(address, 0), 0xfe);
        assert_eq!(AddressSpace::index(address, 1), 0xbb);
        assert_eq!(AddressSpace::index(address, 2), 0x38);
        assert_eq!(AddressSpace::index(address, 3), 0x45);
    }
}
