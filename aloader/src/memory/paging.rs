//! Paging.

use core::ffi::c_void;
use core::mem::{self, MaybeUninit};
use core::ptr;

use astd::boot::PAGE_BYTES;

// The entry the walk writes is its parent module's: the target's, and in the host's tests the
// aarch64 one as well.
use super::Entry;
use crate::memory::{Leaf, PhysicalAllocator};

const LEVEL_MASK: u64 = 0b1_1111_1111;

pub struct AddressSpace {
    pml4: *mut PageTable,
}

#[repr(transparent)]
struct PageTable {
    entries: [MaybeUninit<Entry>; 512],
}

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
                entry = Entry::table(new_table as u64, user);
                (*cur).write(index, entry);
            }

            assert!(!entry.large(), "a 2M leaf maps {:#x}", vaddr);

            cur = entry.address() as *mut PageTable;
        }

        let index = Self::index(vaddr, leaf.level());
        (*cur).write(index, Entry::leaf(paddr, leaf, user, cache_disable));
    }

    /// Maps every 2M frame below `end` at its own address, for the kernel alone. `device` says
    /// which of them are device memory.
    pub unsafe fn map_identity(
        &mut self,
        allocator: &mut impl PhysicalAllocator,
        end: u64,
        device: impl Fn(u64) -> bool,
    ) {
        let mut cur = 0;
        while cur < end {
            self.map(allocator, cur, cur, false, Leaf::Large, device(cur));
            cur += Leaf::Large.size();
        }
    }

    unsafe fn allocate_page_table(allocator: &mut impl PhysicalAllocator) -> *mut PageTable {
        let table =
            { allocator.allocate_physical(mem::size_of::<PageTable>()).0 } as *mut PageTable;

        assert!(
            table as u64 % PAGE_BYTES == 0,
            "page table at an unaligned address {:p}",
            table
        );

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
                assert!(entry.present() && !entry.large());
                cur = entry.address() as *mut PageTable;
            }
            let index = Self::index(vaddr, Leaf::Large.level());
            let leaf = (*cur).read(index);
            assert!(leaf.present());
            if leaf.large() {
                let table = Self::allocate_page_table(allocator);
                for page in 0..512 {
                    let entry = Entry::leaf(
                        leaf.address() + page as u64 * PAGE_BYTES,
                        Leaf::Small,
                        leaf.user(),
                        leaf.cache_disable(),
                    );
                    (*table).write(page, entry);
                }
                (*cur).write(index, Entry::table(table as u64, leaf.user()));
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
            assert!(entry.present() && !entry.large());
            cur = entry.address() as *mut PageTable;
        }
        (*cur).write(Self::index(vaddr, 3), Entry::empty());
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

#[cfg(test)]
mod tests {
    use std::alloc::{alloc_zeroed, Layout};

    use aelf::PAddr;

    use super::*;
    use crate::memory::LARGE_PAGE_SIZE;

    const PAGE: usize = PAGE_BYTES as usize;

    /// Hands out host pages and counts them. A table's address is then a pointer the walk can
    /// follow, as under the identity map.
    struct HostPages {
        count: usize,
    }

    impl PhysicalAllocator for HostPages {
        unsafe fn allocate_physical(&mut self, size: usize) -> PAddr {
            assert_eq!(size, PAGE);
            self.count += 1;
            PAddr(alloc_zeroed(Layout::from_size_align(PAGE, PAGE).unwrap()) as u64)
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
            let leaf = match (level, entry.large()) {
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
    const SMALL: u64 = PAGE_BYTES;

    /// 4 GiB of 2M leaves, as `load` maps them where the target calls no frame a device, and the
    /// tables they took.
    fn identity_map(pages: &mut HostPages) -> AddressSpace {
        let mut space = AddressSpace::new(pages);
        unsafe { space.map_identity(pages, 0x1_0000_0000, |_| false) };
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
    fn the_identity_map_makes_the_frames_the_target_names_device_memory() {
        let mut pages = HostPages { count: 0 };
        let mut space = AddressSpace::new(&mut pages);
        // A machine whose devices are below 1 GiB, with RAM from there.
        unsafe { space.map_identity(&mut pages, 0x1_0000_0000, |paddr| paddr < 0x4000_0000) };
        assert_eq!(pages.count, 6);
        for vaddr in [0, 0x0900_0000, 0x3fff_ffff] {
            assert_eq!(translate(&space, vaddr), Some((vaddr, Leaf::Large, false, true)));
        }
        for vaddr in [0x4000_0000, 0xffff_ffff] {
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

    /// Hands out an address `offset` bytes past a page boundary, with a page of room after it.
    struct OffsetPages {
        offset: usize,
    }

    impl PhysicalAllocator for OffsetPages {
        unsafe fn allocate_physical(&mut self, _size: usize) -> PAddr {
            let base = alloc_zeroed(Layout::from_size_align(2 * PAGE, PAGE).unwrap());
            PAddr(base as u64 + self.offset as u64)
        }
    }

    #[test]
    fn a_page_table_takes_a_page_aligned_address() {
        let table = unsafe { AddressSpace::allocate_page_table(&mut OffsetPages { offset: 0 }) };
        assert_eq!(table as usize % PAGE, 0);
    }

    #[test]
    #[should_panic(expected = "page table at an unaligned address")]
    fn a_page_table_does_not_take_an_address_unaligned_in_a_low_bit() {
        unsafe { AddressSpace::allocate_page_table(&mut OffsetPages { offset: 8 }) };
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
