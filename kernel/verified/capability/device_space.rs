//! A device space's map: the space a device walks through its IOMMU. A device address reaches the map
//! only as a DeviceRange, which only DeviceRange::new makes, so no other kind of address can map as one.
//! A space's kind decides which map it takes, and a device space has no kernel slots, so a device's
//! address may use the low entries a process's root keeps for the kernel. See
//! design/address-spaces-as-objects/.
use vstd::prelude::*;

verus! {

use super::kernel::*;
#[cfg(verus_keep_ghost)]
use super::link::*;
#[cfg(verus_keep_ghost)]
use super::mapping::*;
#[cfg(verus_keep_ghost)]
use super::reach::*;
use super::space::*;
#[cfg(verus_keep_ghost)]
use super::view::*;
use crate::define::*;

/// The first address past those a device space's four levels of table translate.
pub const DEVICE_ADDRESS_END: usize = SIZE_512G * ENTRIES;

/// The bytes of the page a device range covers, 4K or, if large, 2M.
pub open spec fn device_range_bytes(large: bool) -> usize {
    if large { SIZE_2M } else { PAGE_SZ }
}

/// The indices of a device address's page, level 4 first. A large page's level 1 index goes unused.
pub open spec fn device_path(base: usize, large: bool) -> SpacePath {
    SpacePath {
        l4: (base >> L4_SHIFT) & INDEX_MASK,
        l3: (base >> L3_SHIFT) & INDEX_MASK,
        l2: (base >> L2_SHIFT) & INDEX_MASK,
        l1: if large { 0 } else { (base >> L1_SHIFT) & INDEX_MASK },
    }
}

/// One page of a device address space, its address checked to fit four levels of table and aligned to the
/// page.
pub struct DeviceRange {
    base: usize,
    large: bool,
}

impl DeviceRange {
    pub closed spec fn base(self) -> usize {
        self.base
    }

    pub closed spec fn large(self) -> bool {
        self.large
    }

    pub open spec fn path(self) -> SpacePath {
        device_path(self.base(), self.large())
    }

    /// The range of the page at `base`, which comes from user space and so can be refused.
    pub fn new(base: usize, large: bool) -> (ret: Option<DeviceRange>)
        ensures
            ret is Some == (base < DEVICE_ADDRESS_END && base % device_range_bytes(large) == 0),
            ret is Some ==> ret->0.base() == base && ret->0.large() == large,
    {
        let bytes: usize = if large { SIZE_2M } else { PAGE_SZ };
        if base >= DEVICE_ADDRESS_END || base % bytes != 0 {
            return None;
        }
        Some(DeviceRange { base, large })
    }
}

impl CapKernel {
    /// The refusals of a device map: those of a map, or of a large map for a large range, at the range's
    /// path, in a space that must be a device space.
    pub open spec fn can_map_device(&self, root: usize, slot: usize, r: DeviceRange, from: usize, page: usize) -> bool {
        if r.large() {
            self.can_map_large(root, slot, SpaceKind::Device, r.path(), from, page)
        } else {
            self.can_map(root, slot, SpaceKind::Device, r.path(), from, page)
        }
    }

    /// Maps the page at offset `page` of the frame capability at index `from` at the range `r` of the device
    /// space named at index `slot`. The indices and the offset come from user space, so any of them can be
    /// refused, and a refusal changes nothing.
    pub fn map_device(&mut self, root: usize, slot: usize, r: DeviceRange, from: usize, page: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            ret == old(self).can_map_device(root, slot, r, from, page),
            final(self).spaces.loaded == old(self).spaces.loaded,
            !ret ==> *final(self) == *old(self),
            ret && r.large() ==> Self::map_large_done(*old(self), *final(self), root, slot, r.path(), from, page),
            ret && !r.large() ==> Self::map_done(*old(self), *final(self), root, slot, r.path(), from, page),
            ret ==> discharges(
                old(self).view(),
                final(self).view(),
                root,
                Effect::Share { space: old(self).tables.node_of(root, slot), from: old(self).tables.node_of(root, from) },
            ),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let l4 = (r.base >> L4_SHIFT) & INDEX_MASK;
        let l3 = (r.base >> L3_SHIFT) & INDEX_MASK;
        let l2 = (r.base >> L2_SHIFT) & INDEX_MASK;
        let ret = if r.large {
            self.map_large_kind(root, slot, SpaceKind::Device, l4, l3, l2, from, page)
        } else {
            self.map_kind(root, slot, SpaceKind::Device, l4, l3, l2, (r.base >> L1_SHIFT) & INDEX_MASK, from, page)
        };
        ret
    }

    /// A device root holds no kernel entry: each low entry is empty or names one of the space's table pages.
    pub proof fn lemma_device_root_no_kernel_entry(&self, s: usize, i: usize)
        requires
            self.wf(),
            self.spaces.roots@.contains_key(s),
            self.spaces.records@[s].value().kind is Device,
            i < KERNEL_MEM_END_L4INDEX,
        ensures
            ({
                let tree = tree_of(&self.table_pages, &self.spaces);
                let e = tree.entry(s, i);
                e.is_empty() || (tree.names_child(s, i) && tree.is_page((e.addr - TABLE_NODE_PAGES * PAGE_SZ) as usize))
            }),
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert(space_wf(&self.list, &self.spaces, &self.blocks, s));
        assert(self.spaces.roots@[s].value()[i] == self.spaces.roots@[s].value()[i]);
        self.lemma_root_table(s);
    }
}

} // verus!
