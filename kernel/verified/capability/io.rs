//! An IO space's map. An IO address reaches the map only as an IoRange, which only IoRange::new makes, so
//! no other kind of address can map as one. A space's kind decides which map it takes, and an IO space
//! has no kernel slots, so a device's address may use the low entries a process's root keeps for the
//! kernel. See design/address-spaces-as-objects/.
use vstd::prelude::*;

verus! {

use super::kernel::*;
use super::link::*;
use super::map::*;
use super::mapping::*;
use super::reach::*;
use super::space::*;
use super::view::*;
use crate::define::*;

/// The first address past those an IO table of four levels translates.
pub const IO_ADDRESS_END: usize = 0x1_0000_0000_0000;

/// The bytes of the page an IO range covers, 4K or, if large, 2M.
pub open spec fn io_range_bytes(large: bool) -> usize {
    if large { 0x20_0000 } else { 0x1000 }
}

/// The indices of an IO address's page, level 4 first. A large page's level 1 index goes unused.
pub open spec fn io_path(base: usize, large: bool) -> SpacePath {
    SpacePath {
        l4: (base >> 39) & 511,
        l3: (base >> 30) & 511,
        l2: (base >> 21) & 511,
        l1: if large { 0 } else { (base >> 12) & 511 },
    }
}

/// One page of an IO address space, its address checked to fit an IO table and aligned to the page.
pub struct IoRange {
    base: usize,
    large: bool,
}

impl IoRange {
    pub closed spec fn base(self) -> usize {
        self.base
    }

    pub closed spec fn large(self) -> bool {
        self.large
    }

    pub open spec fn path(self) -> SpacePath {
        io_path(self.base(), self.large())
    }

    /// The range of the page at `base`, which comes from user space and so can be refused.
    pub fn new(base: usize, large: bool) -> (ret: Option<IoRange>)
        ensures
            ret is Some == (base < IO_ADDRESS_END && base % io_range_bytes(large) == 0),
            ret is Some ==> ret->0.base() == base && ret->0.large() == large,
    {
        let bytes: usize = if large { 0x20_0000 } else { 0x1000 };
        if base >= IO_ADDRESS_END || base % bytes != 0 {
            return None;
        }
        Some(IoRange { base, large })
    }
}

impl CapKernel {
    /// The refusals of an IO map: those of a map, or of a large map for a large range, at the range's
    /// path, in a space that must be an IO space.
    pub open spec fn can_map_io(&self, root: usize, slot: usize, r: IoRange, from: usize, page: usize) -> bool {
        if r.large() {
            self.can_map_large(root, slot, SpaceKind::Io, r.path(), from, page)
        } else {
            self.can_map(root, slot, SpaceKind::Io, r.path(), from, page)
        }
    }

    /// Maps the page at offset `page` of the frame capability at index `from` at the range `r` of the IO
    /// space named at index `slot`. The indices and the offset come from user space, so any of them can
    /// be refused, and a refusal changes nothing.
    pub fn map_io(&mut self, root: usize, slot: usize, r: IoRange, from: usize, page: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            ret == old(self).can_map_io(root, slot, r, from, page),
            final(self).spaces.loaded == old(self).spaces.loaded,
            !ret ==> *final(self) == *old(self),
            ret && r.large() ==> Self::map_large_done(*old(self), *final(self), root, slot, r.path(), from, page),
            ret && !r.large() ==> Self::map_done(*old(self), *final(self), root, slot, r.path(), from, page),
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
    {
        let l4 = (r.base >> 39) & 511;
        let l3 = (r.base >> 30) & 511;
        let l2 = (r.base >> 21) & 511;
        if r.large {
            self.map_large_kind(root, slot, SpaceKind::Io, l4, l3, l2, from, page)
        } else {
            self.map_kind(root, slot, SpaceKind::Io, l4, l3, l2, (r.base >> 12) & 511, from, page)
        }
    }

    /// An IO root holds no kernel entry: each low entry is empty or names one of the space's table pages.
    pub proof fn lemma_io_root_no_kernel_entry(&self, s: usize, i: usize)
        requires
            self.wf(),
            self.spaces.roots@.contains_key(s),
            self.spaces.records@[s].value().kind is Io,
            i < KERNEL_MEM_END_L4INDEX,
        ensures
            ({
                let tree = tree_of(&self.table_pages, &self.spaces);
                let e = tree.entry(s, i);
                e.is_empty() || (tree.names_child(s, i) && tree.is_page((e.addr - TABLE_NODE_PAGES * 4096) as usize))
            }),
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert(space_wf(&self.list, &self.spaces, &self.blocks, s));
        assert(self.spaces.roots@[s].value()[i] == self.spaces.roots@[s].value()[i]);
        self.lemma_root_table(s);
    }
}

} // verus!
