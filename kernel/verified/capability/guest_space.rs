// SPDX-License-Identifier: MIT

//! A guest-physical page: the address a guest's nested table translates. A guest-physical address reaches
//! a nested table only as a GuestPhysRange, which only GuestPhysRange::new makes, so no other kind of
//! address, a device's included, passes for one. A nested table has four levels and no kernel slots, so
//! every address its four levels translate is a guest-physical address. See design/vmm-over-svm/ and
//! design/address-spaces-as-objects/.
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use super::mapping::*;
use crate::define::*;

/// The first address past those a nested table's four levels translate.
pub const GUEST_PHYS_END: usize = SIZE_512G * ENTRIES;

/// The bytes of the page a guest-physical range covers, 4K or, if large, 2M.
pub open spec fn guest_range_bytes(large: bool) -> usize {
    if large { SIZE_2M } else { PAGE_SZ }
}

/// The indices of a guest-physical address's page, level 4 first. A large page's level 1 index goes
/// unused.
pub open spec fn guest_path(base: usize, large: bool) -> SpacePath {
    SpacePath {
        l4: (base >> L4_SHIFT) & INDEX_MASK,
        l3: (base >> L3_SHIFT) & INDEX_MASK,
        l2: (base >> L2_SHIFT) & INDEX_MASK,
        l1: if large { 0 } else { (base >> L1_SHIFT) & INDEX_MASK },
    }
}

/// One page of a guest's physical address space, its address checked to fit a nested table's four levels
/// and aligned to the page.
pub struct GuestPhysRange {
    base: usize,
    large: bool,
}

impl GuestPhysRange {
    pub closed spec fn base(self) -> usize {
        self.base
    }

    pub closed spec fn large(self) -> bool {
        self.large
    }

    pub open spec fn path(self) -> SpacePath {
        guest_path(self.base(), self.large())
    }

    /// The range of the page at `base`, which comes from user space and so can be refused.
    pub fn new(base: usize, large: bool) -> (ret: Option<GuestPhysRange>)
        ensures
            ret is Some == (base < GUEST_PHYS_END && base % guest_range_bytes(large) == 0),
            ret is Some ==> ret->0.base() == base && ret->0.large() == large,
    {
        let bytes: usize = if large { SIZE_2M } else { PAGE_SZ };
        if base >= GUEST_PHYS_END || base % bytes != 0 {
            return None;
        }
        Some(GuestPhysRange { base, large })
    }

    /// Whether the range is a large page, as a map of it takes the level.
    pub fn is_large(&self) -> (ret: bool)
        ensures
            ret == self.large(),
    {
        self.large
    }

    /// The indices of the range's page, level 4 first, as a map of it takes them.
    pub fn indices(&self) -> (ret: (usize, usize, usize, usize))
        ensures
            ret.0 == self.path().l4,
            ret.1 == self.path().l3,
            ret.2 == self.path().l2,
            ret.3 == self.path().l1,
    {
        let l1 = if self.large { 0 } else { (self.base >> L1_SHIFT) & INDEX_MASK };
        ((self.base >> L4_SHIFT) & INDEX_MASK, (self.base >> L3_SHIFT) & INDEX_MASK, (self.base >> L2_SHIFT) & INDEX_MASK, l1)
    }
}

} // verus!
