// SPDX-License-Identifier: MIT

//! What the instruction set fixes, one implementation per target, selected by target_arch. Each
//! implementation defines the same items with the same specs, so code above this module does not know
//! which ISA it runs on. See design/arch-module/.
//!
//! The tokens the glue and the capability kernel pass are defined here, once for both targets. Their
//! fields are private to this module and its per-target submodules, so no code above it can build or
//! change one: proof code cannot write the struct, and verified code cannot call Tracked::assume_new,
//! which Verus marks external. Only the glue that does what a token attests makes or changes it, but for
//! TlbModel::grow and IotlbModel::grow, by which proof code may add to a model of what a TLB holds,
//! since a model that holds more claims less.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::capability::kernel::TlbEntry;

verus! {

/// Core `core()`'s page-table base register: the core translates through the table whose top level is
/// at `root()`, filling its TLB under tag `tag()`, the PCID or ASID written with it. The kernel value
/// holds one for each core, made at boot for the root the loader left there, and load_translation_root
/// writes the register only through it, so what it says is the register's latest write.
// Only specs read the fields, and a cargo build erases specs, so only Verus compiles them.
pub tracked struct BaseRegister {
    #[cfg(verus_keep_ghost)]
    ghost core: int,
    #[cfg(verus_keep_ghost)]
    ghost root: usize,
    #[cfg(verus_keep_ghost)]
    ghost tag: usize,
}

impl BaseRegister {
    pub closed spec fn core(self) -> int {
        self.core
    }

    pub closed spec fn root(self) -> usize {
        self.root
    }

    pub closed spec fn tag(self) -> usize {
        self.tag
    }
}

/// What each core's TLB may hold that the kernel's model tracks: one set of entries per core, indexed
/// by core. The kernel value holds the one boot makes, with every set empty. Proof code may add to the
/// sets, since a model that holds more claims less, and only flush_every_context empties a set, so a
/// core's model is emptied only by a flush of that core: design/flush-without-waiting/.
// Only specs read the field, and a cargo build erases specs, so only Verus compiles it.
pub tracked struct TlbModel {
    #[cfg(verus_keep_ghost)]
    ghost held: Seq<Set<TlbEntry>>,
}

impl TlbModel {
    pub closed spec fn len(self) -> nat {
        self.held.len()
    }

    pub closed spec fn spec_index(self, c: int) -> Set<TlbEntry> {
        self.held[c]
    }

    /// Each core's model becomes `held`'s set for it, which holds all it held.
    pub proof fn grow(tracked &mut self, held: Seq<Set<TlbEntry>>)
        requires
            held.len() == old(self).len(),
            forall|c: int| 0 <= c < held.len() ==> old(self)[c].subset_of(#[trigger] held[c]),
        ensures
            final(self).len() == old(self).len(),
            forall|c: int| 0 <= c < held.len() ==> #[trigger] final(self)[c] == held[c],
    {
        self.held = held;
    }
}

/// What each IOMMU's IOTLB may hold that its device spaces' tables no longer say: one set of entries per
/// IOMMU, indexed by IOMMU. The kernel value holds the one boot makes, with every set empty. Proof code
/// may add to the sets, and only invalidate_iommu_all empties one, once the IOMMU has finished the
/// invalidate, so an IOMMU's model is emptied only by an invalidate that no unmap came after:
/// design/flush-without-waiting/.
// Only specs read the field, and a cargo build erases specs, so only Verus compiles it.
pub tracked struct IotlbModel {
    #[cfg(verus_keep_ghost)]
    ghost held: Seq<Set<TlbEntry>>,
}

impl IotlbModel {
    pub closed spec fn len(self) -> nat {
        self.held.len()
    }

    pub closed spec fn spec_index(self, i: int) -> Set<TlbEntry> {
        self.held[i]
    }

    /// Each IOMMU's model becomes `held`'s set for it, which holds all it held.
    pub proof fn grow(tracked &mut self, held: Seq<Set<TlbEntry>>)
        requires
            held.len() == old(self).len(),
            forall|i: int| 0 <= i < held.len() ==> old(self)[i].subset_of(#[trigger] held[i]),
        ensures
            final(self).len() == old(self).len(),
            forall|i: int| 0 <= i < held.len() ==> #[trigger] final(self)[i] == held[i],
    {
        self.held = held;
    }
}

} // verus!

#[cfg(target_arch = "x86_64")]
mod x86_64;
#[cfg(target_arch = "x86_64")]
pub use x86_64::*;
#[cfg(target_arch = "aarch64")]
mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::*;
