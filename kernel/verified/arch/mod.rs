// SPDX-License-Identifier: MIT

//! What the instruction set fixes, one implementation per target, selected by target_arch. Each
//! implementation defines the same items with the same specs, so code above this module does not know
//! which ISA it runs on. See design/arch-module/.
//!
//! The tokens the glue and the capability kernel pass are defined here, once for both targets. Their
//! fields are private to this module and its per-target submodules, so no code above it can build or
//! change one: proof code cannot write the struct, and verified code cannot call Tracked::assume_new,
//! which Verus marks external. Nor can code above it copy one: each holds a Unique, which is private here
//! and neither Copy nor Clone, so rustc refuses an `impl Copy` for a token wherever it is written, and a
//! `Clone` could only return the token it was given. tools/check-external-body.py refuses `unsafe` outside
//! counted glue, by which exec code could zero one up or read one out twice (core::mem::zeroed,
//! core::ptr::read), and every spec of exec code Verus does not read (a vstd `*SpecImpl`, the
//! StructuralEq derive, the exec_spec macros), by which a safe impl outside verus! could be said to
//! return a token it never made, or an earlier one. Only the glue that does what a token attests makes or changes it, but for
//! TlbModel::grow and IotlbModel::grow, by which proof code may add entries to a model of what a TLB
//! holds, since a model that holds more claims less.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::capability::kernel::TlbEntry;

verus! {

/// A field each token holds so that the token is not Copy: rustc refuses `impl Copy` for a struct with a
/// field that is not Copy, and only this module can name this type to make it Copy. Without it every
/// field of a token is ghost, hence Copy, and any module of the crate could write `impl Copy` for the
/// token and use one tracked token twice, keeping a register's record across a later write of it.
// Only Verus compiles the field that holds it, as it does the tokens' other fields.
#[cfg(verus_keep_ghost)]
struct Unique {}

/// Core `core()`'s page-table base register: the core translates through the table whose top level is
/// at `root()`, filling its TLB under tag `tag()`, the PCID or ASID written with it. The kernel value
/// holds one for each core, made at boot for the root the loader left there, and load_translation_root
/// writes the register only through it, and it cannot be copied, so what it says is the register's latest write.
// Only specs read the fields, and a cargo build erases specs, so only Verus compiles them.
pub tracked struct BaseRegister {
    #[cfg(verus_keep_ghost)]
    ghost core: int,
    #[cfg(verus_keep_ghost)]
    ghost root: usize,
    #[cfg(verus_keep_ghost)]
    ghost tag: usize,
    #[cfg(verus_keep_ghost)]
    unique: Unique,
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
/// by core, and one set of the tags, PCIDs or ASIDs, it may hold entries under. The kernel value holds
/// the one boot makes, with every set empty. Proof code may add to the sets of entries, since a model
/// that holds more claims less; load_translation_root adds the tag it writes to the core's tags; and
/// only flush_every_context empties a core's sets, so a core's model is emptied, and the tags it used
/// freed for reuse, only by a flush of that core: design/flush-without-waiting/.
// Only specs read the fields, and a cargo build erases specs, so only Verus compiles them.
pub tracked struct TlbModel {
    #[cfg(verus_keep_ghost)]
    ghost held: Seq<Set<TlbEntry>>,
    #[cfg(verus_keep_ghost)]
    ghost tags: Seq<Set<usize>>,
    #[cfg(verus_keep_ghost)]
    unique: Unique,
}

impl TlbModel {
    pub closed spec fn len(self) -> nat {
        self.held.len()
    }

    pub closed spec fn spec_index(self, c: int) -> Set<TlbEntry> {
        self.held[c]
    }

    /// The tags core c may hold entries under.
    pub closed spec fn tags(self, c: int) -> Set<usize> {
        self.tags[c]
    }

    /// Each core's model becomes `held`'s set for it, which holds all it held. The tags are kept.
    pub proof fn grow(tracked &mut self, held: Seq<Set<TlbEntry>>)
        requires
            held.len() == old(self).len(),
            forall|c: int| 0 <= c < held.len() ==> old(self)[c].subset_of(#[trigger] held[c]),
        ensures
            final(self).len() == old(self).len(),
            forall|c: int| 0 <= c < held.len() ==> #[trigger] final(self)[c] == held[c],
            forall|c: int| #[trigger] final(self).tags(c) == old(self).tags(c),
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
    #[cfg(verus_keep_ghost)]
    unique: Unique,
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
