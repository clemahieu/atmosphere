// SPDX-License-Identifier: MIT

//! What the instruction set fixes, one implementation per target, selected by target_arch. Each
//! implementation defines the same items with the same specs, so code above this module does not know
//! which ISA it runs on. See design/arch-module/.
//!
//! The tokens the glue hands the capability kernel are defined here, once for both targets. Their
//! fields are private to this module and its per-target submodules, so no code above it can build
//! one: proof code cannot write the struct, and verified code cannot call Tracked::assume_new, which
//! Verus marks external. Only the glue that does what a token attests makes it.
use vstd::prelude::*;

verus! {

/// What a write of a core's page-table base register proves: core `core()` now translates through the
/// table whose top level is at `root()`, filling its TLB under tag `tag()`, the PCID or ASID written
/// with it. Only load_translation_root makes one.
// The fields are read only by specs, which a build that is not verifying erases.
#[allow(dead_code)]
pub tracked struct Translating {
    ghost core: int,
    ghost root: usize,
    ghost tag: usize,
}

impl Translating {
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

/// What a flush cleared: every context on a core, or all of an IOMMU's IOTLB.
pub ghost enum FlushTarget {
    Core(int),
    Iommu(int),
}

/// What a flush of `target()`, started when the epoch was `epoch()`, proves. Only flush glue can make
/// one, so only it can clear a model of what the target holds: flush_every_context for a core,
/// invalidate_iommu_all for an IOMMU.
// The fields are read only by specs, which a build that is not verifying erases.
#[allow(dead_code)]
pub tracked struct Flushed {
    ghost target: FlushTarget,
    ghost epoch: int,
}

impl Flushed {
    pub closed spec fn target(self) -> FlushTarget {
        self.target
    }

    pub closed spec fn epoch(self) -> int {
        self.epoch
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
