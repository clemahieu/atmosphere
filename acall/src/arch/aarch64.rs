// SPDX-License-Identifier: MIT

//! aarch64's translation of a process's own pages, VMSAv8-64 stage 1 with the 4 KiB granule.
use vstd::prelude::*;

use verified::capability::kernel::CapKernel;

#[cfg(verus_keep_ghost)]
use super::{translates, translation_premises};

verus! {

/// Core `core` translates `address` through the space keyed at `root` of `kernel` to page `page`, and
/// an EL0 load or store there reaches that page's bytes: the walk from the core's TTBR0_EL1 reads the
/// table descriptors at lookup levels 0 to 2 and the page descriptor at level 3 the path names, the
/// page descriptor gives the page's base (Arm ARM D8.2.8, D8.3.1.1, D8.3.1.2), AP[2:1] = 01 lets EL0
/// read and write (D8.4.1.2.1, Table D8-63), and no table descriptor above it limits that through
/// APTable (D8.4.1.2.2, Table D8-64). A leaf may hold AF clear, and a writable one is written with DBM
/// and AP[2] set; an access through it sets AF and a write clears AP[2], by the walker where hardware
/// management is on and otherwise by the kernel's fault handler, after which the access is retried
/// (D8.5.1, D8.5.2), so the access reaches the page either way. The core may cache the
/// translation; the model holds every translation it caches, and the premises say the space's are what
/// its tables give or point at pages a space maps. There is no instruction: the guarantee is a standing
/// property of the walk, so the body is empty.
// cite: arm-arm D8.2.8 VMSAv8-64 translation using the 4KB granule
// cite: arm-arm D8.3.1.1 VMSAv8-64 Table descriptor format
// cite: arm-arm D8.3.1.2 VMSAv8-64 Block descriptor and Page descriptor formats
// cite: arm-arm D8.4.1.2.1 Stage 1 data accesses using Direct permissions, Table D8-63
// cite: arm-arm D8.4.1.2.2 Hierarchical control of data access Direct permissions, Table D8-64
// cite: arm-arm D8.5.1 The Access flag
// cite: arm-arm D8.5.2 The dirty state
pub assume_specification[translates_page](kernel: Ghost<CapKernel>, root: Ghost<usize>, core: Ghost<int>, address: Ghost<usize>, page: Ghost<usize>)
    requires
        translation_premises(kernel@, root@, core@, address@, page@),
    ensures
        translates(core@, address@, page@),
    no_unwind;

} // verus!

pub fn translates_page(_kernel: Ghost<CapKernel>, _root: Ghost<usize>, _core: Ghost<int>, _address: Ghost<usize>, _page: Ghost<usize>) {}
