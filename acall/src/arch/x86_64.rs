// SPDX-License-Identifier: MIT

//! x86_64's translation of a process's own pages, long mode with 4-level paging and 4 KiB pages.
use vstd::prelude::*;

use verified::capability::kernel::CapKernel;

#[cfg(verus_keep_ghost)]
use super::{translates, translation_premises};

verus! {

/// Core `core` translates `address` through the space keyed at `root` of `kernel` to page `page`, and
/// a user-mode load or store there reaches that page's bytes: the walk from the core's CR3 reads the
/// PML4, PDPT and PD entries and the PTE the path names, the leaf gives the page's base (APM 2 5.3.3),
/// and a user write is allowed where R/W and U/S are set at every level of the walk (5.6.1, 5.6.2, 5.8,
/// Table 5-2). The core may cache the translation (5.5); the model holds every translation it caches,
/// and the premises say the space's are what its tables give or point at pages a space maps. There is
/// no instruction: the guarantee is a standing property of the walk, so the body is empty.
// cite: amd-apm2 5.3.3 4-Kbyte Page Translation
// cite: amd-apm2 5.5 Translation-Lookaside Buffer (TLB)
// cite: amd-apm2 5.6.1 User/Supervisor (U/S) Bit
// cite: amd-apm2 5.6.2 Read/Write (R/W) Bit
// cite: amd-apm2 5.8 Protection Across Paging Hierarchy, Table 5-2
pub assume_specification[translates_page](kernel: Ghost<CapKernel>, root: Ghost<usize>, core: Ghost<int>, address: Ghost<usize>, page: Ghost<usize>)
    requires
        translation_premises(kernel@, root@, core@, address@, page@),
    ensures
        translates(core@, address@, page@),
    no_unwind;

} // verus!

pub fn translates_page(_kernel: Ghost<CapKernel>, _root: Ghost<usize>, _core: Ghost<int>, _address: Ghost<usize>, _page: Ghost<usize>) {}
