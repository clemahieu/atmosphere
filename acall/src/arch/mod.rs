// SPDX-License-Identifier: MIT

//! What the target's translation does with the entries of a process's own space, one implementation
//! per target, selected by target_arch. Each states the same guarantee under the same name, citing its
//! own manual, over the premises this file states in the kernel's model, so the code above it holds a
//! mapped page's bytes without knowing the ISA. See design/arch-module/ and
//! design/who-vouches-for-an-unproven-claim/.
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::step::returned_clean;
#[cfg(verus_keep_ghost)]
use verified::capability::kernel::CapKernel;
#[cfg(verus_keep_ghost)]
use verified::capability::link::tree_of;
#[cfg(verus_keep_ghost)]
use verified::capability::map::{address_path, names_entry};
#[cfg(verus_keep_ghost)]
use verified::capability::mapping::{space_mapping, walk_open};
#[cfg(verus_keep_ghost)]
use verified::define::{NUM_CPUS, PAGE_SZ};

#[cfg(target_arch = "x86_64")]
mod x86_64;
#[cfg(target_arch = "x86_64")]
pub use x86_64::*;
#[cfg(target_arch = "aarch64")]
mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::*;

verus! {

/// Core `core`, running user code, loads and stores the bytes of the physical page whose number is
/// `page` when it reads and writes the 4 KiB page at virtual address `address`. Only the target's
/// translation guarantee, `translates_page`, says it.
pub uninterp spec fn translates(core: int, address: usize, page: usize) -> bool;

/// What the translation guarantee reads of the kernel's model `kernel`: the space keyed at `root` maps
/// the 4 KiB page at `address`, in the lower half, to physical page `page` by a present leaf that allows
/// a write and a user access, every entry its walk reads above the leaf allows both, and core `core`
/// has that space loaded and holds no translation of it to a page no space maps.
pub open spec fn translation_premises(kernel: CapKernel, root: usize, core: int, address: usize, page: usize) -> bool {
    let tree = tree_of(&kernel.table_pages, &kernel.spaces);
    let path = address_path(address as u64);
    let entry = space_mapping(tree, root)[path];
    &&& names_entry(address as u64, 1)
    &&& space_mapping(tree, root).contains_key(path)
    &&& entry.addr == (page * PAGE_SZ) as usize
    &&& entry.perm.present
    &&& !entry.perm.ps
    &&& entry.perm.write
    &&& entry.perm.user
    &&& walk_open(tree, root, path)
    &&& 0 <= core < NUM_CPUS
    &&& returned_clean(kernel, root, core)
}

} // verus!
