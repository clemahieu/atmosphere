// SPDX-License-Identifier: MIT

//! The default heap allocator for user space, verified with Verus.
//!
//! The heap sits over a span source and holds no capability. `source` states the source's contract;
//! `arch` names the page and block sizes the target's translation fixes, which the rest of the crate
//! counts in. `buddy` cuts page runs out of one block; `page` cuts them out of spans of two blocks
//! it reserves from the source, a block buddy per block, both kept in the span's metadata page, the
//! first page of its second block. `class` names the size classes, each a slot size and the order
//! of the runs its slabs are cut from. `slab` cuts one backed run into slots of one size, with a record
//! that keeps no permission: its caller holds the permission to each free slot in a map. `large`
//! keeps each object over one block in a span of its own, recorded in a node in the span's record
//! page, the nodes linked into one list. `list` links slab records through their links, the list of
//! a size class's partial or full slabs, holding the permission to each. `record` keeps each slab's record in record pages the page
//! buddy cuts and the heap backs itself, the pages linked into one list. `small` keeps one size
//! class: its partial and full slabs on two lists and the permissions to their free slots, taking a
//! slot from a partial slab or from a new one it cuts, backs and records. `heap` holds a size class
//! per class over one record store and one page buddy, under one invariant, and allocates and frees
//! slots of the class a layout fits. `witness` holds verified
//! uses of the contract, of the buddies, of the size classes, of the slab, of the large-object map,
//! of the record store and of the heap, built into no image.
#![no_std]
// A cargo build erases specifications and proofs, so there a variable only they read looks unused,
// and one only they borrow mutably looks as if it need not be mutable.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_mut))]

pub mod arch;
pub mod buddy;
pub mod class;
pub mod heap;
pub mod large;
pub mod list;
pub mod page;
pub mod record;
pub mod slab;
pub mod small;
pub mod source;
#[cfg(throwaway)]
mod throwaway;
#[cfg(verus_keep_ghost)]
mod witness;
