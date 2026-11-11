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
//! page, the nodes linked into one list. `record` keeps each slab's record in record pages the page
//! buddy cuts and the heap backs itself, the pages linked into one list. `witness` holds verified
//! uses of the contract, of the buddies, of the size classes, of the slab, of the large-object map
//! and of the record store, built into no image.
#![no_std]
// A cargo build erases specifications and proofs, so there a variable only they read looks unused.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables))]

pub mod arch;
pub mod buddy;
pub mod class;
pub mod large;
pub mod page;
pub mod record;
pub mod slab;
pub mod source;
#[cfg(verus_keep_ghost)]
mod witness;
