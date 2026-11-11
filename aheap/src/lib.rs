// SPDX-License-Identifier: MIT

//! The default heap allocator for user space, verified with Verus.
//!
//! The heap sits over a span source and holds no capability. `source` states the source's contract;
//! `arch` names the page and block sizes the target's translation fixes, which the rest of the crate
//! counts in. `buddy` cuts page runs out of one block; `page` cuts them out of spans of two blocks
//! it reserves from the source, a block buddy per block, both kept in the span's metadata page, the
//! first page of its second block. `witness` holds verified uses of the contract and of the buddies,
//! built into no image.
#![no_std]
// A cargo build erases specifications and proofs, so there a variable only they read looks unused.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables))]

pub mod arch;
pub mod buddy;
pub mod page;
pub mod source;
#[cfg(verus_keep_ghost)]
mod witness;
