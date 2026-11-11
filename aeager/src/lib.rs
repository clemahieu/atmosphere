// SPDX-License-Identifier: MIT

//! The eager span source: aheap's span source contract over an untyped and a window of virtual
//! addresses it is given, verified with Verus.
//!
//! `Eager` hands out spans of its window and backs page runs in them at once, with no fault: it
//! retypes frames from its untyped, retypes and links the table pages the run needs, and maps each
//! page through acall. It keeps its own record of the untyped's pages, since a retype names a physical
//! base: which are free, which are frames held for reuse or mapped, and which went to tables. A
//! released run's frames go back to that record unmapped, since the kernel takes no frame back for a
//! later retype. `glue` is the system calls, verified over acall's kernel step but for the one item
//! that turns an accepted map into the permission to the page's bytes; `exercise` is a verified use of
//! the contract that dom0 runs at boot.
#![no_std]
// A cargo build erases specifications and proofs, so there a variable only they read looks unused.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables))]

mod eager;
mod exercise;
mod glue;

pub use eager::{Eager, MAX_PAGES, REGION_BYTES, TABLE_PAGES, WINDOW_BLOCKS};
pub use exercise::{exercise, Exercised};
