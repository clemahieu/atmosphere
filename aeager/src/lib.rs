// SPDX-License-Identifier: MIT

//! The eager span source: aheap's span source contract over an untyped and a window of virtual
//! addresses it is given, verified with Verus.
//!
//! `Eager` hands out spans of its window and backs page runs in them at once, with no fault: it
//! retypes frames from its untyped, retypes and links the table pages the run needs, and maps each
//! page through acall. It keeps its own record of the untyped's pages, since a retype names a physical
//! base: which are free, which are frames mapped or parked, and which went to tables. A released run's
//! pages stay mapped, parked at their addresses, and back those addresses again; a back elsewhere with
//! no frame held or page free unmaps a parked page and maps its frame there. `glue` is the system calls, verified over acall's kernel step but for the one item
//! that turns an accepted map into the permission to the page's bytes; `exercise` is a verified use of
//! the contract, which dom0 runs at boot over a source `exercise_eager` builds in the same call; `apart` is what one source's steps leave of another's over
//! disjoint ranges; `witness` holds verified uses of the operations, built into no image.
#![no_std]
// A cargo build erases specifications and proofs, so there a variable only they read looks unused.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables))]

mod allocator;
#[cfg(verus_keep_ghost)]
mod apart;
mod eager;
mod bootcheck;
mod glue;
mod invoke;
#[cfg(throwaway)]
mod throwaway;
#[cfg(refused)]
mod refused;
#[cfg(verus_keep_ghost)]
mod witness;

#[cfg(verus_keep_ghost)]
pub use acall::step::caller_alone;
pub use allocator::{AllocatorInit, new_allocator};
pub use eager::{Eager, MAX_PAGES, REGION_BYTES, TABLE_PAGES, WINDOW_BLOCKS};
#[cfg(verus_keep_ghost)]
pub use eager::{acall_call_in_window, acall_setup_call, run_touches_block, untyped_page, window_block};
pub use bootcheck::{exercise, exercise_eager, Exercised, PairedEager};
pub use glue::{AcallCall, AcallStep};
#[cfg(verus_keep_ghost)]
pub use glue::{acall_ok, acall_steps, flush_room, kernel_source_ready, source_ready};
pub use invoke::{GuardedCall, invoke};
#[cfg(verus_keep_ghost)]
pub use invoke::{call_contract, call_keeps_count, call_keeps_slot_space, call_keeps_source, is_source_slot};
