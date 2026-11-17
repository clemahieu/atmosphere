// SPDX-License-Identifier: MIT

//! The kernel's operations as a verified user crate calls them: each wrapper's ensures is the
//! operation's contract over the caller's view, proven in kernel/verified, which this crate imports.
//!
//! `step` is the system call, the one trusted item: its ensures is what the kernel proves of its own
//! step, from an entry state the kernel's rely relates to the caller token's last state, on the premises
//! `step` states: the token held the process's state and root when handed it, and the process's Rust
//! memory is mapped when its first call through acall enters. Every wrapper in
//! `capability` and `memory` is verified over it by the operation's kernel-side lemma and states the
//! operation's contract from that entry state, so a contract here is a proven one, not an assumed one. `step`
//! is private to this crate, so verified code calls the kernel only through the wrappers, and changes
//! its own space only through map_own and unmap_own, against a page token
//! (design/region-map-owns-the-address-space/). `example` is a verified use of the wrappers.
//! See design/divider-proven-by-invariant/.
#![no_std]
// A cargo build erases specifications and proofs, so there a variable only they read looks unused.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables))]

pub mod arch;
pub mod capability;
pub mod example;
pub mod memory;
pub mod step;
