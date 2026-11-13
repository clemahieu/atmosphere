// SPDX-License-Identifier: MIT

//! The kernel's operations as a verified user crate calls them: each wrapper's ensures is the
//! operation's contract over the caller's view, proven in kernel/verified, which this crate imports.
//!
//! `step` is the system call, the one trusted item: its ensures is what the kernel proves of its own
//! step, from an entry state the kernel's rely relates to the caller token's last state, on the premise
//! `step` states that the token was the kernel's state when the process was handed it. Every wrapper in
//! `capability` and `memory` is verified over it by the operation's kernel-side lemma and states the
//! operation's contract from that entry state, so a contract here is a proven one, not an assumed one. `example` is a verified use of the
//! wrappers.
//! See design/divider-proven-by-invariant/.
#![no_std]
// A cargo build erases specifications and proofs, so there a variable only they read looks unused.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables))]

pub mod arch;
pub mod capability;
pub mod example;
pub mod memory;
pub mod step;
