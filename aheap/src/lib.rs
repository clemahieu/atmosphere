//! The default heap allocator for user space, verified with Verus.
//!
//! The heap sits over a span source and holds no capability. `source` states the source's contract;
//! `arch` names the page and block sizes the target's translation fixes, which the rest of the crate
//! counts in. `buddy` cuts page runs out of one block. `witness` holds verified uses of the contract
//! and of the buddy, built into no image.
#![no_std]
#![allow(unused)]

pub mod arch;
pub mod buddy;
pub mod source;
mod witness;
