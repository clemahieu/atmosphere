// SPDX-License-Identifier: MIT

//! Synchronization.
//!
//! We re-export the `spin` types the loader, the kernel and the machine crates take.

pub use spin::{Mutex, MutexGuard, RwLock};
