#![no_std]
// SPDX-License-Identifier: MIT

// A cargo build erases specifications and proofs, so there a variable or an assignment that only
// they read looks unused.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_assignments))]

use vstd::prelude::verus;

pub mod arch;
pub mod capability;
pub mod define;
pub mod pptr;
pub mod queue_lock;
pub mod layouts;
pub mod array;
pub mod pagetable;

pub mod util;

verus! {

// A cargo build checks the size with a block the lint calls unnecessary braces. Verus expands the
// global to a macro invocation, where the attribute would be unused.
#[cfg_attr(not(verus_keep_ghost), allow(unused_braces))]
global size_of usize == 8;

}
