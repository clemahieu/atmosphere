#![no_std]
// A cargo build erases specifications and proofs, so there a variable or an assignment that only
// they read looks unused.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_assignments))]

use vstd::prelude::verus;

pub mod arch;
pub mod bridge;
pub mod capability;
pub mod define;
pub mod device;
pub mod pptr;
pub mod queue_lock;
pub mod layouts;
pub mod array;
pub mod pagetable;

pub mod lemma;
pub mod util;

verus! {

// A cargo build checks the size with a block the lint calls unnecessary braces.
#[allow(unused_braces)]
global size_of usize == 8;

}
