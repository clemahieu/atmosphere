#![no_std]
#![allow(warnings)]

use vstd::prelude::verus;

pub mod bridge;
pub mod capability;
pub mod define;
pub mod device;
pub mod pptr;
pub mod queue_lock;
pub mod layouts;
pub mod trap;
pub mod array;
pub mod array_set;
pub mod array_vec;
pub mod slinkedlist;
pub mod pagetable;
pub mod allocator;
pub mod process_manager;
pub mod memory_manager;
pub mod va_range;
pub mod quota;

pub mod kernel;

pub mod lemma;
pub mod util;

verus! {

global size_of usize == 8;

}

fn main(){

}
