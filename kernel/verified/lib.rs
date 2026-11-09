#![no_std]
#![allow(warnings)]

use vstd::prelude::verus;

pub mod arch;
pub mod bridge;
pub mod capability;
pub mod define;
pub mod device;
pub mod pptr;
pub mod queue_lock;
pub mod layouts;
pub mod trap;
pub mod array;
pub mod pagetable;

pub mod lemma;
pub mod util;

verus! {

global size_of usize == 8;

}

fn main(){

}
