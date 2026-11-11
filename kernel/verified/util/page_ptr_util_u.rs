// SPDX-License-Identifier: MIT

use vstd::prelude::*;
verus! {

#[cfg(verus_keep_ghost)]
use crate::arch::MEM_MASK;
#[cfg(verus_keep_ghost)]
use crate::define::PAddr;

pub open spec fn mem_valid(v: PAddr) -> bool {
    v & (!MEM_MASK) as usize == 0
}

} // verus!
