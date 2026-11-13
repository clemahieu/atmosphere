// SPDX-License-Identifier: MIT

//! The throwaway of `witness_new`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::prelude::*;
use verified::capability::table::TABLE_INDICES;
use crate::eager::*;
use crate::{Eager, MAX_PAGES, REGION_BYTES};

verus! {

use crate::witness::*;

pub fn throwaway_new(space: u64, untyped: u64, window: *mut u8)
    requires
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
    ensures
        false,
{
    witness_new(space, untyped, window);
}

} // verus!
