// SPDX-License-Identifier: MIT

//! The throwaway of `witness_length_u32_be`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::prelude::*;
use crate::*;

verus! {

use crate::witness::*;

pub fn throwaway_length_u32_be()
    ensures
        false,
{
    witness_length_u32_be();
}

} // verus!
