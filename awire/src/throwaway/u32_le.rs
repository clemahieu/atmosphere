// SPDX-License-Identifier: MIT

//! The throwaway of `witness_u32_le`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::prelude::*;
use crate::*;

verus! {

use crate::witness::*;

pub fn throwaway_u32_le(input: &[u8], out: &mut [u8])
    requires
        input.len() >= 4,
        old(out).len() >= 4,
    ensures
        false,
{
    witness_u32_le(input, out);
}

} // verus!
