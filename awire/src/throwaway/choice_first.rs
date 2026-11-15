// SPDX-License-Identifier: MIT

//! The throwaway of `witness_choice_first`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::prelude::*;
use crate::*;

verus! {

use crate::witness::*;

pub fn throwaway_choice_first(input: &[u8], out: &mut [u8])
    requires
        input.len() >= 2,
        input@[0] == 0x08,
        input@[1] == 0x00,
        old(out).len() >= 2,
    ensures
        false,
{
    witness_choice_first(input, out);
}

} // verus!
