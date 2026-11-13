// SPDX-License-Identifier: MIT

//! The throwaway of `witness_layout`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;
use crate::*;

verus! {

use crate::witness::*;

pub fn throwaway_layout()
    ensures
        false,
{
    witness_layout();
}

} // verus!
