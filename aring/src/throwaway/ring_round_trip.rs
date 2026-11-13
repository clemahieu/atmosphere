// SPDX-License-Identifier: MIT

//! The throwaway of `witness_ring_round_trip`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::prelude::*;
use crate::{Consumer, Producer};

verus! {

use crate::witness::*;

pub fn throwaway_ring_round_trip(slots: &mut [u64])
    requires
        old(slots)@.len() == 4,
    ensures
        false,
{
    witness_ring_round_trip(slots);
}

} // verus!
