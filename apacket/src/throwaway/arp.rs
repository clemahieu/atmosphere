// SPDX-License-Identifier: MIT

//! The throwaway of `witness_arp`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::prelude::*;
use awire::*;
use crate::*;

verus! {

use crate::witness::*;

pub fn throwaway_arp<'a>(input: &'a [u8], out: &mut [u8])
    requires
        input.len() >= 28,
        input@[0] == 0x00,
        input@[1] == 0x01,
        input@[2] == 0x08,
        input@[3] == 0x00,
        input@[4] == 6,
        input@[5] == 4,
        old(out).len() >= 28,
    ensures
        false,
{
    witness_arp(input, out);
}

} // verus!
