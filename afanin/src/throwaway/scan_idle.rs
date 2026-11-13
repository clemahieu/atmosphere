// SPDX-License-Identifier: MIT

//! The throwaway of `witness_scan_idle`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use aring::{Consumer, Producer};
use vstd::prelude::*;
use crate::{examined, order, scan, Heads, Scan};

verus! {

use crate::witness::*;

pub fn throwaway_scan_idle()
    ensures
        false,
{
    witness_scan_idle();
}

} // verus!
