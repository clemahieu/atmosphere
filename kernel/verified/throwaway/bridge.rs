// SPDX-License-Identifier: MIT

//! The throwaway of `witness_bridge`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use core::marker::PhantomData;
use vstd::atomic_ghost::{AtomicInvariantPredicate, AtomicUsize};
use vstd::atomic_with_ghost;
use vstd::prelude::*;
use vstd::resource::ghost_var::{GhostVar, GhostVarAuth};
use vstd::resource::set::GhostSetAuth;
use vstd::resource::set::GhostSingleton;
use vstd::resource::Loc;
use crate::arch::spin_hint;
use crate::capability::steps::Steps;
use crate::define::NUM_CPUS;

verus! {

use crate::core_bridge::*;

pub fn throwaway_bridge(cpu: usize)
    requires
        cpu < NUM_CPUS,
    ensures
        false,
{
    witness_bridge(cpu);
}

} // verus!
