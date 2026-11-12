// SPDX-License-Identifier: MIT

//! The throwaway of `witness_free_partial`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::layout::*;
use vstd::raw_ptr::*;
use crate::arch::*;
use crate::buddy::*;
use crate::class::*;
use crate::large::*;
use crate::heap::{Heap, class_for, part_refused, run_order};
use crate::page::*;
use crate::record::{RecordStore, back_refused, gave_back, page_refused, record_page, took_page};
use crate::slab::*;
use crate::small::*;
use crate::source::*;

verus! {

use crate::witness::*;

pub fn throwaway_free_partial<S: SpanSource>(src: &mut S, token: &mut Tracked<S::Token>)
    requires
        old(src).serves(old(token)@),
        old(src)@.wf(),
    ensures
        false,
{
    witness_free_partial(src, token);
}

} // verus!
