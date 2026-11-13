// SPDX-License-Identifier: MIT

//! The witnesses: verified sequences of operations, built into no image, that reach the uses the
//! eager span source exists for.
use vstd::prelude::*;
use acall::step::Caller;
use aheap::source::*;
use verified::capability::table::TABLE_INDICES;

use crate::eager::*;
use crate::exercise::*;
use crate::glue::names_own_space;
use crate::{Eager, MAX_PAGES, REGION_BYTES};

verus! {

/// Constructs an eager source of `MAX_PAGES` pages over a region-aligned window.
pub fn witness_new(space: u64, untyped: u64, window: *mut u8) -> (r: Option<Eager>)
    requires
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
    ensures
        r is Some,
{
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
    }
    Eager::new(space, untyped, 0, MAX_PAGES, 1, window)
}

/// Constructs an eager source of `MAX_PAGES` pages over a region-aligned window in the caller's own
/// space and exercises it, as dom0 does at boot.
pub fn witness_exercise(space: u64, untyped: u64, window: *mut u8, token: &mut Tracked<Caller>) -> (seen: Exercised)
    requires
        old(token)@.wf(),
        names_own_space(old(token)@, space),
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
    ensures
        final(token)@.wf(),
{
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
    }
    let mut source = Eager::new(space, untyped, 0, MAX_PAGES, 1, window).unwrap();
    let seen = exercise(&mut source, token);
    seen
}

/// Reserves a one-block span from a fresh eager source over a region-aligned window.
pub fn witness_reserve(space: u64, untyped: u64, window: *mut u8, token: &mut Tracked<Caller>) -> (r: Option<*mut u8>)
    requires
        window@.addr != 0,
        window@.addr as int % REGION_BYTES as int == 0,
        window@.addr + WINDOW_BYTES <= usize::MAX,
        old(token)@.wf(),
        names_own_space(old(token)@, space),
    ensures
        r is Some,
{
    proof {
        assert(1int % LEAF_INDICES as int != 0) by (compute);
        assert(frame_slot(1, (MAX_PAGES - 1) as int) < TABLE_INDICES) by (compute);
    }
    let mut src: Eager = Eager::new(space, untyped, 0, MAX_PAGES, 1, window).unwrap();
    src.reserve(token, 1)
}

} // verus!
