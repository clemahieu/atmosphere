// SPDX-License-Identifier: MIT

//! `scan`'s Ready where the ring at `start` already has a slot, claimed as Idle. The requires add
//! that state, the rings are unchanged, and the ensures is Idle. design/refused-claim-per-way/.
//!
//! covers: afanin/src/lib.rs	scan	Ready
//! refused: wrong: idle(pre, post, (r->Idle_0)@)

use vstd::prelude::*;

use aring::Consumer;

use crate::{Heads, Scan};

verus! {

impl super::ScanReady for () {
    proof fn wrong<H: Heads>(pre: Seq<Consumer>, post: Seq<Consumer>, heads: &H, start: usize, r: Scan) {
    }
}

} // verus!
