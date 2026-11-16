// SPDX-License-Identifier: MIT

//! `scan`'s Idle where every ring has nothing available and a loadable head leaves the ring as it
//! was, claimed as Ready. The requires add that state, the rings are unchanged, and the ensures is
//! Ready. design/refused-claim-per-way/.
//!
//! covers: afanin/src/lib.rs	scan	Idle
//! refused: wrong: ready(pre, post, (r->Ready_1)@, start as int, (r->Ready_0) as int)

use vstd::prelude::*;

use aring::Consumer;

use crate::{Heads, Scan};

verus! {

impl super::ScanIdle for () {
    proof fn wrong<H: Heads>(pre: Seq<Consumer>, post: Seq<Consumer>, heads: &H, start: usize, r: Scan) {
    }
}

} // verus!
