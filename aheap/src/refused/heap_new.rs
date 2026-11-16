// SPDX-License-Identifier: MIT

//! `Heap::new` at a heap whose spare count is not the argument, or whose live set is not empty.
//! Each is an ensures of the operation at the output it excludes. design/refused-claim-per-way/.
//!
//! covers: aheap/src/heap.rs	Heap::new	returns
//! refused: wrong: r.spares() != spares
//! refused: wrong: r.live() != ISet::<int>::empty()

use vstd::prelude::*;

use crate::heap::Heap;

verus! {

impl super::HeapNewReturns for () {
    proof fn wrong(spares: usize, r: Heap) {}
}

} // verus!
