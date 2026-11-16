// SPDX-License-Identifier: MIT

//! `Heap::free` at an unchanged heap and source. The ensures removes the address from the live
//! set. The requires are the operation's. design/refused-claim-per-way/.
//!
//! covers: aheap/src/heap.rs	Heap::free	returns
//! refused: unchanged: final_self.live() == old_self.live().remove(p@.addr as int)

use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;

use crate::heap::Heap;
use crate::source::SpanSource;

verus! {

impl super::HeapFreeReturns for () {
    proof fn unchanged<S: SpanSource>(
        old_self: Heap,
        final_self: Heap,
        old_src: S,
        final_src: S,
        old_token: Tracked<S::Token>,
        final_token: Tracked<S::Token>,
        p: *mut u8,
        size: usize,
        align: usize,
        perm: Tracked<PointsToRaw>,
    ) {
    }
}

} // verus!
