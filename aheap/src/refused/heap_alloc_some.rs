// SPDX-License-Identifier: MIT

//! `Heap::alloc`'s Some at an unchanged heap and source, for a small layout. The ensures is the
//! operation's small-layout arm. The requires are the operation's, plus that layout and the
//! unchanged component. design/refused-claim-per-way/.
//!
//! covers: aheap/src/heap.rs	Heap::alloc	Some
//! refused: unchanged: small_layout(size as nat, align as nat) ==> slot_alloc(old_self, final_self, old_src@, final_src@, size as nat, align as nat, r)

use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;

use crate::heap::Heap;
use crate::source::SpanSource;

verus! {

impl super::HeapAllocSome for () {
    proof fn unchanged<S: SpanSource>(
        old_self: Heap,
        final_self: Heap,
        old_src: S,
        final_src: S,
        old_token: Tracked<S::Token>,
        final_token: Tracked<S::Token>,
        size: usize,
        align: usize,
        r: Option<(*mut u8, Tracked<PointsToRaw>)>,
    ) {
    }
}

} // verus!
