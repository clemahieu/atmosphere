// SPDX-License-Identifier: MIT

//! `Allocator::alloc`'s Some at an unchanged allocator that holds its token, for a small layout.
//! The ensures is the operation's small-layout arm. design/refused-claim-per-way/.
//!
//! covers: aheap/src/allocator.rs	Allocator::alloc	Some
//! refused: unchanged: old_self.held() && small_layout(size as nat, align as nat) ==> slot_alloc(old_self.heap(), final_self.heap(), old_self.src_view(), final_self.src_view(), size as nat, align as nat, r)

use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;

use crate::allocator::Allocator;
use crate::source::SpanSource;

verus! {

impl super::AllocSome for () {
    proof fn unchanged<S: SpanSource>(
        old_self: Allocator<S>,
        final_self: Allocator<S>,
        size: usize,
        align: usize,
        r: Option<(*mut u8, Tracked<PointsToRaw>)>,
    ) {
    }
}

} // verus!
