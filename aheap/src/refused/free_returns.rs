// SPDX-License-Identifier: MIT

//! `Allocator::free` at an unchanged allocator. The ensures removes the address from the live set.
//! design/refused-claim-per-way/.
//!
//! covers: aheap/src/allocator.rs	Allocator::free	returns
//! refused: unchanged: final_self.live() == old_self.live().remove(p@.addr as int)

use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;

use crate::allocator::Allocator;
use crate::source::SpanSource;

verus! {

impl super::FreeReturns for () {
    proof fn unchanged<S: SpanSource>(
        old_self: Allocator<S>,
        final_self: Allocator<S>,
        p: *mut u8,
        size: usize,
        align: usize,
        perm: Tracked<PointsToRaw>,
    ) {
    }
}

} // verus!
