// SPDX-License-Identifier: MIT

//! `Allocator::source` at a reference that is not the source it holds. The ensures is the
//! operation's at the output that ensures excludes. design/refused-claim-per-way/.
//!
//! covers: aheap/src/allocator.rs	Allocator::source	returns
//! refused: wrong: *r != alloc.src()

use vstd::prelude::*;

use crate::allocator::Allocator;
use crate::source::SpanSource;

verus! {

impl super::SourceReturns for () {
    proof fn wrong<S: SpanSource>(alloc: &Allocator<S>, r: &S) {}
}

} // verus!
