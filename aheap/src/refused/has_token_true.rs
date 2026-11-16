// SPDX-License-Identifier: MIT

//! `Allocator::has_token` at an allocator that holds its token, claimed false. The operation
//! ensures the bool is `held`. design/refused-claim-per-way/.
//!
//! covers: aheap/src/allocator.rs	Allocator::has_token	true
//! refused: wrong: r == alloc.held()

use vstd::prelude::*;

use crate::allocator::Allocator;
use crate::source::SpanSource;

verus! {

impl super::HasTokenTrue for () {
    proof fn wrong<S: SpanSource>(alloc: &Allocator<S>, r: bool) {}
}

} // verus!
