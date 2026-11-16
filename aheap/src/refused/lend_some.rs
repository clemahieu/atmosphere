// SPDX-License-Identifier: MIT

//! `Allocator::lend`'s Some at an unchanged allocator. The ensures gives the token up, so the
//! allocator no longer holds it. design/refused-claim-per-way/.
//!
//! covers: aheap/src/allocator.rs	Allocator::lend	Some
//! refused: unchanged: !final_self.held()
//! refused: unchanged: final_self.token() is None

use vstd::prelude::*;

use crate::allocator::Allocator;
use crate::source::SpanSource;

verus! {

impl super::LendSome for () {
    proof fn unchanged<S: SpanSource>(old_self: Allocator<S>, final_self: Allocator<S>, r: Option<Tracked<S::Token>>) {}
}

} // verus!
