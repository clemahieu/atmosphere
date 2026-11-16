// SPDX-License-Identifier: MIT

//! `Allocator::new` at an allocator that does not hold the token it was given. The requires are the
//! operation's: the source is well formed and serves the token. design/refused-claim-per-way/.
//!
//! covers: aheap/src/allocator.rs	Allocator::new	returns
//! refused: wrong: !r.held()
//! refused: wrong: r.token() != Some(token@)

use vstd::prelude::*;

use crate::allocator::Allocator;
use crate::source::SpanSource;

verus! {

impl super::AllocatorNewReturns for () {
    proof fn wrong<S: SpanSource>(spares: usize, src: S, token: Tracked<S::Token>, r: Allocator<S>) {}
}

} // verus!
