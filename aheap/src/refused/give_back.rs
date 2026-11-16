// SPDX-License-Identifier: MIT

//! `Allocator::give_back` at an unchanged allocator. The requires are the operation's, that the
//! source serves the token, and the ensures holds that token. design/refused-claim-per-way/.
//!
//! covers: aheap/src/allocator.rs	Allocator::give_back	returns
//! refused: unchanged: final_self.held()
//! refused: unchanged: final_self.token() == Some(token@)

use vstd::prelude::*;

use crate::allocator::Allocator;
use crate::source::SpanSource;

verus! {

impl super::GiveBackReturns for () {
    proof fn unchanged<S: SpanSource>(old_self: Allocator<S>, final_self: Allocator<S>, token: Tracked<S::Token>) {}
}

} // verus!
