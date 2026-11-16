// SPDX-License-Identifier: MIT

//! `invoke`'s `STATUS_AGAIN` outcome on an allowed `RETYPE_LARGE_FRAME` meets no unchanged
//! allocator: the token history grows and the region zeroing state advances.
//! design/refused-claim-per-way/.
//!
//! covers: aeager/src/invoke.rs	invoke	STATUS_AGAIN
//! refused: unchanged: final_alloc.token()->0.history() == old_alloc.token()->0.history().push((final_alloc.token()->0.entry(), final_alloc.token()->0.kernel()))
//! refused: unchanged: call_contract(final_alloc.token()->0.entry(), final_alloc.token()->0.kernel(), final_alloc.token()->0.root(), GuardedCall::Retype { untyped, kind: RETYPE_LARGE_FRAME, base, word, level: 0 }, out)

use vstd::prelude::*;

use aheap::allocator::Allocator;
use verified::capability::operation::Outcome;

use crate::eager::Eager;

verus! {

impl super::InvokeAgain for () {
    proof fn unchanged(old_alloc: Allocator<Eager>, final_alloc: Allocator<Eager>, untyped: u64, base: u64, word: u64, out: Outcome) {}
}

} // verus!
