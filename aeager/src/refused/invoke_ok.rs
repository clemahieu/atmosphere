// SPDX-License-Identifier: MIT

//! `invoke`'s `STATUS_OK` outcome on an allowed `Retype` meets no unchanged allocator: the token
//! history grows and the destination slot gains the retyped frame. design/refused-claim-per-way/.
//!
//! covers: aeager/src/invoke.rs	invoke	STATUS_OK
//! refused: unchanged: final_alloc.token()->0.history() == old_alloc.token()->0.history().push((final_alloc.token()->0.entry(), final_alloc.token()->0.kernel()))
//! refused: unchanged: call_contract(final_alloc.token()->0.entry(), final_alloc.token()->0.kernel(), final_alloc.token()->0.root(), GuardedCall::Retype { untyped, kind: RETYPE_FRAME, base, word, level: 0 }, out)

use vstd::prelude::*;

use aheap::allocator::Allocator;
use verified::capability::operation::Outcome;

use crate::eager::Eager;

verus! {

impl super::InvokeOk for () {
    proof fn unchanged(old_alloc: Allocator<Eager>, final_alloc: Allocator<Eager>, untyped: u64, base: u64, word: u64, out: Outcome) {}
}

} // verus!
