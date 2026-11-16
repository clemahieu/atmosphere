// SPDX-License-Identifier: MIT

//! False claims for `aeager`. An unchanged allocator cannot meet `invoke`'s `STATUS_OK` or
//! `STATUS_AGAIN` guarantees because `invoke` extends the held caller token's history and fulfills
//! the operation's `acall` contract. tools/check-refused.py runs each module under cfg(refused),
//! which nothing else sets, so the claims are in no image and no verify count.
//! design/refused-claim-per-way/.

pub mod invoke_again;
pub mod invoke_ok;

use vstd::prelude::*;

use aheap::allocator::Allocator;
use verified::capability::operation::{status_only, Outcome, RETYPE_FRAME, RETYPE_LARGE_FRAME, STATUS_AGAIN, STATUS_OK};

use crate::eager::Eager;
use crate::invoke::{call_contract, call_keeps_source, GuardedCall};

verus! {

/// `invoke` returning `STATUS_OK` on an allowed `Retype` with an unchanged allocator.
pub trait InvokeOk {
    proof fn unchanged(old_alloc: Allocator<Eager>, final_alloc: Allocator<Eager>, untyped: u64, base: u64, word: u64, out: Outcome)
        requires
            old_alloc.held(),
            old_alloc.token() is Some,
            old_alloc.token()->0.wf(),
            old_alloc.token()->0.entry() == old_alloc.token()->0.kernel(),
            ({
                let call = GuardedCall::Retype { untyped, kind: RETYPE_FRAME, base, word, level: 0 };
                let pre = old_alloc.token()->0;
                &&& call_keeps_source(&old_alloc.src(), call)
                &&& pre.kernel().retype_allowed(pre.root(), RETYPE_FRAME, untyped as usize, base as usize, word, 0)
            }),
            final_alloc == old_alloc,
            out == status_only(STATUS_OK),
        ensures
            final_alloc.token()->0.history() == old_alloc.token()->0.history().push((final_alloc.token()->0.entry(), final_alloc.token()->0.kernel())),
            call_contract(final_alloc.token()->0.entry(), final_alloc.token()->0.kernel(), final_alloc.token()->0.root(), GuardedCall::Retype { untyped, kind: RETYPE_FRAME, base, word, level: 0 }, out),
    ;
}

/// `invoke` returning `STATUS_AGAIN` on an allowed `Retype` (`RETYPE_LARGE_FRAME`) with an unchanged allocator.
pub trait InvokeAgain {
    proof fn unchanged(old_alloc: Allocator<Eager>, final_alloc: Allocator<Eager>, untyped: u64, base: u64, word: u64, out: Outcome)
        requires
            old_alloc.held(),
            old_alloc.token() is Some,
            old_alloc.token()->0.wf(),
            old_alloc.token()->0.entry() == old_alloc.token()->0.kernel(),
            ({
                let call = GuardedCall::Retype { untyped, kind: RETYPE_LARGE_FRAME, base, word, level: 0 };
                let pre = old_alloc.token()->0;
                &&& call_keeps_source(&old_alloc.src(), call)
                &&& pre.kernel().retype_allowed(pre.root(), RETYPE_LARGE_FRAME, untyped as usize, base as usize, word, 0)
            }),
            final_alloc == old_alloc,
            out == status_only(STATUS_AGAIN),
        ensures
            final_alloc.token()->0.history() == old_alloc.token()->0.history().push((final_alloc.token()->0.entry(), final_alloc.token()->0.kernel())),
            call_contract(final_alloc.token()->0.entry(), final_alloc.token()->0.kernel(), final_alloc.token()->0.root(), GuardedCall::Retype { untyped, kind: RETYPE_LARGE_FRAME, base, word, level: 0 }, out),
    ;
}

} // verus!
