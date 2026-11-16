// SPDX-License-Identifier: MIT

//! `Eager::release_span` at an unchanged source and token. The trait ensures the span leaves the
//! view, and the unchanged source still holds it. design/refused-claim-per-way/.
//!
//! covers: aeager/src/eager.rs	Eager::release_span	returns
//! refused: unchanged: final_self@ == old_self@.released_span(span as int)

use vstd::prelude::*;

use acall::step::Caller;

use crate::eager::Eager;

verus! {

impl super::ReleaseSpanReturns for () {
    proof fn unchanged(
        old_self: Eager,
        final_self: Eager,
        old_token: Tracked<Caller>,
        final_token: Tracked<Caller>,
        span: usize,
    ) {
    }
}

} // verus!
