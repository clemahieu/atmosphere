// SPDX-License-Identifier: MIT

//! False claims for the heap allocator. `Allocator::source` returns the source it holds, so a
//! reference that is not that source fails its ensures. The specification is the trait and the
//! body is the module, so the refusal's body span is the module's, which is the span the check
//! joins to the clause. tools/check-refused.py runs each module under cfg(refused), which nothing
//! else sets, so the claims are in no image and no verify count. design/refused-claim-per-way/.

pub mod source_returns;

use vstd::prelude::*;

use crate::allocator::Allocator;
use crate::source::SpanSource;

verus! {

/// `Allocator::source` at a reference that is not the source it holds.
pub trait SourceReturns {
    proof fn wrong<S: SpanSource>(alloc: &Allocator<S>, r: &S)
        ensures
            *r != alloc.src(),
    ;
}

} // verus!
