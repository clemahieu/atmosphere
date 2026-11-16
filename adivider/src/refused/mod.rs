// SPDX-License-Identifier: MIT

//! False claims for the divider. `check` returns exactly `layout_ok`, so a bool that is not that
//! value fails its ensures. The specification is the trait and the body is the module, so the
//! refusal's body span is the module's, which is the span the check joins to the clause.
//! tools/check-refused.py runs each module under cfg(refused), which nothing else sets, so the
//! claims are in no image and no verify count. design/refused-claim-per-way/.

pub mod check_true;

use vstd::prelude::*;

use crate::{Block, Join, Row, layout_ok};

verus! {

/// `check` at a bool that is not `layout_ok`.
pub trait CheckTrue {
    proof fn wrong(held: &[Block], rows: &[Row], joins: &[Join], ok: bool)
        ensures
            ok != layout_ok(held@, rows@, joins@),
    ;
}

} // verus!
