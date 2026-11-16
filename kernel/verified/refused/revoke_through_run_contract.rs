// SPDX-License-Identifier: MIT

//! revoke_contract under R3 (position through pc deeper than c, with c's block holding pc's) does not
//! return a non-refused outcome.
//! design/refused-claim-per-way/.
//!
//! refused: wrong: CapKernel::revoke_contract(pre, post, root, Some(at), out)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::operation::Outcome;
use crate::capability::position::Position;

impl super::RevokeThroughRunContract for () {
    proof fn wrong(pre: CapKernel, post: CapKernel, root: usize, at: Position, out: Outcome) {}
}

} // verus!
