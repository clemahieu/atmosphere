// SPDX-License-Identifier: MIT

//! `check` at a bool that is not `layout_ok`. The ensures is the operation's at the output that
//! ensures excludes. design/refused-claim-per-way/.
//!
//! covers: adivider/src/lib.rs	check	true
//! refused: wrong: ok != layout_ok(held@, rows@, joins@)

use vstd::prelude::*;

use crate::{Block, Join, Row};

verus! {

impl super::CheckTrue for () {
    proof fn wrong(held: &[Block], rows: &[Row], joins: &[Join], ok: bool) {}
}

} // verus!
