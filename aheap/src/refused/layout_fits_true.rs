// SPDX-License-Identifier: MIT

//! `layout_fits` at a bool that is not the layout disjunction. The ensures is the operation's at
//! the output that ensures excludes. design/refused-claim-per-way/.
//!
//! covers: aheap/src/heap.rs	layout_fits	true
//! refused: wrong: r != (small_layout(size as nat, align as nat) || run_layout(size as nat, align as nat) || large_layout(size as nat, align as nat))

use vstd::prelude::*;

verus! {

impl super::LayoutFitsTrue for () {
    proof fn wrong(size: usize, align: usize, r: bool) {}
}

} // verus!
