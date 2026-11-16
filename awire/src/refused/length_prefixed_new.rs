// SPDX-License-Identifier: MIT

//! `LengthPrefixed::new` at fields that are not the arguments. The ensures is
//! `r.length == length` and `r.inner == inner`; this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/length.rs	LengthPrefixed::new	returns
//! refused: wrong: !(r.length == length && r.inner == inner)

use crate::*;

verus! {

impl<L, I> super::LengthPrefixedNew<L, I> for () {
    proof fn wrong(r: LengthPrefixed<L, I>, length: L, inner: I) {}
}

} // verus!
