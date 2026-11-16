// SPDX-License-Identifier: MIT

//! `Elements::new` at a value that is not the empty sequence. The ensures is
//! `r@ == Seq::<T::V>::empty()`; this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/repeat.rs	Elements::new	returns
//! refused: wrong: r@ != Seq::<T::V>::empty()

use crate::*;

verus! {

impl<T: Copy + View, const N: usize> super::ElementsNew<T, N> for () {
    proof fn wrong(r: Elements<T, N>) {}
}

} // verus!
