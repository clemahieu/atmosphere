// SPDX-License-Identifier: MIT

//! `Tag::length`'s Some at a length that is not the serialisation's. The ensures is
//! `n == spec_serialize(v).len()`; this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/tag.rs	Tag::length	Some
//! refused: wrong: n != c.spec_serialize(v).len()

use crate::*;

verus! {

impl<'t> super::TagLength<'t> for () {
    proof fn wrong(c: &Tag<'t>, v: (), n: nat) {}
}

} // verus!
