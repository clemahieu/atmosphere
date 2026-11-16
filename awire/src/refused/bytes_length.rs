// SPDX-License-Identifier: MIT

//! `Bytes::length`'s Some at a length that is not the serialisation's. The ensures is
//! `n == spec_serialize(v).len()`; this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/bytes.rs	Bytes::length	Some
//! refused: wrong: n != c.spec_serialize(v).len()

use crate::*;

verus! {

impl super::BytesLength for () {
    proof fn wrong(c: &Bytes, v: Seq<u8>, n: nat) {}
}

} // verus!
