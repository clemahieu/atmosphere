// SPDX-License-Identifier: MIT

//! `checksum` at a sum that is not `spec_checksum`. The ensures is `r == spec_checksum(data@)`;
//! this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/checksum.rs	checksum	returns
//! refused: wrong: r != spec_checksum(s)

use crate::*;

verus! {

impl super::ChecksumReturns for () {
    proof fn wrong(s: Seq<u8>, r: u16) {}
}

} // verus!
