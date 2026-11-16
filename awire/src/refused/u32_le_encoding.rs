// SPDX-License-Identifier: MIT

//! `U32Le`'s width, max, len_of and of_len at an output the ensures excludes. width returns
//! `spec_width`, max returns `spec_max`, len_of returns `spec_len` and of_len returns
//! `spec_of_len`; each claim is that ensures at the other output. The requires are the
//! operation's. design/refused-claim-per-way/.
//!
//! covers: awire/src/length.rs	U32Le::width	returns
//! covers: awire/src/length.rs	U32Le::max	returns
//! covers: awire/src/length.rs	U32Le::len_of	returns
//! covers: awire/src/length.rs	U32Le::of_len	returns
//! refused: width: w != c.spec_width()
//! refused: max: m != c.spec_max()
//! refused: len_of: n != c.spec_len(t@)
//! refused: of_len: t@ != c.spec_of_len(n as nat)

use crate::*;

verus! {

impl<'a> super::LengthEncodingReturns<'a, U32Le> for () {
    proof fn width(c: &U32Le, w: usize) {}

    proof fn max(c: &U32Le, m: usize) {}

    proof fn len_of(c: &U32Le, t: &u32, n: usize) {}

    proof fn of_len(c: &U32Le, n: usize, t: u32) {}
}

} // verus!
