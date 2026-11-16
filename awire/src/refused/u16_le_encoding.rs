// SPDX-License-Identifier: MIT

//! `U16Le`'s width, max, len_of and of_len at an output the ensures excludes. width returns
//! `spec_width`, max returns `spec_max`, len_of returns `spec_len` and of_len returns
//! `spec_of_len`; each claim is that ensures at the other output. The requires are the
//! operation's. design/refused-claim-per-way/.
//!
//! covers: awire/src/length.rs	U16Le::width	returns
//! covers: awire/src/length.rs	U16Le::max	returns
//! covers: awire/src/length.rs	U16Le::len_of	returns
//! covers: awire/src/length.rs	U16Le::of_len	returns
//! refused: width: w != c.spec_width()
//! refused: max: m != c.spec_max()
//! refused: len_of: n != c.spec_len(t@)
//! refused: of_len: t@ != c.spec_of_len(n as nat)

use crate::*;

verus! {

impl<'a> super::LengthEncodingReturns<'a, U16Le> for () {
    proof fn width(c: &U16Le, w: usize) {}

    proof fn max(c: &U16Le, m: usize) {}

    proof fn len_of(c: &U16Le, t: &u16, n: usize) {}

    proof fn of_len(c: &U16Le, n: usize, t: u16) {}
}

} // verus!
