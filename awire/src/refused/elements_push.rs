// SPDX-License-Identifier: MIT

//! `Elements::push` at an unchanged buffer. The operation ensures
//! `final(self)@ == old(self)@.push(t@)`; an unchanged buffer (`post == pre`) meets that ensures
//! as `post@ == pre@.push(t@)`.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/repeat.rs	Elements::push	returns
//! refused: unchanged: post@ == pre@.push(t@)

use crate::*;

verus! {

impl<T: Copy + View, const N: usize> super::ElementsPush<T, N> for () {
    proof fn unchanged(pre: Elements<T, N>, post: Elements<T, N>, t: T) {}
}

} // verus!
