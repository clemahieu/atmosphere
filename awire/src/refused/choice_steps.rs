// SPDX-License-Identifier: MIT

//! A choice whose alternatives' constants are all 0 parsing a 1000-byte input in 0 steps. Its loop
//! tries a window per iteration, each a step, so its bound cannot be the alternatives' alone; were
//! the windows uncounted, `Choice::parse`'s ensures would give this claim. The choice is a
//! length-prefixed byte or a length-prefixed u16, disjoint because the first's inner byte leaves one
//! of the two bytes a length of 2 counts. design/wire-combinators-written-here/.
//!
//! refused: zero: final(steps).count == 0

use crate::*;

verus! {

impl super::ChoiceSteps for () {
    fn zero(input: &[u8], Tracked(steps): Tracked<&mut Steps>) {
        let c = Choice {
            first: LengthPrefixed { length: U8, inner: U8 },
            second: LengthPrefixed { length: U8, inner: U16Be },
        };
        proof {
            assert forall|v: u16, rest: Seq<u8>| c.second.valid(v) implies (#[trigger] c.first.spec_parse(c.second.spec_serialize(v) + rest)) is None by {
                let b = U16Be.spec_serialize(v);
                let p = U8.spec_serialize(U8.spec_of_len(b.len()));
                let s = c.second.spec_serialize(v) + rest;
                assert(s == p + b + rest);
                assert(s.len() >= 3);
                assert(s[0] == 2u8);
                assert(s.subrange(1, 3).len() == 2);
            };
        }
        assert(c.first.k() + c.second.k() + c.first.c() + c.second.c() == 0);
        c.parse(input, Tracked(steps));
    }
}

} // verus!
