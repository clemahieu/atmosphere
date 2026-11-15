// SPDX-License-Identifier: MIT

//! A u16 parsed big-endian and serialised little-endian: everything the interface asks holds but
//! the round trip, so Verus must refuse it there and nowhere else: the two postconditions of
//! `Combinator` below, each in the lemma named. Were they too weak to tell a serialiser that does
//! not invert its parse, this would verify. tools/check-refused.py runs it under cfg(refused).
//!
//! refused: lemma_parse_serialize: self.spec_parse(s) matches Some((n, v)) ==> self.spec_serialize(v) == s.take(n as int)
//! refused: lemma_serialize_parse: self.spec_parse(self.spec_serialize(v) + rest) == Some((self.spec_serialize(v).len(), v))

use crate::*;

verus! {

proof fn lemma_be16(b0: u8, b1: u8)
    ensures
        (be16(b0, b1) >> 8u16) as u8 == b0,
        be16(b0, b1) as u8 == b1,
{
    assert(((((b0 as u16) << 8u16) | (b1 as u16)) >> 8u16) as u8 == b0) by (bit_vector);
    assert((((b0 as u16) << 8u16) | (b1 as u16)) as u8 == b1) by (bit_vector);
}

proof fn lemma_be16_of(v: u16)
    ensures
        be16((v >> 8u16) as u8, v as u8) == v,
{
    assert(((((v >> 8u16) as u8) as u16) << 8u16) | ((v as u8) as u16) == v) by (bit_vector);
}

/// Big-endian in, little-endian out.
pub struct U16BeLe;

impl<'a> Combinator<'a> for U16BeLe {
    type V = u16;

    type T = u16;

    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, u16)> {
        if 2 <= s.len() {
            Some((2, be16(s[0], s[1])))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: u16) -> Seq<u8> {
        seq![v as u8, (v >> 8u16) as u8]
    }

    open spec fn valid(&self, v: u16) -> bool {
        true
    }

    open spec fn k(&self) -> nat {
        0
    }

    open spec fn c(&self) -> nat {
        0
    }

    // The proofs U16Be's would be, each fact true of this format too: with a big-endian serialiser
    // they verify, so the serialiser alone is what Verus refuses.
    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        if 2 <= s.len() {
            lemma_be16(s[0], s[1]);
            assert(s.take(2) =~= seq![s[0], s[1]]);
        }
    }

    proof fn lemma_serialize_parse(&self, v: u16, rest: Seq<u8>) {
        lemma_be16_of(v);
        let s = self.spec_serialize(v) + rest;
        assert(s[0] == self.spec_serialize(v)[0]);
        assert(s[1] == self.spec_serialize(v)[1]);
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, u16)>) {
        if input.len() < 2 {
            return None;
        }
        let v = ((input[0] as u16) << 8u16) | (input[1] as u16);
        proof {
            self.lemma_parse_serialize(input@);
        }
        Some((2, v))
    }

    fn serialize(&self, v: &u16, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        if pos > out.len() || out.len() - pos < 2 {
            return None;
        }
        let ghost before = out@;
        out[pos] = *v as u8;
        out[pos + 1] = (*v >> 8u16) as u8;
        assert(out@ =~= written(before, pos as int, self.spec_serialize(*v)));
        Some(2)
    }
}

} // verus!
