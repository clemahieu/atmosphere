// SPDX-License-Identifier: MIT

//! The fixed-width unsigned integers: `U8`, and `U16`, `U32` and `U64` big-endian (`Be`), as the
//! Internet's headers carry them, and little-endian (`Le`), as virtio's do. A value is assembled
//! from its bytes by shifts and taken apart by shifts and truncation, each step proven by the
//! bit-vector solver, so nothing here is trusted. None loops: each adds no step.


use crate::*;

verus! {

/// One byte.
pub struct U8;

impl<'a> Combinator<'a> for U8 {
    type V = u8;

    type T = u8;

    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, u8)> {
        if 1 <= s.len() {
            Some((1, s[0]))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: u8) -> Seq<u8> {
        seq![v]
    }

    open spec fn valid(&self, v: u8) -> bool {
        true
    }

    open spec fn k(&self) -> nat {
        0
    }

    open spec fn c(&self) -> nat {
        0
    }

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        if 1 <= s.len() {
            assert(self.spec_serialize(s[0]) =~= s.take(1));
        }
    }

    proof fn lemma_serialize_parse(&self, v: u8, rest: Seq<u8>) {
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, u8)>) {
        if input.len() < 1 {
            return None;
        }
        proof {
            self.lemma_parse_serialize(input@);
        }
        Some((1, input[0]))
    }

    fn serialize(&self, v: &u8, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        if pos >= out.len() {
            return None;
        }
        let ghost before = out@;
        out[pos] = *v;
        assert(out@ =~= written(before, pos as int, self.spec_serialize(*v)));
        Some(1)
    }
}

/// The u16 whose big-endian bytes are `b0`, `b1`.
pub open spec fn be16(b0: u8, b1: u8) -> u16 {
    ((b0 as u16) << 8u16) | (b1 as u16)
}

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

/// A big-endian u16.
pub struct U16Be;

impl<'a> Combinator<'a> for U16Be {
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
        seq![(v >> 8u16) as u8, v as u8]
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

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        if 2 <= s.len() {
            lemma_be16(s[0], s[1]);
            assert(self.spec_serialize(be16(s[0], s[1])) =~= s.take(2));
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
        out[pos] = (*v >> 8u16) as u8;
        out[pos + 1] = *v as u8;
        assert(out@ =~= written(before, pos as int, self.spec_serialize(*v)));
        Some(2)
    }
}

/// A little-endian u16.
pub struct U16Le;

impl<'a> Combinator<'a> for U16Le {
    type V = u16;

    type T = u16;

    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, u16)> {
        if 2 <= s.len() {
            Some((2, be16(s[1], s[0])))
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

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        if 2 <= s.len() {
            lemma_be16(s[1], s[0]);
            assert(self.spec_serialize(be16(s[1], s[0])) =~= s.take(2));
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
        let v = ((input[1] as u16) << 8u16) | (input[0] as u16);
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

/// The u32 whose big-endian bytes are `b0`, `b1`, `b2`, `b3`.
pub open spec fn be32(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    ((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (b3 as u32)
}

proof fn lemma_be32(b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        (be32(b0, b1, b2, b3) >> 24u32) as u8 == b0,
        (be32(b0, b1, b2, b3) >> 16u32) as u8 == b1,
        (be32(b0, b1, b2, b3) >> 8u32) as u8 == b2,
        be32(b0, b1, b2, b3) as u8 == b3,
{
    assert(((((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (b3 as u32)) >> 24u32) as u8 == b0) by (bit_vector);
    assert(((((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (b3 as u32)) >> 16u32) as u8 == b1) by (bit_vector);
    assert(((((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (b3 as u32)) >> 8u32) as u8 == b2) by (bit_vector);
    assert((((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (b3 as u32)) as u8 == b3) by (bit_vector);
}

proof fn lemma_be32_of(v: u32)
    ensures
        be32((v >> 24u32) as u8, (v >> 16u32) as u8, (v >> 8u32) as u8, v as u8) == v,
{
    assert(((((v >> 24u32) as u8) as u32) << 24u32) | ((((v >> 16u32) as u8) as u32) << 16u32) | ((((v >> 8u32) as u8) as u32) << 8u32) | ((v as u8) as u32) == v) by (bit_vector);
}

/// A big-endian u32.
pub struct U32Be;

impl<'a> Combinator<'a> for U32Be {
    type V = u32;

    type T = u32;

    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, u32)> {
        if 4 <= s.len() {
            Some((4, be32(s[0], s[1], s[2], s[3])))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: u32) -> Seq<u8> {
        seq![(v >> 24u32) as u8, (v >> 16u32) as u8, (v >> 8u32) as u8, v as u8]
    }

    open spec fn valid(&self, v: u32) -> bool {
        true
    }

    open spec fn k(&self) -> nat {
        0
    }

    open spec fn c(&self) -> nat {
        0
    }

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        if 4 <= s.len() {
            lemma_be32(s[0], s[1], s[2], s[3]);
            assert(self.spec_serialize(be32(s[0], s[1], s[2], s[3])) =~= s.take(4));
        }
    }

    proof fn lemma_serialize_parse(&self, v: u32, rest: Seq<u8>) {
        lemma_be32_of(v);
        let s = self.spec_serialize(v) + rest;
        assert(s[0] == self.spec_serialize(v)[0]);
        assert(s[1] == self.spec_serialize(v)[1]);
        assert(s[2] == self.spec_serialize(v)[2]);
        assert(s[3] == self.spec_serialize(v)[3]);
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, u32)>) {
        if input.len() < 4 {
            return None;
        }
        let v = ((input[0] as u32) << 24u32) | ((input[1] as u32) << 16u32) | ((input[2] as u32) << 8u32) | (input[3] as u32);
        proof {
            self.lemma_parse_serialize(input@);
        }
        Some((4, v))
    }

    fn serialize(&self, v: &u32, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        if pos > out.len() || out.len() - pos < 4 {
            return None;
        }
        let ghost before = out@;
        out[pos] = (*v >> 24u32) as u8;
        out[pos + 1] = (*v >> 16u32) as u8;
        out[pos + 2] = (*v >> 8u32) as u8;
        out[pos + 3] = *v as u8;
        assert(out@ =~= written(before, pos as int, self.spec_serialize(*v)));
        Some(4)
    }
}

/// A little-endian u32.
pub struct U32Le;

impl<'a> Combinator<'a> for U32Le {
    type V = u32;

    type T = u32;

    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, u32)> {
        if 4 <= s.len() {
            Some((4, be32(s[3], s[2], s[1], s[0])))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: u32) -> Seq<u8> {
        seq![v as u8, (v >> 8u32) as u8, (v >> 16u32) as u8, (v >> 24u32) as u8]
    }

    open spec fn valid(&self, v: u32) -> bool {
        true
    }

    open spec fn k(&self) -> nat {
        0
    }

    open spec fn c(&self) -> nat {
        0
    }

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        if 4 <= s.len() {
            lemma_be32(s[3], s[2], s[1], s[0]);
            assert(self.spec_serialize(be32(s[3], s[2], s[1], s[0])) =~= s.take(4));
        }
    }

    proof fn lemma_serialize_parse(&self, v: u32, rest: Seq<u8>) {
        lemma_be32_of(v);
        let s = self.spec_serialize(v) + rest;
        assert(s[0] == self.spec_serialize(v)[0]);
        assert(s[1] == self.spec_serialize(v)[1]);
        assert(s[2] == self.spec_serialize(v)[2]);
        assert(s[3] == self.spec_serialize(v)[3]);
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, u32)>) {
        if input.len() < 4 {
            return None;
        }
        let v = ((input[3] as u32) << 24u32) | ((input[2] as u32) << 16u32) | ((input[1] as u32) << 8u32) | (input[0] as u32);
        proof {
            self.lemma_parse_serialize(input@);
        }
        Some((4, v))
    }

    fn serialize(&self, v: &u32, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        if pos > out.len() || out.len() - pos < 4 {
            return None;
        }
        let ghost before = out@;
        out[pos] = *v as u8;
        out[pos + 1] = (*v >> 8u32) as u8;
        out[pos + 2] = (*v >> 16u32) as u8;
        out[pos + 3] = (*v >> 24u32) as u8;
        assert(out@ =~= written(before, pos as int, self.spec_serialize(*v)));
        Some(4)
    }
}

/// The u64 whose big-endian bytes are `b0`, `b1`, `b2`, `b3`, `b4`, `b5`, `b6`, `b7`.
pub open spec fn be64(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8) -> u64 {
    ((b0 as u64) << 56u64) | ((b1 as u64) << 48u64) | ((b2 as u64) << 40u64) | ((b3 as u64) << 32u64) | ((b4 as u64) << 24u64) | ((b5 as u64) << 16u64) | ((b6 as u64) << 8u64) | (b7 as u64)
}

proof fn lemma_be64(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8)
    ensures
        (be64(b0, b1, b2, b3, b4, b5, b6, b7) >> 56u64) as u8 == b0,
        (be64(b0, b1, b2, b3, b4, b5, b6, b7) >> 48u64) as u8 == b1,
        (be64(b0, b1, b2, b3, b4, b5, b6, b7) >> 40u64) as u8 == b2,
        (be64(b0, b1, b2, b3, b4, b5, b6, b7) >> 32u64) as u8 == b3,
        (be64(b0, b1, b2, b3, b4, b5, b6, b7) >> 24u64) as u8 == b4,
        (be64(b0, b1, b2, b3, b4, b5, b6, b7) >> 16u64) as u8 == b5,
        (be64(b0, b1, b2, b3, b4, b5, b6, b7) >> 8u64) as u8 == b6,
        be64(b0, b1, b2, b3, b4, b5, b6, b7) as u8 == b7,
{
    assert(((((b0 as u64) << 56u64) | ((b1 as u64) << 48u64) | ((b2 as u64) << 40u64) | ((b3 as u64) << 32u64) | ((b4 as u64) << 24u64) | ((b5 as u64) << 16u64) | ((b6 as u64) << 8u64) | (b7 as u64)) >> 56u64) as u8 == b0) by (bit_vector);
    assert(((((b0 as u64) << 56u64) | ((b1 as u64) << 48u64) | ((b2 as u64) << 40u64) | ((b3 as u64) << 32u64) | ((b4 as u64) << 24u64) | ((b5 as u64) << 16u64) | ((b6 as u64) << 8u64) | (b7 as u64)) >> 48u64) as u8 == b1) by (bit_vector);
    assert(((((b0 as u64) << 56u64) | ((b1 as u64) << 48u64) | ((b2 as u64) << 40u64) | ((b3 as u64) << 32u64) | ((b4 as u64) << 24u64) | ((b5 as u64) << 16u64) | ((b6 as u64) << 8u64) | (b7 as u64)) >> 40u64) as u8 == b2) by (bit_vector);
    assert(((((b0 as u64) << 56u64) | ((b1 as u64) << 48u64) | ((b2 as u64) << 40u64) | ((b3 as u64) << 32u64) | ((b4 as u64) << 24u64) | ((b5 as u64) << 16u64) | ((b6 as u64) << 8u64) | (b7 as u64)) >> 32u64) as u8 == b3) by (bit_vector);
    assert(((((b0 as u64) << 56u64) | ((b1 as u64) << 48u64) | ((b2 as u64) << 40u64) | ((b3 as u64) << 32u64) | ((b4 as u64) << 24u64) | ((b5 as u64) << 16u64) | ((b6 as u64) << 8u64) | (b7 as u64)) >> 24u64) as u8 == b4) by (bit_vector);
    assert(((((b0 as u64) << 56u64) | ((b1 as u64) << 48u64) | ((b2 as u64) << 40u64) | ((b3 as u64) << 32u64) | ((b4 as u64) << 24u64) | ((b5 as u64) << 16u64) | ((b6 as u64) << 8u64) | (b7 as u64)) >> 16u64) as u8 == b5) by (bit_vector);
    assert(((((b0 as u64) << 56u64) | ((b1 as u64) << 48u64) | ((b2 as u64) << 40u64) | ((b3 as u64) << 32u64) | ((b4 as u64) << 24u64) | ((b5 as u64) << 16u64) | ((b6 as u64) << 8u64) | (b7 as u64)) >> 8u64) as u8 == b6) by (bit_vector);
    assert((((b0 as u64) << 56u64) | ((b1 as u64) << 48u64) | ((b2 as u64) << 40u64) | ((b3 as u64) << 32u64) | ((b4 as u64) << 24u64) | ((b5 as u64) << 16u64) | ((b6 as u64) << 8u64) | (b7 as u64)) as u8 == b7) by (bit_vector);
}

proof fn lemma_be64_of(v: u64)
    ensures
        be64((v >> 56u64) as u8, (v >> 48u64) as u8, (v >> 40u64) as u8, (v >> 32u64) as u8, (v >> 24u64) as u8, (v >> 16u64) as u8, (v >> 8u64) as u8, v as u8) == v,
{
    assert(((((v >> 56u64) as u8) as u64) << 56u64) | ((((v >> 48u64) as u8) as u64) << 48u64) | ((((v >> 40u64) as u8) as u64) << 40u64) | ((((v >> 32u64) as u8) as u64) << 32u64) | ((((v >> 24u64) as u8) as u64) << 24u64) | ((((v >> 16u64) as u8) as u64) << 16u64) | ((((v >> 8u64) as u8) as u64) << 8u64) | ((v as u8) as u64) == v) by (bit_vector);
}

/// A big-endian u64.
pub struct U64Be;

impl<'a> Combinator<'a> for U64Be {
    type V = u64;

    type T = u64;

    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, u64)> {
        if 8 <= s.len() {
            Some((8, be64(s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7])))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: u64) -> Seq<u8> {
        seq![(v >> 56u64) as u8, (v >> 48u64) as u8, (v >> 40u64) as u8, (v >> 32u64) as u8, (v >> 24u64) as u8, (v >> 16u64) as u8, (v >> 8u64) as u8, v as u8]
    }

    open spec fn valid(&self, v: u64) -> bool {
        true
    }

    open spec fn k(&self) -> nat {
        0
    }

    open spec fn c(&self) -> nat {
        0
    }

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        if 8 <= s.len() {
            lemma_be64(s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]);
            assert(self.spec_serialize(be64(s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7])) =~= s.take(8));
        }
    }

    proof fn lemma_serialize_parse(&self, v: u64, rest: Seq<u8>) {
        lemma_be64_of(v);
        let s = self.spec_serialize(v) + rest;
        assert(s[0] == self.spec_serialize(v)[0]);
        assert(s[1] == self.spec_serialize(v)[1]);
        assert(s[2] == self.spec_serialize(v)[2]);
        assert(s[3] == self.spec_serialize(v)[3]);
        assert(s[4] == self.spec_serialize(v)[4]);
        assert(s[5] == self.spec_serialize(v)[5]);
        assert(s[6] == self.spec_serialize(v)[6]);
        assert(s[7] == self.spec_serialize(v)[7]);
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, u64)>) {
        if input.len() < 8 {
            return None;
        }
        let v = ((input[0] as u64) << 56u64) | ((input[1] as u64) << 48u64) | ((input[2] as u64) << 40u64) | ((input[3] as u64) << 32u64) | ((input[4] as u64) << 24u64) | ((input[5] as u64) << 16u64) | ((input[6] as u64) << 8u64) | (input[7] as u64);
        proof {
            self.lemma_parse_serialize(input@);
        }
        Some((8, v))
    }

    fn serialize(&self, v: &u64, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        if pos > out.len() || out.len() - pos < 8 {
            return None;
        }
        let ghost before = out@;
        out[pos] = (*v >> 56u64) as u8;
        out[pos + 1] = (*v >> 48u64) as u8;
        out[pos + 2] = (*v >> 40u64) as u8;
        out[pos + 3] = (*v >> 32u64) as u8;
        out[pos + 4] = (*v >> 24u64) as u8;
        out[pos + 5] = (*v >> 16u64) as u8;
        out[pos + 6] = (*v >> 8u64) as u8;
        out[pos + 7] = *v as u8;
        assert(out@ =~= written(before, pos as int, self.spec_serialize(*v)));
        Some(8)
    }
}

/// A little-endian u64.
pub struct U64Le;

impl<'a> Combinator<'a> for U64Le {
    type V = u64;

    type T = u64;

    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, u64)> {
        if 8 <= s.len() {
            Some((8, be64(s[7], s[6], s[5], s[4], s[3], s[2], s[1], s[0])))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: u64) -> Seq<u8> {
        seq![v as u8, (v >> 8u64) as u8, (v >> 16u64) as u8, (v >> 24u64) as u8, (v >> 32u64) as u8, (v >> 40u64) as u8, (v >> 48u64) as u8, (v >> 56u64) as u8]
    }

    open spec fn valid(&self, v: u64) -> bool {
        true
    }

    open spec fn k(&self) -> nat {
        0
    }

    open spec fn c(&self) -> nat {
        0
    }

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        if 8 <= s.len() {
            lemma_be64(s[7], s[6], s[5], s[4], s[3], s[2], s[1], s[0]);
            assert(self.spec_serialize(be64(s[7], s[6], s[5], s[4], s[3], s[2], s[1], s[0])) =~= s.take(8));
        }
    }

    proof fn lemma_serialize_parse(&self, v: u64, rest: Seq<u8>) {
        lemma_be64_of(v);
        let s = self.spec_serialize(v) + rest;
        assert(s[0] == self.spec_serialize(v)[0]);
        assert(s[1] == self.spec_serialize(v)[1]);
        assert(s[2] == self.spec_serialize(v)[2]);
        assert(s[3] == self.spec_serialize(v)[3]);
        assert(s[4] == self.spec_serialize(v)[4]);
        assert(s[5] == self.spec_serialize(v)[5]);
        assert(s[6] == self.spec_serialize(v)[6]);
        assert(s[7] == self.spec_serialize(v)[7]);
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, u64)>) {
        if input.len() < 8 {
            return None;
        }
        let v = ((input[7] as u64) << 56u64) | ((input[6] as u64) << 48u64) | ((input[5] as u64) << 40u64) | ((input[4] as u64) << 32u64) | ((input[3] as u64) << 24u64) | ((input[2] as u64) << 16u64) | ((input[1] as u64) << 8u64) | (input[0] as u64);
        proof {
            self.lemma_parse_serialize(input@);
        }
        Some((8, v))
    }

    fn serialize(&self, v: &u64, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        if pos > out.len() || out.len() - pos < 8 {
            return None;
        }
        let ghost before = out@;
        out[pos] = *v as u8;
        out[pos + 1] = (*v >> 8u64) as u8;
        out[pos + 2] = (*v >> 16u64) as u8;
        out[pos + 3] = (*v >> 24u64) as u8;
        out[pos + 4] = (*v >> 32u64) as u8;
        out[pos + 5] = (*v >> 40u64) as u8;
        out[pos + 6] = (*v >> 48u64) as u8;
        out[pos + 7] = (*v >> 56u64) as u8;
        assert(out@ =~= written(before, pos as int, self.spec_serialize(*v)));
        Some(8)
    }
}

} // verus!
