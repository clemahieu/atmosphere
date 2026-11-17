// SPDX-License-Identifier: MIT

//! The witnesses, built into no image: for each combinator, a caller holding an input and an
//! output buffer, as a format's parser and serialiser do, parses a value from the input and writes
//! it back, having first asked the value's serialised length within the buffer's room, as a composite
//! does before it writes; the buffer then starts with exactly the bytes the parse consumed. Each
//! reaches the accepting way of the combinator's `parse`, `length` and `serialize`; a choice's,
//! through each alternative. Each `Length` integer's witness reaches its conversions. A repetition's
//! witness asks the length of, and writes, the value its parse gave, which it holds in place; the
//! witness of `Elements` builds a value in place and reads it back.
//! design/witness-per-way-an-operation-succeeds/.

use vstd::prelude::*;

use crate::*;

verus! {

/// Reads one byte as a `u8` and writes it back.
pub fn witness_u8(input: &[u8], out: &mut [u8]) -> (r: (Option<(usize, u8)>, Option<usize>, Option<usize>))
    requires
        input.len() >= 1,
        old(out).len() >= 1,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(1) == input@.take(1),
{
    let c: U8 = U8;
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.unwrap();
    let room = c.length(&v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(&v, out, 0, Tracked(&mut steps));
    assert(out@.take(1) =~= input@.take(1));
    (parsed, wrote, room)
}

/// Reads two bytes as a big-endian `u16` and writes it back.
pub fn witness_u16_be(input: &[u8], out: &mut [u8]) -> (r: (Option<(usize, u16)>, Option<usize>, Option<usize>))
    requires
        input.len() >= 2,
        old(out).len() >= 2,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(2) == input@.take(2),
{
    let c: U16Be = U16Be;
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.unwrap();
    let room = c.length(&v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(&v, out, 0, Tracked(&mut steps));
    assert(out@.take(2) =~= input@.take(2));
    (parsed, wrote, room)
}

/// Reads two bytes as a little-endian `u16` and writes it back.
pub fn witness_u16_le(input: &[u8], out: &mut [u8]) -> (r: (Option<(usize, u16)>, Option<usize>, Option<usize>))
    requires
        input.len() >= 2,
        old(out).len() >= 2,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(2) == input@.take(2),
{
    let c: U16Le = U16Le;
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.unwrap();
    let room = c.length(&v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(&v, out, 0, Tracked(&mut steps));
    assert(out@.take(2) =~= input@.take(2));
    (parsed, wrote, room)
}

/// Reads four bytes as a big-endian `u32` and writes it back.
pub fn witness_u32_be(input: &[u8], out: &mut [u8]) -> (r: (Option<(usize, u32)>, Option<usize>, Option<usize>))
    requires
        input.len() >= 4,
        old(out).len() >= 4,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(4) == input@.take(4),
{
    let c: U32Be = U32Be;
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.unwrap();
    let room = c.length(&v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(&v, out, 0, Tracked(&mut steps));
    assert(out@.take(4) =~= input@.take(4));
    (parsed, wrote, room)
}

/// Reads four bytes as a little-endian `u32` and writes it back.
pub fn witness_u32_le(input: &[u8], out: &mut [u8]) -> (r: (Option<(usize, u32)>, Option<usize>, Option<usize>))
    requires
        input.len() >= 4,
        old(out).len() >= 4,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(4) == input@.take(4),
{
    let c: U32Le = U32Le;
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.unwrap();
    let room = c.length(&v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(&v, out, 0, Tracked(&mut steps));
    assert(out@.take(4) =~= input@.take(4));
    (parsed, wrote, room)
}

/// Reads eight bytes as a big-endian `u64` and writes it back.
pub fn witness_u64_be(input: &[u8], out: &mut [u8]) -> (r: (Option<(usize, u64)>, Option<usize>, Option<usize>))
    requires
        input.len() >= 8,
        old(out).len() >= 8,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(8) == input@.take(8),
{
    let c: U64Be = U64Be;
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.unwrap();
    let room = c.length(&v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(&v, out, 0, Tracked(&mut steps));
    assert(out@.take(8) =~= input@.take(8));
    (parsed, wrote, room)
}

/// Reads eight bytes as a little-endian `u64` and writes it back.
pub fn witness_u64_le(input: &[u8], out: &mut [u8]) -> (r: (Option<(usize, u64)>, Option<usize>, Option<usize>))
    requires
        input.len() >= 8,
        old(out).len() >= 8,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(8) == input@.take(8),
{
    let c: U64Le = U64Le;
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.unwrap();
    let room = c.length(&v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(&v, out, 0, Tracked(&mut steps));
    assert(out@.take(8) =~= input@.take(8));
    (parsed, wrote, room)
}

/// Reads a run of three bytes, borrowed from the input, and writes it back.
pub fn witness_bytes<'a>(input: &'a [u8], out: &mut [u8]) -> (r: (Option<(usize, &'a [u8])>, Option<usize>, Option<usize>))
    requires
        input.len() >= 3,
        old(out).len() >= 3,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(3) == input@.take(3),
{
    let c: Bytes = Bytes { len: 3 };
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.unwrap();
    let room = c.length(&v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(&v, out, 0, Tracked(&mut steps));
    assert(out@.take(3) =~= input@.take(3));
    (parsed, wrote, room)
}

/// Reads a byte and then a run of two bytes as a pair, the run borrowed from the input, and writes
/// the pair back.
pub fn witness_pair<'a>(input: &'a [u8], out: &mut [u8]) -> (r: (Option<(usize, (u8, &'a [u8]))>, Option<usize>, Option<usize>))
    requires
        input.len() >= 3,
        old(out).len() >= 3,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(3) == input@.take(3),
{
    let c: Pair<U8, Bytes> = Pair { first: U8, second: Bytes { len: 2 } };
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.unwrap();
    let room = c.length(&v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(&v, out, 0, Tracked(&mut steps));
    assert(out@.take(3) =~= input@.take(3));
    (parsed, wrote, room)
}

/// Reads the IPv4 ethertype, 0x0800, as a tag and writes it back.
pub fn witness_tag(input: &[u8], out: &mut [u8]) -> (r: (Option<(usize, ())>, Option<usize>, Option<usize>))
    requires
        input.len() >= 2,
        input@[0] == 0x08,
        input@[1] == 0x00,
        old(out).len() >= 2,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(2) == input@.take(2),
{
    let ipv4: [u8; 2] = [0x08, 0x00];
    let c: Tag = Tag { bytes: &ipv4 };
    assert(c.bytes@ =~= input@.take(2));
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.unwrap();
    let room = c.length(&v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(&v, out, 0, Tracked(&mut steps));
    assert(out@.take(2) =~= input@.take(2));
    (parsed, wrote, room)
}

/// Tells an IPv4 ethertype from an IPv6 one, reading an IPv4 one, and writes it back.
pub fn witness_choice_first(input: &[u8], out: &mut [u8]) -> (r: (Option<(usize, Either<(), ()>)>, Option<usize>, Option<usize>))
    requires
        input.len() >= 2,
        input@[0] == 0x08,
        input@[1] == 0x00,
        old(out).len() >= 2,
    ensures
        r.0 is Some,
        r.0 matches Some((_, Either::First(_))),
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(2) == input@.take(2),
{
    let ipv4: [u8; 2] = [0x08, 0x00];
    let ipv6: [u8; 2] = [0x86, 0xdd];
    let c: Choice<Tag, Tag> = Choice { first: Tag { bytes: &ipv4 }, second: Tag { bytes: &ipv6 } };
    proof {
        lemma_ethertypes_disjoint(&c);
    }
    assert(c.first.bytes@ =~= input@.take(2));
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.as_ref().unwrap();
    let room = c.length(v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(v, out, 0, Tracked(&mut steps));
    assert(out@.take(2) =~= input@.take(2));
    (parsed, wrote, room)
}

/// Tells an IPv4 ethertype from an IPv6 one, reading an IPv6 one, and writes it back.
pub fn witness_choice_second(input: &[u8], out: &mut [u8]) -> (r: (Option<(usize, Either<(), ()>)>, Option<usize>, Option<usize>))
    requires
        input.len() >= 2,
        input@[0] == 0x86,
        input@[1] == 0xdd,
        old(out).len() >= 2,
    ensures
        r.0 is Some,
        r.0 matches Some((_, Either::Second(_))),
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(2) == input@.take(2),
{
    let ipv4: [u8; 2] = [0x08, 0x00];
    let ipv6: [u8; 2] = [0x86, 0xdd];
    let c: Choice<Tag, Tag> = Choice { first: Tag { bytes: &ipv4 }, second: Tag { bytes: &ipv6 } };
    proof {
        lemma_ethertypes_disjoint(&c);
    }
    assert(c.second.bytes@ =~= input@.take(2));
    assert(input@.take(2)[0] != c.first.bytes@[0]);
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.as_ref().unwrap();
    let room = c.length(v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(v, out, 0, Tracked(&mut steps));
    assert(out@.take(2) =~= input@.take(2));
    (parsed, wrote, room)
}

/// A tag of 0x08 0x00 refuses whatever starts with 0x86 0xdd.
proof fn lemma_ethertypes_disjoint(c: &Choice<Tag, Tag>)
    requires
        c.first.bytes@ == seq![0x08u8, 0x00u8],
        c.second.bytes@ == seq![0x86u8, 0xddu8],
    ensures
        c.wf(),
{
    assert forall|v: (), rest: Seq<u8>| c.second.valid(v) implies (#[trigger] c.first.spec_parse(c.second.spec_serialize(v) + rest)) is None by {
        let s = c.second.spec_serialize(v) + rest;
        assert(s[0] == 0x86u8);
        if 2 <= s.len() {
            assert(s.take(2)[0] != c.first.bytes@[0]);
        }
    }
}

/// Reads a run of three bytes behind a one-byte length of 3, borrowed from the input, and writes the
/// length and the run back.
pub fn witness_length_prefixed<'a>(input: &'a [u8], out: &mut [u8]) -> (r: (Option<(usize, &'a [u8])>, Option<usize>, Option<usize>))
    requires
        input.len() >= 4,
        input[0] == 3,
        old(out).len() >= 4,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(4) == input@.take(4),
{
    let c = LengthPrefixed::new(U8, Bytes { len: 3 });
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.unwrap();
    let room = c.length(&v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(&v, out, 0, Tracked(&mut steps));
    assert(out@.take(4) =~= input@.take(4));
    (parsed, wrote, room)
}

/// `u8` as a length: its width and its largest count, and the count 3 made into a value and read
/// back.
pub fn witness_length_u8() -> (r: (usize, usize, usize))
    ensures
        r == (1usize, u8::MAX as usize, 3usize),
{
    let c: U8 = U8;
    let w = c.width();
    let m = c.max();
    let t = c.of_len(3);
    let n = c.len_of(&t);
    (w, m, n)
}

/// `u16` as a length: its width and its largest count, and the count 3 made into a value and read
/// back.
pub fn witness_length_u16_be() -> (r: (usize, usize, usize))
    ensures
        r == (2usize, u16::MAX as usize, 3usize),
{
    let c: U16Be = U16Be;
    let w = c.width();
    let m = c.max();
    let t = c.of_len(3);
    let n = c.len_of(&t);
    (w, m, n)
}

/// `u16` as a length: its width and its largest count, and the count 3 made into a value and read
/// back.
pub fn witness_length_u16_le() -> (r: (usize, usize, usize))
    ensures
        r == (2usize, u16::MAX as usize, 3usize),
{
    let c: U16Le = U16Le;
    let w = c.width();
    let m = c.max();
    let t = c.of_len(3);
    let n = c.len_of(&t);
    (w, m, n)
}

/// `u32` as a length: its width and its largest count, and the count 3 made into a value and read
/// back.
pub fn witness_length_u32_be() -> (r: (usize, usize, usize))
    ensures
        r == (4usize, u32::MAX as usize, 3usize),
{
    let c: U32Be = U32Be;
    let w = c.width();
    let m = c.max();
    let t = c.of_len(3);
    let n = c.len_of(&t);
    (w, m, n)
}

/// `u32` as a length: its width and its largest count, and the count 3 made into a value and read
/// back.
pub fn witness_length_u32_le() -> (r: (usize, usize, usize))
    ensures
        r == (4usize, u32::MAX as usize, 3usize),
{
    let c: U32Le = U32Le;
    let w = c.width();
    let m = c.max();
    let t = c.of_len(3);
    let n = c.len_of(&t);
    (w, m, n)
}

/// The value a parse accepted, left where the parse put it.
fn accepted<T>(parsed: &Option<(usize, T)>) -> (t: &T)
    requires
        parsed is Some,
    ensures
        *t == (parsed->0).1,
{
    match parsed {
        Some((_, t)) => t,
        None => unreached(),
    }
}

/// Reads three bytes as exactly three `u8`s and writes them back.
pub fn witness_count(input: &[u8], out: &mut [u8]) -> (r: (Option<(usize, Elements<u8, 4>)>, Option<usize>, Option<usize>))
    requires
        input.len() >= 3,
        old(out).len() >= 3,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(3) == input@.take(3),
{
    let c: Count<U8, 4> = Count { inner: U8, count: 3 };
    proof {
        reveal_with_fuel(parse_count, 4);
    }
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let room = c.length(accepted(&parsed), out.len(), Tracked(&mut steps));
    let wrote = c.serialize(accepted(&parsed), out, 0, Tracked(&mut steps));
    assert(out@.take(3) =~= input@.take(3));
    (parsed, wrote, room)
}

/// A field as a format names it: a kind and a value, where the combinators give the pair of them.
#[derive(Clone, Copy)]
pub struct Field {
    pub kind: u8,
    pub value: u16,
}

impl View for Field {
    type V = Field;

    open spec fn view(&self) -> Field {
        *self
    }
}

/// A `Field` from the pair of its kind and value, and back.
pub struct FieldMapping;

impl Mapping<(u8, u16)> for FieldMapping {
    type T = Field;

    open spec fn spec_into(&self, s: (u8, u16)) -> Field {
        Field { kind: s.0, value: s.1 }
    }

    open spec fn spec_from(&self, t: Field) -> (u8, u16) {
        (t.kind, t.value)
    }

    open spec fn c(&self) -> nat {
        0
    }

    proof fn lemma_from_into(&self, s: (u8, u16)) {
    }

    proof fn lemma_into_from(&self, t: Field) {
    }

    fn map_into(&self, s: (u8, u16), Tracked(steps): Tracked<&mut Steps>) -> (t: Field) {
        Field { kind: s.0, value: s.1 }
    }

    fn map_from(&self, t: &Field, Tracked(steps): Tracked<&mut Steps>) -> (s: (u8, u16)) {
        (t.kind, t.value)
    }
}

/// Reads a byte and a big-endian `u16` as a `Field` with named members, and writes it back.
pub fn witness_mapped(input: &[u8], out: &mut [u8]) -> (r: (Option<(usize, Field)>, Option<usize>, Option<usize>))
    requires
        input.len() >= 3,
        old(out).len() >= 3,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(3) == input@.take(3),
{
    let c: Mapped<Pair<U8, U16Be>, FieldMapping> = Mapped { inner: Pair { first: U8, second: U16Be }, mapping: FieldMapping };
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, v) = parsed.unwrap();
    let room = c.length(&v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(&v, out, 0, Tracked(&mut steps));
    assert(out@.take(3) =~= input@.take(3));
    (parsed, wrote, room)
}

/// Reads a length of 2 and the two `u8`s it counts, at most three of them, and writes them back.
pub fn witness_bounded(input: &[u8], out: &mut [u8]) -> (r: (Option<(usize, Elements<u8, 4>)>, Option<usize>, Option<usize>))
    requires
        input.len() >= 3,
        input[0] == 2,
        old(out).len() >= 3,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(3) == input@.take(3),
{
    let c: Bounded<U8, U8, 4> = Bounded { length: U8, inner: U8, bound: 3 };
    proof {
        reveal_with_fuel(parse_fill, 3);
    }
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let room = c.length(accepted(&parsed), out.len(), Tracked(&mut steps));
    let wrote = c.serialize(accepted(&parsed), out, 0, Tracked(&mut steps));
    assert(out@.take(3) =~= input@.take(3));
    (parsed, wrote, room)
}

/// Builds two values in place and reads them back.
pub fn witness_elements() -> (r: (usize, u8, u8))
    ensures
        r == (2usize, 7u8, 9u8),
{
    let mut e: Elements<u8, 2> = Elements::new();
    e.push(7);
    e.push(9);
    let n = e.len();
    let a = e.get(0);
    let b = e.get(1);
    (n, a, b)
}

} // verus!
