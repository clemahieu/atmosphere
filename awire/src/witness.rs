// SPDX-License-Identifier: MIT

//! The witnesses, built into no image: for each combinator, a caller holding an input and an
//! output buffer, as a format's parser and serialiser do, parses a value from the input and writes
//! it back, having first asked the value's serialised length within the buffer's room, as a composite
//! does before it writes; the buffer then starts with exactly the bytes the parse consumed. Each
//! reaches the accepting way of the combinator's `parse`, `length` and `serialize`.
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

} // verus!
