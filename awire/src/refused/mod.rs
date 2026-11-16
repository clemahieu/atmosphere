// SPDX-License-Identifier: MIT

//! False claims, one module each, which Verus must refuse at the postconditions each names.
//! `u16_be_le` is the interface example and names no inventory line, and `choice_steps` is a step
//! count no bound may give and names none either. The others are claims about a type. Each but
//! `u16_be_le` states its claim as a trait here and its body in the module, so the refusal's body
//! span is the module's. tools/check-refused.py runs them under cfg(refused), which nothing else
//! sets, so they are in no image and no verify count. design/refused-claim-per-way/.
pub mod bounded_length;
pub mod bounded_round;
pub mod bytes_length;
pub mod bytes_round;
pub mod choice_steps;
pub mod count_length;
pub mod count_round;
pub mod elements_get;
pub mod elements_len;
pub mod elements_new;
pub mod elements_push;
pub mod length_prefixed_length;
pub mod length_prefixed_new;
pub mod length_prefixed_round;
pub mod pair_length;
pub mod pair_round;
pub mod tag_length;
pub mod tag_round;
pub mod u16_be_encoding;
pub mod u16_be_le;
pub mod u16_le_encoding;
pub mod u32_be_encoding;
pub mod u32_le_encoding;
pub mod u8_encoding;

use crate::*;

verus! {

/// A choice of alternatives that take no steps, parsing a 1000-byte input in none.
pub trait ChoiceSteps {
    fn zero(input: &[u8], Tracked(steps): Tracked<&mut Steps>)
        requires
            input.len() == 1000,
            input@[0] == 200u8,
            old(steps).count == 0,
        ensures
            final(steps).count == 0,
    ;
}

/// `Bytes`'s parse and serialize at the round trip they exclude.
pub trait BytesRound {
    proof fn parse_trip(c: &Bytes, s: Seq<u8>)
        requires
            c.wf(),
        ensures
            c.spec_parse(s) matches Some((n, v)) ==> c.spec_serialize(v) != s.take(n as int),
    ;

    proof fn serialize_trip(c: &Bytes, v: Seq<u8>, rest: Seq<u8>)
        requires
            c.wf(),
            c.valid(v),
        ensures
            c.spec_parse(c.spec_serialize(v) + rest) != Some((c.spec_serialize(v).len(), v)),
    ;
}

/// `Bytes::length`'s Some at a length that is not the serialisation's.
pub trait BytesLength {
    proof fn wrong(c: &Bytes, v: Seq<u8>, n: nat)
        requires
            c.wf(),
        ensures
            n != c.spec_serialize(v).len(),
    ;
}

/// `Count`'s parse and serialize at the round trip they exclude.
pub trait CountRound<'a, I: Combinator<'a>, const N: usize> where I::T: Copy {
    proof fn parse_trip(c: &Count<I, N>, s: Seq<u8>)
        requires
            c.wf(),
        ensures
            c.spec_parse(s) matches Some((n, v)) ==> c.spec_serialize(v) != s.take(n as int),
    ;

    proof fn serialize_trip(c: &Count<I, N>, v: Seq<I::V>, rest: Seq<u8>)
        requires
            c.wf(),
            c.valid(v),
        ensures
            c.spec_parse(c.spec_serialize(v) + rest) != Some((c.spec_serialize(v).len(), v)),
    ;
}

/// `Count::length`'s Some at a length that is not the serialisation's.
pub trait CountLength<'a, I: Combinator<'a>, const N: usize> where I::T: Copy {
    proof fn wrong(c: &Count<I, N>, v: Seq<I::V>, n: nat)
        requires
            c.wf(),
        ensures
            n != c.spec_serialize(v).len(),
    ;
}

/// `Bounded`'s parse and serialize at the round trip they exclude.
pub trait BoundedRound<'a, L: Length<'a>, I: Combinator<'a>, const N: usize> where I::T: Copy {
    proof fn parse_trip(c: &Bounded<L, I, N>, s: Seq<u8>)
        requires
            c.wf(),
        ensures
            c.spec_parse(s) matches Some((n, v)) ==> c.spec_serialize(v) != s.take(n as int),
    ;

    proof fn serialize_trip(c: &Bounded<L, I, N>, v: Seq<I::V>, rest: Seq<u8>)
        requires
            c.wf(),
            c.valid(v),
        ensures
            c.spec_parse(c.spec_serialize(v) + rest) != Some((c.spec_serialize(v).len(), v)),
    ;
}

/// `Bounded::length`'s Some at a length that is not the serialisation's.
pub trait BoundedLength<'a, L: Length<'a>, I: Combinator<'a>, const N: usize> where I::T: Copy {
    proof fn wrong(c: &Bounded<L, I, N>, v: Seq<I::V>, n: nat)
        requires
            c.wf(),
        ensures
            n != c.spec_serialize(v).len(),
    ;
}

/// `Elements::new` at a value that is not the empty sequence.
pub trait ElementsNew<T: Copy + View, const N: usize> {
    proof fn wrong(r: Elements<T, N>)
        ensures
            r@ != Seq::<T::V>::empty(),
    ;
}

/// `Elements::len` at a count that is not the length.
pub trait ElementsLen<T: Copy + View, const N: usize> {
    proof fn wrong(e: &Elements<T, N>, n: usize)
        ensures
            n != e@.len(),
    ;
}

/// `Elements::get` at a value that is not the element at `i`.
pub trait ElementsGet<T: Copy + View, const N: usize> {
    proof fn wrong(e: &Elements<T, N>, i: usize, t: T)
        requires
            i < e@.len(),
        ensures
            t@ != e@[i as int],
    ;
}

/// `Elements::push` at an unchanged buffer, which meets the operation's ensures.
pub trait ElementsPush<T: Copy + View, const N: usize> {
    proof fn unchanged(pre: Elements<T, N>, post: Elements<T, N>, t: T)
        requires
            pre@.len() < N,
            post == pre,
        ensures
            post@ == pre@.push(t@),
    ;
}

/// `LengthPrefixed::new` at fields that are not the arguments.
pub trait LengthPrefixedNew<L, I> {
    proof fn wrong(r: LengthPrefixed<L, I>, length: L, inner: I)
        ensures
            !(r.length == length && r.inner == inner),
    ;
}

/// `LengthPrefixed`'s parse and serialize at the round trip they exclude.
pub trait LengthPrefixedRound<'a, L: Length<'a>, I: Combinator<'a>> {
    proof fn parse_trip(c: &LengthPrefixed<L, I>, s: Seq<u8>)
        requires
            c.wf(),
        ensures
            c.spec_parse(s) matches Some((n, v)) ==> c.spec_serialize(v) != s.take(n as int),
    ;

    proof fn serialize_trip(c: &LengthPrefixed<L, I>, v: I::V, rest: Seq<u8>)
        requires
            c.wf(),
            c.valid(v),
        ensures
            c.spec_parse(c.spec_serialize(v) + rest) != Some((c.spec_serialize(v).len(), v)),
    ;
}

/// `LengthPrefixed::length`'s Some at a length that is not the serialisation's.
pub trait LengthPrefixedLength<'a, L: Length<'a>, I: Combinator<'a>> {
    proof fn wrong(c: &LengthPrefixed<L, I>, v: I::V, n: nat)
        requires
            c.wf(),
        ensures
            n != c.spec_serialize(v).len(),
    ;
}

/// `Pair`'s parse and serialize at the round trip they exclude.
pub trait PairRound<'a, A: Combinator<'a>, B: Combinator<'a>> {
    proof fn parse_trip(c: &Pair<A, B>, s: Seq<u8>)
        requires
            c.wf(),
        ensures
            c.spec_parse(s) matches Some((n, v)) ==> c.spec_serialize(v) != s.take(n as int),
    ;

    proof fn serialize_trip(c: &Pair<A, B>, v: (A::V, B::V), rest: Seq<u8>)
        requires
            c.wf(),
            c.valid(v),
        ensures
            c.spec_parse(c.spec_serialize(v) + rest) != Some((c.spec_serialize(v).len(), v)),
    ;
}

/// `Pair::length`'s Some at a length that is not the serialisation's.
pub trait PairLength<'a, A: Combinator<'a>, B: Combinator<'a>> {
    proof fn wrong(c: &Pair<A, B>, v: (A::V, B::V), n: nat)
        requires
            c.wf(),
        ensures
            n != c.spec_serialize(v).len(),
    ;
}

/// `Tag`'s parse and serialize at the round trip they exclude.
pub trait TagRound<'t> {
    proof fn parse_trip(c: &Tag<'t>, s: Seq<u8>)
        requires
            c.wf(),
        ensures
            c.spec_parse(s) matches Some((n, v)) ==> c.spec_serialize(v) != s.take(n as int),
    ;

    proof fn serialize_trip(c: &Tag<'t>, v: (), rest: Seq<u8>)
        requires
            c.wf(),
            c.valid(v),
        ensures
            c.spec_parse(c.spec_serialize(v) + rest) != Some((c.spec_serialize(v).len(), v)),
    ;
}

/// `Tag::length`'s Some at a length that is not the serialisation's.
pub trait TagLength<'t> {
    proof fn wrong(c: &Tag<'t>, v: (), n: nat)
        requires
            c.wf(),
        ensures
            n != c.spec_serialize(v).len(),
    ;
}

/// A length encoding's `width`, `max`, `len_of` and `of_len` at an output the ensures excludes.
/// Each operation returns the spec value; this is that ensures at the other output, and the
/// requires are the operation's. One impl per encoding, so the claim is about that type.
pub trait LengthEncodingReturns<'a, L: Length<'a>> {
    proof fn width(c: &L, w: usize)
        requires
            c.wf(),
        ensures
            w != c.spec_width(),
    ;

    proof fn max(c: &L, m: usize)
        requires
            c.wf(),
        ensures
            m != c.spec_max(),
    ;

    proof fn len_of(c: &L, t: &L::T, n: usize)
        requires
            c.wf(),
            c.valid(t@),
        ensures
            n != c.spec_len(t@),
    ;

    proof fn of_len(c: &L, n: usize, t: L::T)
        requires
            c.wf(),
            n <= c.spec_max(),
        ensures
            t@ != c.spec_of_len(n as nat),
    ;
}

} // verus!
