// SPDX-License-Identifier: MIT

//! False claims, one module each, which Verus must refuse at the postconditions each names.
//! `u16_be_le` is the interface example and names no inventory line. The others are claims about a
//! combinator: the specification is the trait and the body is the module, so the refusal's body
//! span is the module's. tools/check-refused.py runs them under cfg(refused), which nothing else
//! sets, so they are in no image and no verify count. design/refused-claim-per-way/.
pub mod bounded_length;
pub mod bounded_round;
pub mod bytes_length;
pub mod bytes_round;
pub mod count_length;
pub mod count_round;
pub mod u16_be_le;

use crate::*;

verus! {

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

} // verus!
