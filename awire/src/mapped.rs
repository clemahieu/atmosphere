// SPDX-License-Identifier: MIT

//! `Mapped`, a combinator whose value is another's through a bijection: what gives a format's value
//! named fields where the combinators it is written in give nested pairs, so the protocol above reads
//! a field by its name and not by its place in the nesting.
//!
//! The bijection is a `Mapping` from the exec values of the inner combinator, `S`, to the format's,
//! `T`: spec functions each way, with the lemmas that each undoes the other, and exec functions each
//! way proven equal to them. Parsing is the inner parse with its value mapped into `T`; the length
//! and the serialisation are the inner's of the value mapped back. The mapping declares the steps a
//! conversion takes, its `c`, which is the whole of its cost: a conversion reads no byte. A
//! serialisation converts once and the length once more, so `Mapped`'s `c` is the inner's and twice
//! the mapping's, and its `k` is the inner's.

use crate::*;

verus! {

/// A bijection between the exec values `S` of one combinator and those of a format, `Self::T`.
pub trait Mapping<S: View> {
    type T: View;

    /// The format's value of the inner value `s`.
    spec fn spec_into(&self, s: S::V) -> <Self::T as View>::V;

    /// The inner value of the format's value `t`.
    spec fn spec_from(&self, t: <Self::T as View>::V) -> S::V;

    /// The steps a conversion takes, each way.
    spec fn c(&self) -> nat;

    /// Mapping back undoes mapping into.
    proof fn lemma_from_into(&self, s: S::V)
        ensures
            self.spec_from(self.spec_into(s)) == s,
    ;

    /// Mapping into undoes mapping back.
    proof fn lemma_into_from(&self, t: <Self::T as View>::V)
        ensures
            self.spec_into(self.spec_from(t)) == t,
    ;

    /// The format's value of `s`, in at most `c` steps.
    fn map_into(&self, s: S, Tracked(steps): Tracked<&mut Steps>) -> (t: Self::T)
        ensures
            t@ == self.spec_into(s@),
            final(steps).count <= old(steps).count + self.c(),
    ;

    /// The inner value of `t`, in at most `c` steps.
    fn map_from(&self, t: &Self::T, Tracked(steps): Tracked<&mut Steps>) -> (s: S)
        ensures
            s@ == self.spec_from(t@),
            final(steps).count <= old(steps).count + self.c(),
    ;
}

/// `inner`, its value through `mapping`.
pub struct Mapped<I, M> {
    pub inner: I,
    pub mapping: M,
}

impl<'a, I: Combinator<'a>, M: Mapping<I::T>> Combinator<'a> for Mapped<I, M> {
    type V = <M::T as View>::V;

    type T = M::T;

    open spec fn wf(&self) -> bool {
        self.inner.wf()
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, <M::T as View>::V)> {
        match self.inner.spec_parse(s) {
            Some((n, v)) => Some((n, self.mapping.spec_into(v))),
            None => None,
        }
    }

    open spec fn spec_serialize(&self, v: <M::T as View>::V) -> Seq<u8> {
        self.inner.spec_serialize(self.mapping.spec_from(v))
    }

    open spec fn valid(&self, v: <M::T as View>::V) -> bool {
        self.inner.valid(self.mapping.spec_from(v))
    }

    open spec fn k(&self) -> nat {
        self.inner.k()
    }

    open spec fn c(&self) -> nat {
        self.inner.c() + 2 * self.mapping.c()
    }

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        self.inner.lemma_parse_serialize(s);
        if let Some((n, v)) = self.inner.spec_parse(s) {
            self.mapping.lemma_from_into(v);
        }
    }

    proof fn lemma_serialize_parse(&self, v: <M::T as View>::V, rest: Seq<u8>) {
        self.inner.lemma_serialize_parse(self.mapping.spec_from(v), rest);
        self.mapping.lemma_into_from(v);
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, M::T)>) {
        let (n, v) = match self.inner.parse(input, Tracked(&mut *steps)) {
            Some(p) => p,
            None => return None,
        };
        proof {
            self.mapping.lemma_from_into(v@);
        }
        let t = self.mapping.map_into(v, Tracked(&mut *steps));
        Some((n, t))
    }

    fn length(&self, v: &M::T, cap: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        let s = self.mapping.map_from(v, Tracked(&mut *steps));
        self.inner.length(&s, cap, Tracked(&mut *steps))
    }

    fn serialize(&self, v: &M::T, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        let s = self.mapping.map_from(v, Tracked(&mut *steps));
        self.inner.serialize(&s, out, pos, Tracked(&mut *steps))
    }
}

} // verus!
