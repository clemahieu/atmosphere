// SPDX-License-Identifier: MIT

//! The combinators every wire format of the network stack is parsed and serialised in
//! (design/network-stack-proven-at-tier-1/, rule 1; design/wire-combinators-written-here/).
//!
//! Each combinator implements `Combinator`. Its spec parse is total: every byte string is accepted,
//! with the bytes consumed and the value, or refused. Its exec parse returns exactly the spec parse
//! and states again on its result that the bytes consumed are within the input, that the value is
//! one the format can carry and that serialising it gives back exactly the bytes it consumed. Its
//! exec serialise writes exactly the spec serialisation at the position it is given, leaving every
//! other byte as it was, or refuses, leaving the buffer as it was, exactly when the value is not one
//! the format can carry or does not fit. Both run no loop without a decreases clause, so Verus proves
//! they end, and both bound the ghost `Steps` they add by `k * bytes + c`, `k` and `c` constants of
//! the combinator's specification.
//!
//! The combinators here: `U8`, `U16Be`, `U16Le`, `U32Be`, `U32Le`, `U64Be` and `U64Le`, the
//! fixed-width unsigned integers in each byte order, assembled by shifts; and `Bytes`, a run of a
//! length given as a parameter, whose value borrows the input. Nothing allocates.
#![cfg_attr(not(test), no_std)]

use vstd::prelude::*;

mod bytes;
mod integer;
pub use bytes::*;
pub use integer::*;
#[cfg(throwaway)]
mod throwaway;
#[cfg(verus_keep_ghost)]
mod witness;

verus! {

/// Units of work done so far: one per iteration of an exec loop, a callee's units adding to its
/// caller's, as design/one-lock-bounded-steps/ counts the kernel's. A combinator takes it as
/// `Tracked<&mut Steps>` and ensures the count rose by at most its bound.
pub tracked struct Steps {
    pub ghost count: nat,
}

impl Steps {
    /// A counter at zero, which whoever starts a parse or a serialisation makes.
    pub proof fn fresh() -> (tracked ret: Steps)
        ensures
            ret.count == 0,
    {
        Steps { count: 0 }
    }

    /// One iteration's unit.
    pub proof fn step(tracked &mut self)
        ensures
            final(self).count == old(self).count + 1,
    {
        self.count = self.count + 1;
    }
}

/// `before` with `bytes` written from `pos`, every other byte as it was.
pub open spec fn written(before: Seq<u8>, pos: int, bytes: Seq<u8>) -> Seq<u8> {
    before.take(pos) + bytes + before.skip(pos + bytes.len())
}

/// A parser and serialiser of one wire format. `V` is the value as the specification sees it, `T`
/// the value exec code holds, which may borrow the input for `'a`.
pub trait Combinator<'a> {
    type V;

    type T: View<V = Self::V>;

    /// The parameters the combinator was built with are usable.
    spec fn wf(&self) -> bool;

    /// The bytes `s` starts with, as the format reads them: the count consumed and the value, or
    /// `None` when `s` does not start with a value of the format.
    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, Self::V)>;

    /// The bytes `v` is written as.
    spec fn spec_serialize(&self, v: Self::V) -> Seq<u8>;

    /// The values the format can carry.
    spec fn valid(&self, v: Self::V) -> bool;

    /// The steps a parse or a serialisation adds per byte it consumes or writes.
    spec fn k(&self) -> nat;

    /// The steps a parse or a serialisation adds besides those per byte.
    spec fn c(&self) -> nat;

    /// A parse consumes at most its input, gives a value the format can carry, and serialising
    /// that value gives back exactly the bytes consumed. Each is its own clause, so a proof that
    /// fails one is refused at that one.
    proof fn lemma_parse_serialize(&self, s: Seq<u8>)
        requires
            self.wf(),
        ensures
            self.spec_parse(s) matches Some((n, v)) ==> n <= s.len(),
            self.spec_parse(s) matches Some((n, v)) ==> self.valid(v),
            self.spec_parse(s) matches Some((n, v)) ==> self.spec_serialize(v) == s.take(n as int),
    ;

    /// A serialised value parses back to itself, whatever follows it.
    proof fn lemma_serialize_parse(&self, v: Self::V, rest: Seq<u8>)
        requires
            self.wf(),
            self.valid(v),
        ensures
            self.spec_parse(self.spec_serialize(v) + rest) == Some((self.spec_serialize(v).len(), v)),
    ;

    /// Parses the start of `input`: the spec parse of it, with what `lemma_parse_serialize` says
    /// of an accepted one stated on the result, and at most `k * n + c` steps when it consumed `n`
    /// bytes, `k * input.len() + c` when it refused.
    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, Self::T)>)
        requires
            self.wf(),
        ensures
            match r {
                None => {
                    &&& self.spec_parse(input@) is None
                    &&& final(steps).count <= old(steps).count + self.k() * input.len() + self.c()
                },
                Some((n, t)) => {
                    &&& self.spec_parse(input@) == Some((n as nat, t@))
                    &&& n <= input.len()
                    &&& self.valid(t@)
                    &&& self.spec_serialize(t@) == input@.take(n as int)
                    &&& final(steps).count <= old(steps).count + self.k() * n + self.c()
                },
            },
    ;

    /// Writes the serialisation of `v` into `out` from `pos` and returns its length, every other
    /// byte as it was; or refuses, `out` as it was, exactly when `v` is not one the format can carry
    /// or its bytes do not fit. At most `k * n + c` steps when it wrote `n` bytes, `c` when it
    /// refused.
    fn serialize(&self, v: &Self::T, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>)
        requires
            self.wf(),
        ensures
            match r {
                None => {
                    &&& !(self.valid(v@) && pos + self.spec_serialize(v@).len() <= old(out)@.len())
                    &&& final(out)@ == old(out)@
                    &&& final(steps).count <= old(steps).count + self.c()
                },
                Some(n) => {
                    &&& self.valid(v@)
                    &&& n == self.spec_serialize(v@).len()
                    &&& pos + n <= old(out)@.len()
                    &&& final(out)@ == written(old(out)@, pos as int, self.spec_serialize(v@))
                    &&& final(steps).count <= old(steps).count + self.k() * n + self.c()
                },
            },
    ;
}

} // verus!
