// SPDX-License-Identifier: MIT

//! `Pair`, one combinator then another: its first part parsed from the start of the input and its
//! second from the rest, its value the pair of theirs, serialised as the first part's bytes followed
//! by the second's.
//!
//! A serialisation writes the second part before the first. It asks the first part's length within
//! the room it was given, which says where the second part goes; the second part's serialise then
//! writes it or refuses with the buffer as it was; and only then is the first part written, into
//! room its length has shown is there. So a refusal leaves the buffer as it was. The first part's
//! bytes are counted twice, once for its length and once for its serialisation, which is why the
//! pair's `k` is twice its first part's when that is the larger.

use vstd::slice::slice_subrange;

use crate::*;

verus! {

/// Each part's steps per byte within `k`, so their sum on `x` and `y` bytes is within `k * (x + y)`.
proof fn lemma_within(ka: nat, kb: nat, k: nat, x: nat, y: nat)
    requires
        ka <= k,
        kb <= k,
    ensures
        ka * x + kb * y <= k * (x + y),
{
    assert(ka * x + kb * y <= k * (x + y)) by (nonlinear_arith)
        requires
            ka <= k,
            kb <= k,
    ;
}

/// `first`, then `second` on the bytes after it.
pub struct Pair<A, B> {
    pub first: A,
    pub second: B,
}

impl<'a, A: Combinator<'a>, B: Combinator<'a>> Combinator<'a> for Pair<A, B> {
    type V = (A::V, B::V);

    type T = (A::T, B::T);

    open spec fn wf(&self) -> bool {
        &&& self.first.wf()
        &&& self.second.wf()
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, (A::V, B::V))> {
        match self.first.spec_parse(s) {
            Some((n, a)) => match self.second.spec_parse(s.skip(n as int)) {
                Some((m, b)) => Some((n + m, (a, b))),
                None => None,
            },
            None => None,
        }
    }

    open spec fn spec_serialize(&self, v: (A::V, B::V)) -> Seq<u8> {
        self.first.spec_serialize(v.0) + self.second.spec_serialize(v.1)
    }

    open spec fn valid(&self, v: (A::V, B::V)) -> bool {
        &&& self.first.valid(v.0)
        &&& self.second.valid(v.1)
    }

    open spec fn k(&self) -> nat {
        if 2 * self.first.k() >= self.second.k() {
            2 * self.first.k()
        } else {
            self.second.k()
        }
    }

    open spec fn c(&self) -> nat {
        2 * self.first.c() + self.second.c()
    }

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        self.first.lemma_parse_serialize(s);
        if let Some((n, a)) = self.first.spec_parse(s) {
            let rest = s.skip(n as int);
            self.second.lemma_parse_serialize(rest);
            if let Some((m, b)) = self.second.spec_parse(rest) {
                assert(s.take(n as int) + rest.take(m as int) =~= s.take((n + m) as int));
            }
        }
    }

    proof fn lemma_serialize_parse(&self, v: (A::V, B::V), rest: Seq<u8>) {
        let sa = self.first.spec_serialize(v.0);
        let sb = self.second.spec_serialize(v.1);
        assert(sa + sb + rest =~= sa + (sb + rest));
        self.first.lemma_serialize_parse(v.0, sb + rest);
        assert((sa + (sb + rest)).skip(sa.len() as int) =~= sb + rest);
        self.second.lemma_serialize_parse(v.1, rest);
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, (A::T, B::T))>) {
        proof {
            lemma_within(self.first.k(), self.second.k(), self.k(), input.len() as nat, 0);
        }
        let (n, a) = match self.first.parse(input, Tracked(&mut *steps)) {
            Some(p) => p,
            None => return None,
        };
        let rest = slice_subrange(input, n, input.len());
        assert(rest@ =~= input@.skip(n as int));
        proof {
            lemma_within(self.first.k(), self.second.k(), self.k(), n as nat, rest.len() as nat);
        }
        let (m, b) = match self.second.parse(rest, Tracked(&mut *steps)) {
            Some(p) => p,
            None => return None,
        };
        proof {
            lemma_within(self.first.k(), self.second.k(), self.k(), n as nat, m as nat);
            assert(input@.take(n as int) + rest@.take(m as int) =~= input@.take((n + m) as int));
        }
        Some((n + m, (a, b)))
    }

    fn length(&self, v: &(A::T, B::T), cap: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        proof {
            lemma_within(self.first.k(), self.second.k(), self.k(), cap as nat, 0);
        }
        let n = match self.first.length(&v.0, cap, Tracked(&mut *steps)) {
            Some(n) => n,
            None => return None,
        };
        proof {
            lemma_within(self.first.k(), self.second.k(), self.k(), n as nat, (cap - n) as nat);
        }
        let m = match self.second.length(&v.1, cap - n, Tracked(&mut *steps)) {
            Some(m) => m,
            None => return None,
        };
        proof {
            lemma_within(self.first.k(), self.second.k(), self.k(), n as nat, m as nat);
        }
        Some(n + m)
    }

    fn serialize(&self, v: &(A::T, B::T), out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        if pos > out.len() {
            return None;
        }
        let ghost before = out@;
        let room = out.len() - pos;
        proof {
            lemma_within(self.first.k(), self.second.k(), self.k(), room as nat, 0);
        }
        let n = match self.first.length(&v.0, room, Tracked(&mut *steps)) {
            Some(n) => n,
            None => return None,
        };
        proof {
            lemma_within(self.first.k(), self.second.k(), self.k(), n as nat, (room - n) as nat);
        }
        let m = match self.second.serialize(&v.1, out, pos + n, Tracked(&mut *steps)) {
            Some(m) => m,
            None => return None,
        };
        // The first part fits, as its length showed, so its serialisation cannot refuse.
        self.first.serialize(&v.0, out, pos, Tracked(&mut *steps)).unwrap();
        proof {
            lemma_within(2 * self.first.k(), self.second.k(), self.k(), n as nat, m as nat);
            assert((2 * self.first.k()) * n == self.first.k() * n + self.first.k() * n) by (nonlinear_arith);
            let sa = self.first.spec_serialize(v.0@);
            let sb = self.second.spec_serialize(v.1@);
            assert(out@ =~= written(before, pos as int, sa + sb));
        }
        Some(n + m)
    }
}

} // verus!
