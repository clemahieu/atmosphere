// SPDX-License-Identifier: MIT

//! `LengthPrefixed`, a length and then a value over exactly that many bytes, and `Length`, the
//! integer combinators a length is carried in.
//!
//! A parse reads the length with `L`, then parses `I` over exactly the bytes the length counts, and
//! refuses when the input holds fewer or `I` consumes fewer than all of them. A length asks `I`'s
//! within the room behind the length's bytes, no more than the largest length. A serialisation
//! writes `I`'s bytes behind the room the length takes, into a window no longer than the largest
//! length, so a value the length cannot count is refused with the buffer as it was, and then writes
//! the length in front, which cannot refuse. Its steps are `L`'s and `I`'s added: `k` and `c` are
//! the sums of theirs.

use crate::*;
use vstd::slice::slice_subrange;

verus! {

/// An integer combinator that carries a length: each value counts a number of bytes up to a largest
/// one, every count up to it has exactly one value, and every value is written in the same number
/// of bytes.
pub trait Length<'a>: Combinator<'a> {
    /// The bytes every value is written in.
    spec fn spec_width(&self) -> nat;

    /// The largest count a value carries.
    spec fn spec_max(&self) -> nat;

    /// The count the value `v` carries.
    spec fn spec_len(&self, v: Self::V) -> nat;

    /// The value that carries the count `n`.
    spec fn spec_of_len(&self, n: nat) -> Self::V;

    /// Every value is written in `spec_width` bytes, and a value the format carries counts at most
    /// `spec_max` and is the one value of its count.
    proof fn lemma_length(&self, v: Self::V)
        requires
            self.wf(),
        ensures
            self.spec_serialize(v).len() == self.spec_width(),
            self.valid(v) ==> self.spec_len(v) <= self.spec_max(),
            self.valid(v) ==> self.spec_of_len(self.spec_len(v)) == v,
    ;

    /// Every count up to `spec_max` has a value the format carries.
    proof fn lemma_of_len(&self, n: nat)
        requires
            self.wf(),
            n <= self.spec_max(),
        ensures
            self.valid(self.spec_of_len(n)),
            self.spec_len(self.spec_of_len(n)) == n,
    ;

    /// `spec_width`.
    fn width(&self) -> (w: usize)
        requires
            self.wf(),
        ensures
            w == self.spec_width(),
    ;

    /// `spec_max`.
    fn max(&self) -> (m: usize)
        requires
            self.wf(),
        ensures
            m == self.spec_max(),
    ;

    /// The count `t` carries.
    fn len_of(&self, t: &Self::T) -> (n: usize)
        requires
            self.wf(),
            self.valid(t@),
        ensures
            n == self.spec_len(t@),
    ;

    /// The value that carries the count `n`.
    fn of_len(&self, n: usize) -> (t: Self::T)
        requires
            self.wf(),
            n <= self.spec_max(),
        ensures
            t@ == self.spec_of_len(n as nat),
    ;
}

impl<'a> Length<'a> for U8 {
    open spec fn spec_width(&self) -> nat {
        1
    }

    open spec fn spec_max(&self) -> nat {
        u8::MAX as nat
    }

    open spec fn spec_len(&self, v: u8) -> nat {
        v as nat
    }

    open spec fn spec_of_len(&self, n: nat) -> u8 {
        n as u8
    }

    proof fn lemma_length(&self, v: u8) {
    }

    proof fn lemma_of_len(&self, n: nat) {
    }

    fn width(&self) -> (w: usize) {
        1
    }

    fn max(&self) -> (m: usize) {
        u8::MAX as usize
    }

    fn len_of(&self, t: &u8) -> (n: usize) {
        *t as usize
    }

    fn of_len(&self, n: usize) -> (t: u8) {
        n as u8
    }
}

impl<'a> Length<'a> for U16Be {
    open spec fn spec_width(&self) -> nat {
        2
    }

    open spec fn spec_max(&self) -> nat {
        u16::MAX as nat
    }

    open spec fn spec_len(&self, v: u16) -> nat {
        v as nat
    }

    open spec fn spec_of_len(&self, n: nat) -> u16 {
        n as u16
    }

    proof fn lemma_length(&self, v: u16) {
    }

    proof fn lemma_of_len(&self, n: nat) {
    }

    fn width(&self) -> (w: usize) {
        2
    }

    fn max(&self) -> (m: usize) {
        u16::MAX as usize
    }

    fn len_of(&self, t: &u16) -> (n: usize) {
        *t as usize
    }

    fn of_len(&self, n: usize) -> (t: u16) {
        n as u16
    }
}

impl<'a> Length<'a> for U16Le {
    open spec fn spec_width(&self) -> nat {
        2
    }

    open spec fn spec_max(&self) -> nat {
        u16::MAX as nat
    }

    open spec fn spec_len(&self, v: u16) -> nat {
        v as nat
    }

    open spec fn spec_of_len(&self, n: nat) -> u16 {
        n as u16
    }

    proof fn lemma_length(&self, v: u16) {
    }

    proof fn lemma_of_len(&self, n: nat) {
    }

    fn width(&self) -> (w: usize) {
        2
    }

    fn max(&self) -> (m: usize) {
        u16::MAX as usize
    }

    fn len_of(&self, t: &u16) -> (n: usize) {
        *t as usize
    }

    fn of_len(&self, n: usize) -> (t: u16) {
        n as u16
    }
}

impl<'a> Length<'a> for U32Be {
    open spec fn spec_width(&self) -> nat {
        4
    }

    open spec fn spec_max(&self) -> nat {
        u32::MAX as nat
    }

    open spec fn spec_len(&self, v: u32) -> nat {
        v as nat
    }

    open spec fn spec_of_len(&self, n: nat) -> u32 {
        n as u32
    }

    proof fn lemma_length(&self, v: u32) {
    }

    proof fn lemma_of_len(&self, n: nat) {
    }

    fn width(&self) -> (w: usize) {
        4
    }

    fn max(&self) -> (m: usize) {
        u32::MAX as usize
    }

    fn len_of(&self, t: &u32) -> (n: usize) {
        *t as usize
    }

    fn of_len(&self, n: usize) -> (t: u32) {
        n as u32
    }
}

impl<'a> Length<'a> for U32Le {
    open spec fn spec_width(&self) -> nat {
        4
    }

    open spec fn spec_max(&self) -> nat {
        u32::MAX as nat
    }

    open spec fn spec_len(&self, v: u32) -> nat {
        v as nat
    }

    open spec fn spec_of_len(&self, n: nat) -> u32 {
        n as u32
    }

    proof fn lemma_length(&self, v: u32) {
    }

    proof fn lemma_of_len(&self, n: nat) {
    }

    fn width(&self) -> (w: usize) {
        4
    }

    fn max(&self) -> (m: usize) {
        u32::MAX as usize
    }

    fn len_of(&self, t: &u32) -> (n: usize) {
        *t as usize
    }

    fn of_len(&self, n: usize) -> (t: u32) {
        n as u32
    }
}

/// `a * x + b * y` steps, with `x + y` at most `z`, are at most `(a + b) * z`.
proof fn lemma_steps(a: nat, b: nat, x: nat, y: nat, z: nat)
    requires
        x + y <= z,
    ensures
        a * x + b * y <= (a + b) * z,
{
    assert(a * x + b * y <= (a + b) * z) by (nonlinear_arith)
        requires
            x + y <= z,
    ;
}

/// `k` steps per byte on `x` bytes are at most `k` per byte on `y`, when `x` is at most `y`.
proof fn lemma_fewer(k: nat, x: nat, y: nat)
    requires
        x <= y,
    ensures
        k * x <= k * y,
{
    assert(k * x <= k * y) by (nonlinear_arith)
        requires
            x <= y,
    ;
}

/// A length read with `length`, then `inner` over exactly the bytes it counts.
pub struct LengthPrefixed<L, I> {
    pub length: L,
    pub inner: I,
}

impl<L, I> LengthPrefixed<L, I> {
    /// `inner` behind a length read with `length`.
    pub fn new(length: L, inner: I) -> (r: Self)
        ensures
            r.length == length,
            r.inner == inner,
    {
        LengthPrefixed { length, inner }
    }
}

impl<'a, L: Length<'a>, I: Combinator<'a>> Combinator<'a> for LengthPrefixed<L, I> {
    type V = I::V;

    type T = I::T;

    open spec fn wf(&self) -> bool {
        self.length.wf() && self.inner.wf()
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, I::V)> {
        match self.length.spec_parse(s) {
            None => None,
            Some((m, l)) => {
                let len = self.length.spec_len(l);
                if m + len <= s.len() {
                    match self.inner.spec_parse(s.subrange(m as int, (m + len) as int)) {
                        Some((n, v)) => if n == len {
                            Some(((m + len) as nat, v))
                        } else {
                            None
                        },
                        None => None,
                    }
                } else {
                    None
                }
            },
        }
    }

    open spec fn spec_serialize(&self, v: I::V) -> Seq<u8> {
        let b = self.inner.spec_serialize(v);
        self.length.spec_serialize(self.length.spec_of_len(b.len())) + b
    }

    open spec fn valid(&self, v: I::V) -> bool {
        self.inner.valid(v) && self.inner.spec_serialize(v).len() <= self.length.spec_max()
    }

    open spec fn k(&self) -> nat {
        self.length.k() + self.inner.k()
    }

    open spec fn c(&self) -> nat {
        self.length.c() + self.inner.c()
    }

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        self.length.lemma_parse_serialize(s);
        match self.length.spec_parse(s) {
            None => {},
            Some((m, l)) => {
                self.length.lemma_length(l);
                let len = self.length.spec_len(l);
                if m + len <= s.len() {
                    let body = s.subrange(m as int, (m + len) as int);
                    self.inner.lemma_parse_serialize(body);
                    match self.inner.spec_parse(body) {
                        None => {},
                        Some((n, v)) => {
                            if n == len {
                                assert(body.take(n as int) =~= body);
                                assert(s.take(m as int) + body =~= s.take((m + len) as int));
                            }
                        },
                    }
                }
            },
        }
    }

    proof fn lemma_serialize_parse(&self, v: I::V, rest: Seq<u8>) {
        let b = self.inner.spec_serialize(v);
        let l = self.length.spec_of_len(b.len());
        self.length.lemma_of_len(b.len());
        let p = self.length.spec_serialize(l);
        self.length.lemma_serialize_parse(l, b + rest);
        assert(p + b + rest =~= p + (b + rest));
        let body = (p + b + rest).subrange(p.len() as int, (p.len() + b.len()) as int);
        assert(body =~= b + Seq::<u8>::empty());
        self.inner.lemma_serialize_parse(v, Seq::<u8>::empty());
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, I::T)>) {
        let ghost count = steps.count;
        let (m, l) = match self.length.parse(input, Tracked(steps)) {
            Some(p) => p,
            None => {
                proof {
                    lemma_steps(self.length.k(), self.inner.k(), input.len() as nat, 0, input.len() as nat);
                }
                return None;
            },
        };
        proof {
            self.length.lemma_length(l@);
            lemma_steps(self.length.k(), self.inner.k(), m as nat, 0, input.len() as nat);
        }
        let len = self.length.len_of(&l);
        if input.len() - m < len {
            return None;
        }
        let body = slice_subrange(input, m, m + len);
        let ghost after_length = steps.count;
        let parsed = self.inner.parse(body, Tracked(steps));
        proof {
            lemma_steps(self.length.k(), self.inner.k(), m as nat, len as nat, input.len() as nat);
            lemma_steps(self.length.k(), self.inner.k(), m as nat, len as nat, (m + len) as nat);
        }
        match parsed {
            None => None,
            Some((n, v)) => {
                if n != len {
                    proof {
                        lemma_steps(0, self.inner.k(), 0, n as nat, len as nat);
                    }
                    return None;
                }
                proof {
                    assert(body@.take(n as int) =~= body@);
                    assert(input@.take(m as int) + body@ =~= input@.take((m + len) as int));
                }
                Some((m + len, v))
            },
        }
    }

    fn length(&self, v: &I::T, cap: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        let ghost b = self.inner.spec_serialize(v@);
        proof {
            self.length.lemma_length(self.length.spec_of_len(b.len()));
        }
        let w = self.length.width();
        let max = self.length.max();
        if cap < w {
            return None;
        }
        let room = if cap - w > max {
            max
        } else {
            cap - w
        };
        let n = match self.inner.length(v, room, Tracked(&mut *steps)) {
            Some(n) => n,
            None => {
                proof {
                    lemma_steps(self.length.k(), self.inner.k(), 0, room as nat, cap as nat);
                }
                return None;
            },
        };
        proof {
            lemma_steps(self.length.k(), self.inner.k(), w as nat, n as nat, (w + n) as nat);
        }
        Some(w + n)
    }

    fn serialize(&self, v: &I::T, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        let ghost b = self.inner.spec_serialize(v@);
        proof {
            self.length.lemma_length(self.length.spec_of_len(b.len()));
        }
        let w = self.length.width();
        let max = self.length.max();
        if pos > out.len() || out.len() - pos < w {
            return None;
        }
        let start = pos + w;
        let end = if out.len() - start > max {
            start + max
        } else {
            out.len()
        };
        let ghost before = out@;
        let ghost count = steps.count;
        let wrote = {
            let window = &mut out[..end];
            self.inner.serialize(v, window, start, Tracked(steps))
        };
        let n = match wrote {
            Some(n) => n,
            None => {
                assert(out@ =~= before);
                proof {
                    lemma_steps(self.length.k(), self.inner.k(), 0, (end - start) as nat, (out.len() - pos) as nat);
                }
                return None;
            },
        };
        assert(out@ =~= written(before, start as int, b));
        let ghost middle = out@;
        let l = self.length.of_len(n);
        proof {
            self.length.lemma_of_len(n as nat);
            self.length.lemma_length(l@);
        }
        match self.length.serialize(&l, out, pos, Tracked(steps)) {
            Some(_) => {},
            None => {
                assert(false);
                return None;
            },
        }
        proof {
            let p = self.length.spec_serialize(l@);
            assert(out@ =~= written(before, pos as int, p + b));
            lemma_steps(self.length.k(), self.inner.k(), w as nat, n as nat, (w + n) as nat);
        }
        Some(w + n)
    }
}

} // verus!
