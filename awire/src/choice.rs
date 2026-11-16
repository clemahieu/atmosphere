// SPDX-License-Identifier: MIT

//! `Choice`, the first of two alternatives that accepts, its value an `Either` naming the
//! alternative, so serialising a value picks the alternative that parsed it.
//!
//! The round trip needs the alternatives disjoint: the first refuses every serialisation of a value
//! the second can carry, whatever follows it (`disjoint`), which a `Tag` at the start of each
//! alternative gives. Then an input the second accepts is one the first refuses, and a value of the
//! second serialised and parsed again comes back as the second's.
//!
//! The parse cannot simply run the first alternative on the whole input: a refusal is charged the
//! input's length, and the choice, when its second alternative accepts, is charged only the bytes it
//! consumed. So it runs both on windows of the input, the first `w` bytes for `w` = 0, 1, 2, 4, ...
//! up to the input's length. A combinator's answer on a window that holds the bytes it consumes is
//! its answer on the whole input, by its two lemmas (`lemma_window`), so the first window on which
//! either accepts gives the choice's answer, and that window is at most twice the bytes consumed. The
//! windows tried before it sum to less than it, so the count stays linear in the bytes consumed. Each
//! window is a step of its own, besides the alternatives', which the one in `sum` and in `c` pays
//! for, so a choice of alternatives that take no steps still counts its windows.
//! A value's length and its serialisation are its alternative's.

use vstd::slice::slice_subrange;

use crate::*;

verus! {

/// A value of the first alternative or of the second.
pub enum Either<A, B> {
    First(A),
    Second(B),
}

impl<A: View, B: View> View for Either<A, B> {
    type V = Either<A::V, B::V>;

    open spec fn view(&self) -> Either<A::V, B::V> {
        match self {
            Either::First(a) => Either::First(a@),
            Either::Second(b) => Either::Second(b@),
        }
    }
}

/// `first` refuses every serialisation of a value `second` can carry, whatever follows it.
pub open spec fn disjoint<'a, A: Combinator<'a>, B: Combinator<'a>>(first: &A, second: &B) -> bool {
    forall|v: B::V, rest: Seq<u8>|
        second.valid(v) ==> (#[trigger] first.spec_parse(second.spec_serialize(v) + rest)) is None
}

/// What `c` makes of the first `w` bytes of `s` is what it makes of `s`, when it accepts a window
/// or when the window holds the bytes it consumes of `s`.
proof fn lemma_window<'a, C: Combinator<'a>>(c: &C, s: Seq<u8>, w: nat)
    requires
        c.wf(),
        w <= s.len(),
    ensures
        c.spec_parse(s.take(w as int)) matches Some((n, v)) ==> c.spec_parse(s) == Some((n, v)),
        c.spec_parse(s) matches Some((n, v)) ==> (n <= w ==> c.spec_parse(s.take(w as int)) == Some((n, v))),
{
    let t = s.take(w as int);
    c.lemma_parse_serialize(t);
    match c.spec_parse(t) {
        Some((n, v)) => {
            c.lemma_serialize_parse(v, s.skip(n as int));
            assert(t.take(n as int) + s.skip(n as int) =~= s);
        },
        None => {},
    }
    c.lemma_parse_serialize(s);
    match c.spec_parse(s) {
        Some((n, v)) => {
            if n <= w {
                c.lemma_serialize_parse(v, t.skip(n as int));
                assert(s.take(n as int) + t.skip(n as int) =~= t);
            }
        },
        None => {},
    }
}

/// Windows tried so far cost at most `2 * sum * m`; one more refused at `w <= m`, its own step
/// included, stays within the next nominal window's.
proof fn lemma_next_window(sum: nat, ka: nat, kb: nat, ca: nat, cb: nat, m: nat, w: nat, spent: int)
    requires
        ka + kb + ca + cb + 1 <= sum,
        w <= m,
        spent <= 2 * sum * m + 1 + ka * w + ca + kb * w + cb,
    ensures
        spent <= 2 * sum * (if m == 0 { 1nat } else { 2 * m }),
{
    if m == 0 {
        assert(ka * w == 0 && kb * w == 0) by (nonlinear_arith)
            requires
                w == 0,
        ;
    } else {
        assert(1 + ka * w + ca + kb * w + cb <= sum * m) by (nonlinear_arith)
            requires
                ka + kb + ca + cb + 1 <= sum,
                w <= m,
                1 <= m,
        ;
        assert(2 * sum * (2 * m) == 2 * (2 * sum * m)) by (nonlinear_arith);
        assert(sum * m <= 2 * sum * m) by (nonlinear_arith);
    }
}

/// An acceptance of `n` bytes on a window `w <= m <= 2 * n` costs at most `8 * sum * n` beyond the
/// constants.
proof fn lemma_accept(sum: nat, ka: nat, kb: nat, m: nat, w: nat, n: nat)
    requires
        ka + kb <= sum,
        w <= m,
        m <= 2 * n,
    ensures
        2 * sum * m + ka * w + kb * n <= 8 * sum * n,
{
    assert(2 * sum * m + ka * w + kb * n <= 8 * sum * n) by (nonlinear_arith)
        requires
            ka + kb <= sum,
            w <= m,
            m <= 2 * n,
    ;
}

/// A refusal on the window `w == len` with `m <= 2 * len` costs at most `8 * sum * len` beyond the
/// constants.
proof fn lemma_refuse(sum: nat, ka: nat, kb: nat, m: nat, len: nat)
    requires
        ka + kb <= sum,
        m <= 2 * len,
    ensures
        2 * sum * m + ka * len + kb * len <= 8 * sum * len,
{
    assert(2 * sum * m + ka * len + kb * len <= 8 * sum * len) by (nonlinear_arith)
        requires
            ka + kb <= sum,
            m <= 2 * len,
    ;
}

/// An alternative's `ka * n` is within the choice's `8 * sum * n`.
proof fn lemma_alternative(sum: nat, ka: nat, n: nat)
    requires
        ka <= sum,
    ensures
        ka * n <= 8 * sum * n,
{
    assert(ka * n <= 8 * sum * n) by (nonlinear_arith)
        requires
            ka <= sum,
    ;
}

/// The first of `first` and `second` that accepts.
pub struct Choice<A, B> {
    pub first: A,
    pub second: B,
}

impl<'a, A: Combinator<'a>, B: Combinator<'a>> Choice<A, B> {
    /// The sum of the alternatives' constants and the window's own step, of which the choice's `k`
    /// is a multiple.
    pub open spec fn sum(&self) -> nat {
        self.first.k() + self.second.k() + self.first.c() + self.second.c() + 1
    }
}

impl<'a, A: Combinator<'a>, B: Combinator<'a>> Combinator<'a> for Choice<A, B> {
    type V = Either<A::V, B::V>;

    type T = Either<A::T, B::T>;

    open spec fn wf(&self) -> bool {
        &&& self.first.wf()
        &&& self.second.wf()
        &&& disjoint(&self.first, &self.second)
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, Either<A::V, B::V>)> {
        match self.first.spec_parse(s) {
            Some((n, v)) => Some((n, Either::First(v))),
            None => match self.second.spec_parse(s) {
                Some((n, v)) => Some((n, Either::Second(v))),
                None => None,
            },
        }
    }

    open spec fn spec_serialize(&self, v: Either<A::V, B::V>) -> Seq<u8> {
        match v {
            Either::First(a) => self.first.spec_serialize(a),
            Either::Second(b) => self.second.spec_serialize(b),
        }
    }

    open spec fn valid(&self, v: Either<A::V, B::V>) -> bool {
        match v {
            Either::First(a) => self.first.valid(a),
            Either::Second(b) => self.second.valid(b),
        }
    }

    open spec fn k(&self) -> nat {
        8 * self.sum()
    }

    open spec fn c(&self) -> nat {
        self.first.c() + self.second.c() + 1
    }

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        self.first.lemma_parse_serialize(s);
        self.second.lemma_parse_serialize(s);
    }

    proof fn lemma_serialize_parse(&self, v: Either<A::V, B::V>, rest: Seq<u8>) {
        match v {
            Either::First(a) => {
                self.first.lemma_serialize_parse(a, rest);
            },
            Either::Second(b) => {
                self.second.lemma_serialize_parse(b, rest);
                assert(self.first.spec_parse(self.second.spec_serialize(b) + rest) is None);
            },
        }
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, Either<A::T, B::T>)>) {
        let ghost s = input@;
        let ghost count = steps.count;
        let ghost sum = self.sum();
        let ghost mut m: nat = 0;
        let mut w: usize = 0;
        loop
            invariant
                self.wf(),
                s == input@,
                sum == self.sum(),
                count == old(steps).count,
                w <= input.len(),
                m <= input.len() ==> w == m,
                m > input.len() ==> w == input.len(),
                m <= 2 * input.len(),
                self.first.spec_parse(s) matches Some((n, _)) ==> m <= 2 * n,
                self.second.spec_parse(s) matches Some((n, _)) ==> m <= 2 * n,
                steps.count <= count + 2 * sum * m,
            decreases input.len() - w,
        {
            proof {
                steps.step();
            }
            let window = slice_subrange(input, 0, w);
            assert(window@ =~= s.take(w as int));
            proof {
                lemma_window(&self.first, s, w as nat);
                lemma_window(&self.second, s, w as nat);
            }
            match self.first.parse(window, Tracked(steps)) {
                Some((n, a)) => {
                    proof {
                        assert(s.take(w as int).take(n as int) =~= s.take(n as int));
                        lemma_accept(sum, 0, self.first.k(), m, 0, n as nat);
                    }
                    return Some((n, Either::First(a)));
                },
                None => {},
            }
            match self.second.parse(window, Tracked(steps)) {
                Some((n, b)) => {
                    proof {
                        assert(s.take(w as int).take(n as int) =~= s.take(n as int));
                        self.second.lemma_parse_serialize(s);
                        assert(self.second.spec_serialize(b@) + s.skip(n as int) =~= s);
                        assert(self.first.spec_parse(self.second.spec_serialize(b@) + s.skip(n as int)) is None);
                        lemma_accept(sum, self.first.k(), self.second.k(), m, w as nat, n as nat);
                    }
                    return Some((n, Either::Second(b)));
                },
                None => {},
            }
            if w == input.len() {
                proof {
                    lemma_refuse(sum, self.first.k(), self.second.k(), m, w as nat);
                    assert(s.take(w as int) =~= s);
                }
                return None;
            }
            proof {
                lemma_next_window(sum, self.first.k(), self.second.k(), self.first.c(), self.second.c(), m, w as nat, steps.count - count);
                m = if m == 0 { 1nat } else { 2 * m };
            }
            w = if w == 0 {
                1
            } else if input.len() - w < w {
                input.len()
            } else {
                2 * w
            };
        }
    }

    fn length(&self, v: &Either<A::T, B::T>, cap: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        match v {
            Either::First(a) => {
                let r = self.first.length(a, cap, Tracked(steps));
                proof {
                    match r {
                        Some(n) => lemma_alternative(self.sum(), self.first.k(), n as nat),
                        None => lemma_alternative(self.sum(), self.first.k(), cap as nat),
                    }
                }
                r
            },
            Either::Second(b) => {
                let r = self.second.length(b, cap, Tracked(steps));
                proof {
                    match r {
                        Some(n) => lemma_alternative(self.sum(), self.second.k(), n as nat),
                        None => lemma_alternative(self.sum(), self.second.k(), cap as nat),
                    }
                }
                r
            },
        }
    }

    fn serialize(&self, v: &Either<A::T, B::T>, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        let ghost left = room(out@.len() as int, pos as int);
        match v {
            Either::First(a) => {
                let r = self.first.serialize(a, out, pos, Tracked(steps));
                proof {
                    match r {
                        Some(n) => lemma_alternative(self.sum(), self.first.k(), n as nat),
                        None => lemma_alternative(self.sum(), self.first.k(), left),
                    }
                }
                r
            },
            Either::Second(b) => {
                let r = self.second.serialize(b, out, pos, Tracked(steps));
                proof {
                    match r {
                        Some(n) => lemma_alternative(self.sum(), self.second.k(), n as nat),
                        None => lemma_alternative(self.sum(), self.second.k(), left),
                    }
                }
                r
            },
        }
    }
}

} // verus!
