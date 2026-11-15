// SPDX-License-Identifier: MIT

//! Bounded repetition: `Count`, a combinator exactly a count of times, and `Bounded`, a combinator at
//! most a bound of times filling exactly the bytes a `Length` counts in front of them. Their value is
//! `Elements`, at most a capacity `N` of values held in place, `N` fixed when the format is written,
//! so nothing allocates (design/network-stack-proven-at-tier-1/, rules 2 and 5).
//!
//! The count and the bound are parameters, each at most the capacity. A region holding more elements
//! than the bound is refused, as soon as the element past the bound would start. `Bounded` is
//! delimited by a length because a repetition that runs to the end of its input does not parse back
//! to itself when bytes follow it.
//!
//! Each requires its element to consume at least one byte whenever it accepts, so a repetition runs
//! at most one iteration per byte it reads, and its step constants are its element's and its
//! length's, whatever the count or the bound. A parse reads the elements one after another. A length
//! asks each element's within the room left. A serialisation asks every element's length within the
//! room before it writes any, as `Pair` does, so a refusal leaves the buffer as it was; the elements
//! are then written and cannot refuse. That counts each element's bytes twice, so `k` is twice the
//! steps an element costs per byte, its own `k` and `c` and the iteration's one step.

use crate::*;
use vstd::slice::slice_subrange;

verus! {

/// At most `N` values in order, held in place: a repetition's value.
pub struct Elements<T, const N: usize> {
    items: [Option<T>; N],
    count: usize,
}

impl<T, const N: usize> Elements<T, N> {
    /// The first `count` places hold a value.
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.count <= N
        &&& forall|i: int| 0 <= i < self.count ==> (#[trigger] self.items@[i]) is Some
    }
}

impl<T: View, const N: usize> View for Elements<T, N> {
    type V = Seq<T::V>;

    closed spec fn view(&self) -> Seq<T::V> {
        Seq::new(self.count as nat, |i: int| self.items@[i]->0@)
    }
}

impl<T: Copy + View, const N: usize> Elements<T, N> {
    /// No values.
    pub fn new() -> (r: Self)
        ensures
            r@ == Seq::<T::V>::empty(),
    {
        let r = Elements { items: [None; N], count: 0 };
        assert(r@ =~= Seq::<T::V>::empty());
        r
    }

    /// The number of values, at most the capacity.
    pub fn len(&self) -> (n: usize)
        ensures
            n == self@.len(),
            n <= N,
    {
        proof {
            use_type_invariant(self);
        }
        self.count
    }

    /// The value at `i`.
    pub fn get(&self, i: usize) -> (t: T)
        requires
            i < self@.len(),
        ensures
            t@ == self@[i as int],
    {
        proof {
            use_type_invariant(self);
        }
        self.items[i].unwrap()
    }

    /// Adds `t` after the values held, when there is room for it.
    pub fn push(&mut self, t: T)
        requires
            old(self)@.len() < N,
        ensures
            final(self)@ == old(self)@.push(t@),
    {
        proof {
            use_type_invariant(&*self);
        }
        let count = self.count;
        let mut items = self.items;
        items[count] = Some(t);
        *self = Elements { items, count: count + 1 };
        assert(self@ =~= old(self)@.push(t@));
    }
}

/// Every parse of `inner` that accepts consumes at least one byte.
pub open spec fn consumes<'a, I: Combinator<'a>>(inner: &I) -> bool {
    forall|s: Seq<u8>| #[trigger] inner.spec_parse(s) is Some ==> (inner.spec_parse(s)->0).0 > 0
}

/// The steps an element costs per byte it reads or writes: its own per byte, its constant and the
/// iteration's one step, each at most once per byte since it reads or writes at least one.
pub open spec fn per_byte<'a, I: Combinator<'a>>(inner: &I) -> nat {
    inner.k() + inner.c() + 1
}

/// Every value of `vs` is one `inner` can carry.
pub open spec fn all_valid<'a, I: Combinator<'a>>(inner: &I, vs: Seq<I::V>) -> bool {
    forall|i: int| 0 <= i < vs.len() ==> inner.valid(#[trigger] vs[i])
}

/// The serialisations of the values of `vs`, one after another.
pub open spec fn serialize_all<'a, I: Combinator<'a>>(inner: &I, vs: Seq<I::V>) -> Seq<u8>
    decreases vs.len(),
{
    if vs.len() == 0 {
        Seq::empty()
    } else {
        inner.spec_serialize(vs[0]) + serialize_all(inner, vs.skip(1))
    }
}

/// Exactly `n` values of `inner`, one after another from the start of `s`: the bytes they consume
/// and the values.
pub open spec fn parse_count<'a, I: Combinator<'a>>(inner: &I, s: Seq<u8>, n: nat) -> Option<(nat, Seq<I::V>)>
    decreases n,
{
    if n == 0 {
        Some((0, Seq::empty()))
    } else {
        match inner.spec_parse(s) {
            None => None,
            Some((m, v)) => match parse_count(inner, s.skip(m as int), (n - 1) as nat) {
                None => None,
                Some((k, vs)) => Some((m + k, seq![v] + vs)),
            },
        }
    }
}

/// Values of `inner`, one after another, filling all of `s`; none when one refuses or consumes no
/// byte.
pub open spec fn parse_fill<'a, I: Combinator<'a>>(inner: &I, s: Seq<u8>) -> Option<Seq<I::V>>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(Seq::empty())
    } else {
        match inner.spec_parse(s) {
            None => None,
            Some((m, v)) => if 0 < m <= s.len() {
                match parse_fill(inner, s.skip(m as int)) {
                    None => None,
                    Some(vs) => Some(seq![v] + vs),
                }
            } else {
                None
            },
        }
    }
}

/// A value an element accepts serialises to at least one byte.
proof fn lemma_nonempty<'a, I: Combinator<'a>>(inner: &I, v: I::V)
    requires
        inner.wf(),
        consumes(inner),
        inner.valid(v),
    ensures
        inner.spec_serialize(v).len() > 0,
{
    inner.lemma_serialize_parse(v, Seq::empty());
    assert(inner.spec_serialize(v) + Seq::<u8>::empty() =~= inner.spec_serialize(v));
}

/// The serialisation of `vs` is that of its first `i` values, then that of the rest.
proof fn lemma_serialize_split<'a, I: Combinator<'a>>(inner: &I, vs: Seq<I::V>, i: int)
    requires
        0 <= i <= vs.len(),
    ensures
        serialize_all(inner, vs) == serialize_all(inner, vs.take(i)) + serialize_all(inner, vs.skip(i)),
    decreases i,
{
    if i == 0 {
        assert(vs.skip(0) =~= vs);
        assert(serialize_all(inner, vs.take(0)) == Seq::<u8>::empty());
        assert(Seq::<u8>::empty() + serialize_all(inner, vs) =~= serialize_all(inner, vs));
    } else {
        let tail = vs.skip(1);
        lemma_serialize_split(inner, tail, i - 1);
        assert(vs.take(i).skip(1) =~= tail.take(i - 1));
        assert(tail.skip(i - 1) =~= vs.skip(i));
        assert(vs.take(i)[0] == vs[0]);
        let a = inner.spec_serialize(vs[0]);
        assert(a + (serialize_all(inner, tail.take(i - 1)) + serialize_all(inner, vs.skip(i)))
            =~= a + serialize_all(inner, tail.take(i - 1)) + serialize_all(inner, vs.skip(i)));
    }
}

/// The serialisation of the first `i + 1` values of `vs` is that of the first `i`, then the value at
/// `i`'s; and the serialisation of all of `vs` is at least that long.
proof fn lemma_serialize_next<'a, I: Combinator<'a>>(inner: &I, vs: Seq<I::V>, i: int)
    requires
        0 <= i < vs.len(),
    ensures
        serialize_all(inner, vs.take(i + 1)) == serialize_all(inner, vs.take(i)) + inner.spec_serialize(vs[i]),
        serialize_all(inner, vs).len() >= serialize_all(inner, vs.take(i + 1)).len(),
{
    let front = vs.take(i + 1);
    lemma_serialize_split(inner, front, i);
    assert(front.take(i) =~= vs.take(i));
    let last = front.skip(i);
    assert(last.len() == 1);
    assert(last[0] == vs[i]);
    assert(last.skip(1) =~= Seq::<I::V>::empty());
    assert(serialize_all(inner, last.skip(1)) == Seq::<u8>::empty());
    assert(serialize_all(inner, last) =~= inner.spec_serialize(vs[i]));
    lemma_serialize_split(inner, vs, i + 1);
}

/// A count parse consumes at most its input, and gives exactly `n` values `inner` can carry, which
/// serialise to exactly the bytes consumed.
proof fn lemma_count_parse<'a, I: Combinator<'a>>(inner: &I, s: Seq<u8>, n: nat)
    requires
        inner.wf(),
    ensures
        parse_count(inner, s, n) matches Some((m, vs)) ==> {
            &&& m <= s.len()
            &&& vs.len() == n
            &&& all_valid(inner, vs)
            &&& serialize_all(inner, vs) == s.take(m as int)
        },
    decreases n,
{
    if n > 0 {
        inner.lemma_parse_serialize(s);
        if let Some((m, v)) = inner.spec_parse(s) {
            let rest = s.skip(m as int);
            lemma_count_parse(inner, rest, (n - 1) as nat);
            if let Some((k, ws)) = parse_count(inner, rest, (n - 1) as nat) {
                let vs = seq![v] + ws;
                assert(vs[0] == v);
                assert(vs.skip(1) =~= ws);
                assert forall|i: int| 0 <= i < vs.len() implies inner.valid(#[trigger] vs[i]) by {
                    if i > 0 {
                        assert(vs[i] == ws[i - 1]);
                    }
                };
                assert(s.take(m as int) + rest.take(k as int) =~= s.take((m + k) as int));
            }
        }
    } else {
        assert(s.take(0) =~= Seq::<u8>::empty());
    }
}

/// `n` values `inner` can carry, serialised, parse back to themselves as a count of `n`, whatever
/// follows them.
proof fn lemma_count_serialize<'a, I: Combinator<'a>>(inner: &I, vs: Seq<I::V>, rest: Seq<u8>)
    requires
        inner.wf(),
        all_valid(inner, vs),
    ensures
        parse_count(inner, serialize_all(inner, vs) + rest, vs.len()) == Some((serialize_all(inner, vs).len(), vs)),
    decreases vs.len(),
{
    if vs.len() == 0 {
        assert(serialize_all(inner, vs) + rest =~= rest);
        assert(vs =~= Seq::<I::V>::empty());
    } else {
        let a = inner.spec_serialize(vs[0]);
        let tail = vs.skip(1);
        let b = serialize_all(inner, tail);
        assert(inner.valid(vs[0]));
        assert forall|i: int| 0 <= i < tail.len() implies inner.valid(#[trigger] tail[i]) by {
            assert(tail[i] == vs[i + 1]);
        };
        assert(a + b + rest =~= a + (b + rest));
        inner.lemma_serialize_parse(vs[0], b + rest);
        assert((a + (b + rest)).skip(a.len() as int) =~= b + rest);
        lemma_count_serialize(inner, tail, rest);
        assert(seq![vs[0]] + tail =~= vs);
    }
}

/// A fill parse gives values `inner` can carry, which serialise to exactly the bytes filled.
proof fn lemma_fill_parse<'a, I: Combinator<'a>>(inner: &I, s: Seq<u8>)
    requires
        inner.wf(),
    ensures
        parse_fill(inner, s) matches Some(vs) ==> all_valid(inner, vs) && serialize_all(inner, vs) == s,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(serialize_all(inner, Seq::<I::V>::empty()) =~= s);
    } else {
        inner.lemma_parse_serialize(s);
        if let Some((m, v)) = inner.spec_parse(s) {
            if 0 < m <= s.len() {
                let rest = s.skip(m as int);
                lemma_fill_parse(inner, rest);
                if let Some(ws) = parse_fill(inner, rest) {
                    let vs = seq![v] + ws;
                    assert(vs[0] == v);
                    assert(vs.skip(1) =~= ws);
                    assert forall|i: int| 0 <= i < vs.len() implies inner.valid(#[trigger] vs[i]) by {
                        if i > 0 {
                            assert(vs[i] == ws[i - 1]);
                        }
                    };
                    assert(s.take(m as int) + rest =~= s);
                }
            }
        }
    }
}

/// Values `inner` can carry, serialised, fill back to themselves.
proof fn lemma_fill_serialize<'a, I: Combinator<'a>>(inner: &I, vs: Seq<I::V>)
    requires
        inner.wf(),
        consumes(inner),
        all_valid(inner, vs),
    ensures
        parse_fill(inner, serialize_all(inner, vs)) == Some(vs),
    decreases vs.len(),
{
    if vs.len() == 0 {
        assert(vs =~= Seq::<I::V>::empty());
    } else {
        let a = inner.spec_serialize(vs[0]);
        let tail = vs.skip(1);
        let b = serialize_all(inner, tail);
        let s = a + b;
        assert(inner.valid(vs[0]));
        assert forall|i: int| 0 <= i < tail.len() implies inner.valid(#[trigger] tail[i]) by {
            assert(tail[i] == vs[i + 1]);
        };
        inner.lemma_serialize_parse(vs[0], b);
        assert(inner.spec_parse(s) == Some((a.len(), vs[0])));
        assert(a.len() > 0);
        assert(s.skip(a.len() as int) =~= b);
        lemma_fill_serialize(inner, tail);
        assert(seq![vs[0]] + tail =~= vs);
    }
}

/// A fill parse of a nonempty region gives at least one value, or refuses.
proof fn lemma_fill_nonempty<'a, I: Combinator<'a>>(inner: &I, s: Seq<u8>)
    requires
        s.len() > 0,
    ensures
        parse_fill(inner, s) matches Some(vs) ==> vs.len() > 0,
{
}

/// The steps of an element added to those of the elements before it.
proof fn lemma_add(k: nat, c: nat, pos: nat, m: nat, i: nat)
    ensures
        k * pos + (c + 1) * i + k * m + c + 1 == k * (pos + m) + (c + 1) * (i + 1),
{
    assert(k * pos + k * m == k * (pos + m)) by (nonlinear_arith);
    assert((c + 1) * i + c + 1 == (c + 1) * (i + 1)) by (nonlinear_arith);
}

/// `i` elements of at least a byte each in `n` bytes cost at most `per` steps a byte, `per` being
/// `k + c + 1`; and with the bytes left, `rest`, at `k` each besides, at most `per` a byte of any `z`
/// holding both.
proof fn lemma_linear(k: nat, c: nat, n: nat, i: nat, rest: nat, z: nat)
    requires
        i <= n,
        n + rest <= z,
    ensures
        k * n + (c + 1) * i <= (k + c + 1) * n,
        k * n + (c + 1) * i + k * rest <= (k + c + 1) * z,
{
    assert(k * n + (c + 1) * i <= (k + c + 1) * n) by (nonlinear_arith)
        requires
            i <= n,
    ;
    assert(k * n + (c + 1) * i + k * rest <= (k + c + 1) * z) by (nonlinear_arith)
        requires
            i <= n,
            n + rest <= z,
    ;
}

/// `x` steps a byte on `n` bytes are at most `y` a byte when `x` is at most `y`, and on `m` bytes
/// when `n` is at most `m`.
proof fn lemma_more(x: nat, y: nat, n: nat, m: nat)
    requires
        x <= y,
        n <= m,
    ensures
        x * n <= y * m,
{
    assert(x * n <= y * m) by (nonlinear_arith)
        requires
            x <= y,
            n <= m,
    ;
}

/// A length's steps on its `x` bytes and the elements' on `y`, both within `z`, are within
/// `Bounded`'s `k` on `z`.
proof fn lemma_bounded(a: nat, p: nat, x: nat, y: nat, z: nat)
    requires
        x <= z,
        y <= z,
    ensures
        a * x + p * y <= (a + 2 * p) * z,
{
    assert(a * x + p * y <= (a + 2 * p) * z) by (nonlinear_arith)
        requires
            x <= z,
            y <= z,
    ;
}

/// The length of the serialisation of the values of `v`, exactly when each is one `inner` can carry
/// and the length is at most `cap`; at most `per_byte` steps a byte of it, or of `cap` and `inner`'s
/// constant and a step when it refused.
fn length_all<'a, I: Combinator<'a>, const N: usize>(inner: &I, v: &Elements<I::T, N>, cap: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>)
    where
        I::T: Copy,
    requires
        inner.wf(),
        consumes(inner),
    ensures
        match r {
            None => {
                &&& !(all_valid(inner, v@) && serialize_all(inner, v@).len() <= cap)
                &&& final(steps).count <= old(steps).count + per_byte(inner) * cap + inner.c() + 1
            },
            Some(n) => {
                &&& all_valid(inner, v@)
                &&& n == serialize_all(inner, v@).len()
                &&& n <= cap
                &&& v@.len() <= n
                &&& final(steps).count <= old(steps).count + per_byte(inner) * n
            },
        },
{
    let ghost vs = v@;
    let ghost start = steps.count;
    let count = v.len();
    let mut i: usize = 0;
    let mut total: usize = 0;
    while i < count
        invariant
            inner.wf(),
            consumes(inner),
            vs == v@,
            count == vs.len(),
            i <= count,
            total <= cap,
            i <= total,
            total == serialize_all(inner, vs.take(i as int)).len(),
            all_valid(inner, vs.take(i as int)),
            start == old(steps).count,
            steps.count <= start + inner.k() * total + (inner.c() + 1) * i,
        decreases count - i,
    {
        let t = v.get(i);
        let n = match inner.length(&t, cap - total, Tracked(&mut *steps)) {
            Some(n) => n,
            None => {
                proof {
                    lemma_serialize_next(inner, vs, i as int);
                    lemma_linear(inner.k(), inner.c(), total as nat, i as nat, (cap - total) as nat, cap as nat);
                }
                return None;
            },
        };
        proof {
            steps.step();
            lemma_nonempty(inner, vs[i as int]);
            lemma_serialize_next(inner, vs, i as int);
            lemma_add(inner.k(), inner.c(), total as nat, n as nat, i as nat);
            assert forall|j: int| 0 <= j < i + 1 implies inner.valid(#[trigger] vs.take(i + 1)[j]) by {
                if j < i {
                    assert(vs.take(i + 1)[j] == vs.take(i as int)[j]);
                }
            };
        }
        total = total + n;
        i = i + 1;
    }
    proof {
        assert(vs.take(i as int) =~= vs);
        lemma_linear(inner.k(), inner.c(), total as nat, i as nat, 0, total as nat);
    }
    Some(total)
}

/// Writes the serialisation of the values of `v` into `out` from `pos`, every other byte as it was,
/// in at most `per_byte` steps a byte.
fn write_all<'a, I: Combinator<'a>, const N: usize>(inner: &I, v: &Elements<I::T, N>, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>)
    where
        I::T: Copy,
    requires
        inner.wf(),
        consumes(inner),
        all_valid(inner, v@),
        pos + serialize_all(inner, v@).len() <= old(out)@.len(),
    ensures
        final(out)@ == written(old(out)@, pos as int, serialize_all(inner, v@)),
        final(steps).count <= old(steps).count + per_byte(inner) * serialize_all(inner, v@).len(),
{
    let ghost vs = v@;
    let ghost before = out@;
    let ghost start = steps.count;
    let ghost whole = serialize_all(inner, vs);
    let count = v.len();
    let mut i: usize = 0;
    let mut at: usize = pos;
    proof {
        assert(written(before, pos as int, serialize_all(inner, vs.take(0))) =~= before);
    }
    while i < count
        invariant
            inner.wf(),
            consumes(inner),
            vs == v@,
            count == vs.len(),
            all_valid(inner, vs),
            whole == serialize_all(inner, vs),
            pos + whole.len() <= before.len(),
            before == old(out)@,
            out@.len() == before.len(),
            out.len() == before.len(),
            start == old(steps).count,
            i <= count,
            pos <= at,
            at - pos == serialize_all(inner, vs.take(i as int)).len(),
            at <= pos + whole.len(),
            i <= at - pos,
            out@ == written(before, pos as int, serialize_all(inner, vs.take(i as int))),
            steps.count <= start + inner.k() * (at - pos) + (inner.c() + 1) * i,
        decreases count - i,
    {
        let t = v.get(i);
        proof {
            lemma_serialize_next(inner, vs, i as int);
            lemma_nonempty(inner, vs[i as int]);
        }
        let ghost done = serialize_all(inner, vs.take(i as int));
        let ghost middle = out@;
        let n = inner.serialize(&t, out, at, Tracked(&mut *steps)).unwrap();
        proof {
            steps.step();
            lemma_add(inner.k(), inner.c(), (at - pos) as nat, n as nat, i as nat);
            assert(out@ =~= written(before, pos as int, done + inner.spec_serialize(vs[i as int])));
        }
        at = at + n;
        i = i + 1;
    }
    proof {
        assert(vs.take(i as int) =~= vs);
        lemma_linear(inner.k(), inner.c(), (at - pos) as nat, i as nat, 0, (at - pos) as nat);
    }
}

/// `inner`, exactly `count` times, `count` at most the capacity `N`.
pub struct Count<I, const N: usize> {
    pub inner: I,
    pub count: usize,
}

impl<'a, I: Combinator<'a>, const N: usize> Combinator<'a> for Count<I, N> where I::T: Copy {
    type V = Seq<I::V>;

    type T = Elements<I::T, N>;

    open spec fn wf(&self) -> bool {
        &&& self.inner.wf()
        &&& consumes(&self.inner)
        &&& self.count <= N
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, Seq<I::V>)> {
        parse_count(&self.inner, s, self.count as nat)
    }

    open spec fn spec_serialize(&self, v: Seq<I::V>) -> Seq<u8> {
        serialize_all(&self.inner, v)
    }

    open spec fn valid(&self, v: Seq<I::V>) -> bool {
        &&& v.len() == self.count
        &&& all_valid(&self.inner, v)
    }

    open spec fn k(&self) -> nat {
        2 * per_byte(&self.inner)
    }

    open spec fn c(&self) -> nat {
        self.inner.c() + 1
    }

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        lemma_count_parse(&self.inner, s, self.count as nat);
    }

    proof fn lemma_serialize_parse(&self, v: Seq<I::V>, rest: Seq<u8>) {
        lemma_count_serialize(&self.inner, v, rest);
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, Elements<I::T, N>)>) {
        let ghost s = input@;
        let ghost start = steps.count;
        let ghost whole = parse_count(&self.inner, s, self.count as nat);
        let ghost mut vs: Seq<I::V> = Seq::empty();
        let mut items: [Option<I::T>; N] = [None; N];
        let mut i: usize = 0;
        let mut pos: usize = 0;
        proof {
            assert(s.skip(0) =~= s);
            assert(whole == match parse_count(&self.inner, s.skip(0), self.count as nat) {
                None => None,
                Some((k, ws)) => Some((k, vs + ws)),
            }) by {
                if let Some((k, ws)) = parse_count(&self.inner, s, self.count as nat) {
                    assert(vs + ws =~= ws);
                }
            };
        }
        while i < self.count
            invariant
                self.wf(),
                s == input@,
                whole == parse_count(&self.inner, s, self.count as nat),
                start == old(steps).count,
                i <= self.count,
                pos <= s.len(),
                i <= pos,
                vs.len() == i,
                items@.len() == N,
                forall|j: int| 0 <= j < i ==> (#[trigger] items@[j]) is Some && items@[j]->0@ == vs[j],
                whole == match parse_count(&self.inner, s.skip(pos as int), (self.count - i) as nat) {
                    None => None,
                    Some((k, ws)) => Some(((pos + k) as nat, vs + ws)),
                },
                steps.count <= start + self.inner.k() * pos + (self.inner.c() + 1) * i,
            decreases self.count - i,
        {
            let rest = slice_subrange(input, pos, input.len());
            assert(rest@ =~= s.skip(pos as int));
            let (m, t) = match self.inner.parse(rest, Tracked(&mut *steps)) {
                Some(p) => p,
                None => {
                    proof {
                        lemma_linear(self.inner.k(), self.inner.c(), pos as nat, i as nat, (s.len() - pos) as nat, s.len());
                        lemma_more(per_byte(&self.inner), self.k(), s.len(), s.len());
                    }
                    return None;
                },
            };
            proof {
                steps.step();
                lemma_add(self.inner.k(), self.inner.c(), pos as nat, m as nat, i as nat);
                assert(s.skip(pos as int).skip(m as int) =~= s.skip(pos + m));
                if let Some((k, ws)) = parse_count(&self.inner, s.skip(pos + m), (self.count - i - 1) as nat) {
                    assert(vs + (seq![t@] + ws) =~= vs.push(t@) + ws);
                }
                vs = vs.push(t@);
            }
            items[i] = Some(t);
            i = i + 1;
            pos = pos + m;
        }
        let r = Elements { items, count: i };
        proof {
            assert(r@ =~= vs);
            assert(vs + Seq::<I::V>::empty() =~= vs);
            lemma_count_parse(&self.inner, s, self.count as nat);
            lemma_linear(self.inner.k(), self.inner.c(), pos as nat, i as nat, 0, pos as nat);
            lemma_more(per_byte(&self.inner), self.k(), pos as nat, pos as nat);
        }
        Some((pos, r))
    }

    fn length(&self, v: &Elements<I::T, N>, cap: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        if v.len() != self.count {
            return None;
        }
        let r = length_all(&self.inner, v, cap, Tracked(steps));
        proof {
            match r {
                Some(n) => lemma_more(per_byte(&self.inner), self.k(), n as nat, n as nat),
                None => lemma_more(per_byte(&self.inner), self.k(), cap as nat, cap as nat),
            }
        }
        r
    }

    fn serialize(&self, v: &Elements<I::T, N>, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        if pos > out.len() || v.len() != self.count {
            return None;
        }
        let ghost start = steps.count;
        let room = out.len() - pos;
        let n = match length_all(&self.inner, v, room, Tracked(&mut *steps)) {
            Some(n) => n,
            None => {
                proof {
                    lemma_more(per_byte(&self.inner), self.k(), room as nat, room as nat);
                }
                return None;
            },
        };
        write_all(&self.inner, v, out, pos, Tracked(&mut *steps));
        proof {
            assert(per_byte(&self.inner) * n + per_byte(&self.inner) * n == self.k() * n) by (nonlinear_arith);
        }
        Some(n)
    }
}

/// `inner`, at most `bound` times, filling exactly the bytes a length read with `length` counts in
/// front of them; `bound` at most the capacity `N`.
pub struct Bounded<L, I, const N: usize> {
    pub length: L,
    pub inner: I,
    pub bound: usize,
}

impl<'a, L: Length<'a>, I: Combinator<'a>, const N: usize> Bounded<L, I, N> where I::T: Copy {
    /// A region whose values number more than the bound is refused, whatever they are.
    pub proof fn lemma_past_bound(&self, s: Seq<u8>)
        ensures
            self.length.spec_parse(s) matches Some((m, l)) ==> {
                let len = self.length.spec_len(l);
                m + len <= s.len() ==> (parse_fill(&self.inner, s.subrange(m as int, (m + len) as int)) matches Some(vs)
                    ==> (vs.len() > self.bound ==> self.spec_parse(s) is None))
            },
    {
    }
}

impl<'a, L: Length<'a>, I: Combinator<'a>, const N: usize> Combinator<'a> for Bounded<L, I, N> where I::T: Copy {
    type V = Seq<I::V>;

    type T = Elements<I::T, N>;

    open spec fn wf(&self) -> bool {
        &&& self.length.wf()
        &&& self.inner.wf()
        &&& consumes(&self.inner)
        &&& self.bound <= N
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, Seq<I::V>)> {
        match self.length.spec_parse(s) {
            None => None,
            Some((m, l)) => {
                let len = self.length.spec_len(l);
                if m + len <= s.len() {
                    match parse_fill(&self.inner, s.subrange(m as int, (m + len) as int)) {
                        Some(vs) => if vs.len() <= self.bound {
                            Some(((m + len) as nat, vs))
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

    open spec fn spec_serialize(&self, v: Seq<I::V>) -> Seq<u8> {
        let b = serialize_all(&self.inner, v);
        self.length.spec_serialize(self.length.spec_of_len(b.len())) + b
    }

    open spec fn valid(&self, v: Seq<I::V>) -> bool {
        &&& v.len() <= self.bound
        &&& all_valid(&self.inner, v)
        &&& serialize_all(&self.inner, v).len() <= self.length.spec_max()
    }

    open spec fn k(&self) -> nat {
        self.length.k() + 2 * per_byte(&self.inner)
    }

    open spec fn c(&self) -> nat {
        self.length.c() + self.inner.c() + 1
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
                    lemma_fill_parse(&self.inner, body);
                    if let Some(vs) = parse_fill(&self.inner, body) {
                        assert(s.take(m as int) + body =~= s.take((m + len) as int));
                    }
                }
            },
        }
    }

    proof fn lemma_serialize_parse(&self, v: Seq<I::V>, rest: Seq<u8>) {
        let b = serialize_all(&self.inner, v);
        let l = self.length.spec_of_len(b.len());
        self.length.lemma_of_len(b.len());
        let p = self.length.spec_serialize(l);
        self.length.lemma_serialize_parse(l, b + rest);
        assert(p + b + rest =~= p + (b + rest));
        let body = (p + b + rest).subrange(p.len() as int, (p.len() + b.len()) as int);
        assert(body =~= b);
        lemma_fill_serialize(&self.inner, v);
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, Elements<I::T, N>)>) {
        let ghost s = input@;
        let ghost start = steps.count;
        let (m, l) = match self.length.parse(input, Tracked(&mut *steps)) {
            Some(p) => p,
            None => {
                proof {
                    lemma_more(self.length.k(), self.k(), s.len(), s.len());
                }
                return None;
            },
        };
        proof {
            self.length.lemma_length(l@);
            lemma_more(self.length.k(), self.k(), m as nat, s.len());
        }
        let len = self.length.len_of(&l);
        if input.len() - m < len {
            return None;
        }
        let region = slice_subrange(input, m, m + len);
        let ghost body = region@;
        assert(body =~= s.subrange(m as int, (m + len) as int));
        let ghost after_length = steps.count;
        let ghost whole = parse_fill(&self.inner, body);
        let ghost mut vs: Seq<I::V> = Seq::empty();
        let mut items: [Option<I::T>; N] = [None; N];
        let mut i: usize = 0;
        let mut pos: usize = 0;
        proof {
            assert(body.skip(0) =~= body);
            if let Some(ws) = whole {
                assert(vs + ws =~= ws);
            }
        }
        while pos < region.len()
            invariant
                self.wf(),
                body == region@,
                s == input@,
                start == old(steps).count,
                self.length.spec_parse(s) == Some((m as nat, l@)),
                len == self.length.spec_len(l@),
                m + len <= s.len(),
                body == s.subrange(m as int, (m + len) as int),
                after_length <= start + self.length.k() * m + self.length.c(),
                whole == parse_fill(&self.inner, body),
                i <= self.bound,
                pos <= body.len(),
                i <= pos,
                vs.len() == i,
                items@.len() == N,
                forall|j: int| 0 <= j < i ==> (#[trigger] items@[j]) is Some && items@[j]->0@ == vs[j],
                whole == match parse_fill(&self.inner, body.skip(pos as int)) {
                    None => None,
                    Some(ws) => Some(vs + ws),
                },
                steps.count <= after_length + self.inner.k() * pos + (self.inner.c() + 1) * i,
            decreases body.len() - pos,
        {
            let rest = slice_subrange(region, pos, region.len());
            assert(rest@ =~= body.skip(pos as int));
            if i == self.bound {
                proof {
                    lemma_fill_nonempty(&self.inner, rest@);
                    lemma_linear(self.inner.k(), self.inner.c(), pos as nat, i as nat, 0, pos as nat);
                    lemma_bounded(self.length.k(), per_byte(&self.inner), m as nat, pos as nat, s.len());
                }
                return None;
            }
            let (n, t) = match self.inner.parse(rest, Tracked(&mut *steps)) {
                Some(p) => p,
                None => {
                    proof {
                        lemma_linear(self.inner.k(), self.inner.c(), pos as nat, i as nat, (body.len() - pos) as nat, body.len());
                        lemma_bounded(self.length.k(), per_byte(&self.inner), m as nat, body.len(), s.len());
                    }
                    return None;
                },
            };
            proof {
                steps.step();
                lemma_add(self.inner.k(), self.inner.c(), pos as nat, n as nat, i as nat);
                assert(rest@.skip(n as int) =~= body.skip(pos + n));
                if let Some(ws) = parse_fill(&self.inner, body.skip(pos + n)) {
                    assert(vs + (seq![t@] + ws) =~= vs.push(t@) + ws);
                }
                vs = vs.push(t@);
            }
            items[i] = Some(t);
            i = i + 1;
            pos = pos + n;
        }
        let r = Elements { items, count: i };
        proof {
            assert(r@ =~= vs);
            assert(body.skip(pos as int) =~= Seq::<u8>::empty());
            assert(vs + Seq::<I::V>::empty() =~= vs);
            self.lemma_parse_serialize(s);
            lemma_linear(self.inner.k(), self.inner.c(), pos as nat, i as nat, 0, pos as nat);
            lemma_bounded(self.length.k(), per_byte(&self.inner), m as nat, len as nat, (m + len) as nat);
        }
        Some((m + len, r))
    }

    fn length(&self, v: &Elements<I::T, N>, cap: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        let ghost b = serialize_all(&self.inner, v@);
        proof {
            self.length.lemma_length(self.length.spec_of_len(b.len()));
        }
        let w = self.length.width();
        let max = self.length.max();
        if v.len() > self.bound || cap < w {
            return None;
        }
        let room = if cap - w > max {
            max
        } else {
            cap - w
        };
        let n = match length_all(&self.inner, v, room, Tracked(&mut *steps)) {
            Some(n) => n,
            None => {
                proof {
                    lemma_more(per_byte(&self.inner), self.k(), room as nat, cap as nat);
                }
                return None;
            },
        };
        proof {
            lemma_more(per_byte(&self.inner), self.k(), n as nat, (w + n) as nat);
        }
        Some(w + n)
    }

    fn serialize(&self, v: &Elements<I::T, N>, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        let ghost b = serialize_all(&self.inner, v@);
        proof {
            self.length.lemma_length(self.length.spec_of_len(b.len()));
        }
        let w = self.length.width();
        let max = self.length.max();
        if pos > out.len() || out.len() - pos < w || v.len() > self.bound {
            return None;
        }
        let room = if out.len() - pos - w > max {
            max
        } else {
            out.len() - pos - w
        };
        let ghost before = out@;
        let ghost start = steps.count;
        let n = match length_all(&self.inner, v, room, Tracked(&mut *steps)) {
            Some(n) => n,
            None => {
                proof {
                    lemma_more(per_byte(&self.inner), self.k(), room as nat, (out.len() - pos) as nat);
                }
                return None;
            },
        };
        let l = self.length.of_len(n);
        proof {
            self.length.lemma_of_len(n as nat);
            self.length.lemma_length(l@);
        }
        let ghost after_count = steps.count;
        match self.length.serialize(&l, out, pos, Tracked(&mut *steps)) {
            Some(_) => {},
            None => {
                assert(false);
                return None;
            },
        }
        let ghost middle = out@;
        write_all(&self.inner, v, out, pos + w, Tracked(&mut *steps));
        proof {
            let p = self.length.spec_serialize(l@);
            assert(out@ =~= written(before, pos as int, p + b));
            assert(per_byte(&self.inner) * n + per_byte(&self.inner) * n == (2 * per_byte(&self.inner)) * n) by (nonlinear_arith);
            lemma_more(self.length.k(), self.k(), w as nat, w as nat);
            lemma_more(2 * per_byte(&self.inner), self.k(), n as nat, n as nat);
            assert(self.k() * w + self.k() * n == self.k() * (w + n)) by (nonlinear_arith);
        }
        Some(w + n)
    }
}

} // verus!
