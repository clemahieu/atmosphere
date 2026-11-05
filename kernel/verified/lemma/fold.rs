//! Facts about summing a function over a finite set with `fold`.

use vstd::prelude::*;

verus! {

pub open spec fn sum_step<A>(f: spec_fn(A) -> int) -> spec_fn(int, A) -> int {
    |e: int, a: A| e + f(a)
}

proof fn sum_step_commutative<A>(f: spec_fn(A) -> int)
    ensures
        vstd::iset::fold::is_fun_commutative(sum_step(f)),
{
    assert forall|a1: A, a2: A, b: int|
        #[trigger] sum_step(f)(sum_step(f)(b, a2), a1) == sum_step(f)(sum_step(f)(b, a1), a2) by {
    };
}

/// Taking `a` out of the set takes `f(a)` out of the sum.
pub proof fn fold_sum_remove<A>(s: ISet<A>, f: spec_fn(A) -> int, a: A)
    requires
        s.finite(),
        s.contains(a),
    ensures
        s.fold(0, sum_step(f)) == s.remove(a).fold(0, sum_step(f)) + f(a),
{
    sum_step_commutative(f);
    assert(s.remove(a).insert(a) =~= s);
    vstd::iset::fold::lemma_fold_insert(s.remove(a), 0, sum_step(f), a);
}

/// Functions that agree on the set have the same sum over it.
pub proof fn fold_sum_congruence<A>(s: ISet<A>, f: spec_fn(A) -> int, g: spec_fn(A) -> int)
    requires
        s.finite(),
        forall|x: A| #[trigger] s.contains(x) ==> f(x) == g(x),
    ensures
        s.fold(0, sum_step(f)) == s.fold(0, sum_step(g)),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s =~= ISet::empty());
        vstd::iset::fold::lemma_fold_empty::<A, int>(0, sum_step(f));
        vstd::iset::fold::lemma_fold_empty::<A, int>(0, sum_step(g));
    } else {
        let a = s.choose();
        fold_sum_remove(s, f, a);
        fold_sum_remove(s, g, a);
        fold_sum_congruence(s.remove(a), f, g);
    }
}

/// With no negative terms, the sum is at least any one of them.
pub proof fn fold_sum_ge<A>(s: ISet<A>, f: spec_fn(A) -> int, c: A)
    requires
        s.finite(),
        s.contains(c),
        forall|x: A| #[trigger] f(x) >= 0,
    ensures
        s.fold(0, sum_step(f)) >= f(c),
{
    fold_sum_remove(s, f, c);
    fold_sum_nonneg(s.remove(c), f);
}

proof fn fold_sum_nonneg<A>(s: ISet<A>, f: spec_fn(A) -> int)
    requires
        s.finite(),
        forall|x: A| #[trigger] f(x) >= 0,
    ensures
        s.fold(0, sum_step(f)) >= 0,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s =~= ISet::empty());
        vstd::iset::fold::lemma_fold_empty::<A, int>(0, sum_step(f));
    } else {
        let a = s.choose();
        fold_sum_remove(s, f, a);
        fold_sum_nonneg(s.remove(a), f);
    }
}

/// Changing `f` at one element changes the sum by that difference.
pub proof fn fold_sum_change<A>(s: ISet<A>, new: spec_fn(A) -> int, old: spec_fn(A) -> int, a: A)
    requires
        s.finite(),
        s.contains(a),
        forall|x: A| #[trigger] s.contains(x) && x != a ==> new(x) == old(x),
    ensures
        s.fold(0, sum_step(new)) == s.fold(0, sum_step(old)) - old(a) + new(a),
{
    fold_sum_remove(s, new, a);
    fold_sum_remove(s, old, a);
    fold_sum_congruence(s.remove(a), new, old);
}

} // verus!
