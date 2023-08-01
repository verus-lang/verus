//! Declares helper lemmas and predicates for non-linear arithmetic
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn add (a: int, b: int) -> int
{
    a + b
}

pub open spec fn sub (a: int, b: int) -> int
{
    a - b
}

pub open spec fn is_le(x: int, y: int) -> bool
{
    x <= y
}

/* aids in the process of induction for modulus */
// #[verifier::spinoff_prover]
proof fn lemma_induction_helper_pos(n: int, f: FnSpec(int) -> bool, x: int)
    requires 
        x >= 0,
        n > 0,
        forall |i : int| 0 <= i < n ==> #[trigger] f(i),
        forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (add(i, n)),
        forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (sub(i, n))
    ensures
        f(x)
    decreases x
{
    if (x >= n)
    {
        assert(x - n < x);
        lemma_induction_helper_pos(n, f, x - n);
        assert (f (add(x - n, n)));
        assert(f((x - n) + n));
    }
}

// #[verifier::spinoff_prover]
proof fn lemma_induction_helper_neg(n: int, f: FnSpec(int) -> bool, x: int)
    requires 
        x < 0,
        n > 0,
        forall |i : int| 0 <= i < n ==> #[trigger] f(i),
        forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (add(i, n)),
        forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (sub(i, n))
    ensures
        f(x)
    decreases -x
{
    if (-x <= n) {
        lemma_induction_helper_pos(n, f, x + n);
        assert (f (sub(x + n, n)));
        assert(f((x + n) - n));
    }
    else {
        lemma_induction_helper_neg(n, f, x + n);
        assert (f (sub(x + n, n)));
        assert(f((x + n) - n));
    }
}

// #[verifier::spinoff_prover]
pub proof fn lemma_induction_helper(n: int, f: FnSpec(int) -> bool, x: int)
requires 
    n > 0,
    forall |i : int| 0 <= i < n ==> #[trigger] f(i),
    forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (add(i, n)),
    forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (sub(i, n))
ensures
    f(x)
{
    if (x >= 0) {
        lemma_induction_helper_pos(n, f, x);
    }
    else {
        lemma_induction_helper_neg(n, f, x);
    }
}

}

