#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus! {
use crate::nonlinear_arith::internals::general_internals::{is_le};
use crate::nonlinear_arith::internals::mod_internals::{lemma_mod_induction_forall, lemma_mod_induction_forall2, mod_auto, lemma_mod_auto, lemma_mod_basics_auto};
use crate::nonlinear_arith::internals::mod_internals_nonlinear;
use crate::nonlinear_arith::internals::div_internals_nonlinear;
use crate::nonlinear_arith::math::{add as add1, sub as sub1};

/// Performs division recursively with positive denominator.
#[verifier(opaque)]
pub open spec fn div_pos(x: int, d: int) -> int
    recommends d > 0
    decreases (if x < 0 {d - x} else {x}) when d > 0
{
    if x < 0 
    {
        -1 + div_pos(x + d, d) 
    } else if x < d {
        0
    }
    else {
        1 + div_pos(x - d, d)
    }
}

/// Performs division recursively.
#[verifier(opaque)]
pub open spec fn div_recursive(x: int, d: int) -> int
    recommends d != 0
{
    // reveal(div_pos);
    if d > 0 {
        div_pos(x, d)
    } else {
        -1 * div_pos(x, -1 * d)
    }
}

/// Proves the basics of the division operation
// #[verifier::spinoff_prover]
pub proof fn lemma_div_basics(n: int)
    requires n > 0
    ensures  
        (n / n) == 1 &&  -((-n) / n) == 1,
        forall |x:int| 0 <= x < n <==> #[trigger](x / n) == 0,
        forall |x:int| #[trigger]((x + n) / n) == x / n + 1,
        forall |x:int| #[trigger]((x - n) / n) == x / n - 1,
{
    lemma_mod_auto(n);
    lemma_mod_basics_auto(n);
    div_internals_nonlinear::lemma_small_div();
    div_internals_nonlinear::lemma_div_by_self(n);
    
    assert forall |x:int| 0 <= x < n <== #[trigger](x / n) == 0 by {
        mod_internals_nonlinear::lemma_fundamental_div_mod(x, n);
    }
}

/// Automates the division operator process. Contains the identity property, a
/// fact about when quotients are zero, and facts about adding and subtracting
/// integers over a common denominator.
pub open spec fn div_auto(n: int) -> bool
    recommends n > 0
{
    &&& mod_auto(n)
    &&& (n / n == -((-n) / n) == 1)
    &&& forall |x: int| 0 <= x < n <==> #[trigger](x / n) == 0
    &&& (forall |x: int, y: int| #![trigger ((x + y) / n)]
         {let z = (x % n) + (y % n);
         (  (0 <= z < n && ((x + y) / n) == x / n + y / n)
             || (n <= z < n + n && ((x + y) / n) == x / n + y / n + 1))})
    &&& (forall |x: int, y: int| #![trigger ((x - y) / n)]
        {let z = (x % n) - (y % n);
        (  (0 <= z < n && ((x - y) / n) == x / n - y / n)
            || (-n <= z < 0  && ((x - y) / n) == x / n - y / n - 1))})
}

/// Ensures that div_auto is true 
#[verifier::spinoff_prover]
pub proof fn lemma_div_auto(n: int)
    requires n > 0
    ensures
        div_auto(n)
{
    lemma_mod_auto(n);
    lemma_div_basics(n);

    assert forall |x: int| 0 <= x < n <==> #[trigger](x / n) == 0 by {
        lemma_div_basics(n);
    }
    assert ((0 + n) / n == 1);
    assert ((0 - n) / n == -1);

    assert forall |x: int, y: int|
         {let z = (x % n) + (y % n);
         (  (0 <= z < n && #[trigger]((x + y) / n) == x / n + y / n)
             || (n <= z < n + n && #[trigger]((x + y) / n) == x / n + y / n + 1))} by
    {
    let f = |xx:int, yy:int|
        {let z = (xx % n) + (yy % n);
            (  (0 <= z < n && ((xx + yy) / n) == xx / n + yy / n)
                || (n <= z < 2 * n && ((xx + yy) / n) == xx / n + yy / n + 1))};
    
    assert forall |i: int, j: int| {
        // changing this from j + n to mod's addition speeds up the verification
        // otherwise you need higher rlimit
        // might be a good case for profilers
        &&& ( j >= 0 && #[trigger]f(i, j) ==> f(i, add1(j, n)))
        &&& ( i < n  && f(i, j) ==> f(i - n, j))
        &&& ( j < n  && f(i, j) ==> f(i, j - n))
        &&& ( i >= 0 && f(i, j) ==> f(i + n, j))
    } by
    {
        assert(((i + n) + j) / n == ((i + j) + n) / n);
        assert((i + (j + n)) / n == ((i + j) + n) / n);
        assert(((i - n) + j) / n == ((i + j) - n) / n);
        assert((i + (j - n)) / n == ((i + j) - n) / n);
    }
    assert forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger]f(i, j) by
    {
        assert(((i + n) + j) / n == ((i + j) + n) / n);
        assert((i + (j + n)) / n == ((i + j) + n) / n);
        assert(((i - n) + j) / n == ((i + j) - n) / n);
        assert((i + (j - n)) / n == ((i + j) - n) / n);
    }

    lemma_mod_induction_forall2(n, f);
    assert(f(x, y));
    }

    assert forall |x:int, y:int|
        {let z = (x % n) - (y % n);
        (  (0 <= z < n && #[trigger]((x - y) / n) == x / n - y / n)
            || (-n <= z < 0  && #[trigger]((x - y) / n) == x / n - y / n - 1))} by
    {
    let f = |xx:int, yy:int|
        {let z = (xx % n) - (yy % n);
            (  (0 <= z < n &&((xx - yy) / n) == xx / n - yy / n)
                || (-n <= z < 0 && (xx - yy) / n == xx / n - yy / n - 1))};
    
    assert forall |i: int, j: int| {
        &&& ( j >= 0 && #[trigger]f(i, j) ==> f(i, j + n))
        &&& ( i < n  && f(i, j) ==> f(i - n, j))
        &&& ( j < n  && f(i, j) ==> f(i, j - n))
        &&& ( i >= 0 && f(i, j) ==> f(i + n, j))
    } by
    {
        assert(((i + n) - j) / n == ((i - j) + n) / n);
        assert((i - (j - n)) / n == ((i - j) + n) / n);
        assert(((i - n) - j) / n == ((i - j) - n) / n);
        assert((i - (j + n)) / n == ((i - j) - n) / n);
    }
    assert forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger]f(i, j) by
    {
        assert(((i + n) - j) / n == ((i - j) + n) / n);
        assert((i - (j - n)) / n == ((i - j) + n) / n);
        assert(((i - n) - j) / n == ((i - j) - n) / n);
        assert((i - (j + n)) / n == ((i - j) - n) / n);
    }
    lemma_mod_induction_forall2(n, f);
    assert(f(x, y));
    }
}

/// Performs auto induction for division 
// #[verifier::spinoff_prover]
pub proof fn lemma_div_induction_auto(n: int, x: int, f: FnSpec(int) -> bool)
    requires
        n > 0,
        div_auto(n) ==>{&&& (forall |i: int| #[trigger]is_le(0, i) && i < n ==> f(i))
                        &&& (forall |i: int| #[trigger]is_le(0, i) && f(i) ==> f(i + n))
                        &&& (forall |i: int| #[trigger]is_le(i + 1, n) && f(i) ==> f(i - n))}
    ensures  
        div_auto(n),
        f(x)
{
    lemma_div_auto(n);
    assert(forall |i: int| is_le(0, i) && i < n ==> f(i));
    assert(forall |i: int| is_le(0, i) && #[trigger]f(i) ==> #[trigger]f(add1(i, n)));
    assert(forall |i: int| is_le(i + 1, n) && #[trigger]f(i) ==> #[trigger]f(sub1(i, n)));
    assert forall |i: int| 0 <= i < n implies #[trigger]f(i) by {
        assert(f(i)) by {
            assert(forall |i: int| is_le(0, i) && i < n ==> f(i));
            assert(is_le(0, i) && i < n);
        };
    };
    lemma_mod_induction_forall(n, f);
    assert(f(x));
}

// same as the mod case, it is not invoked anywhere else
// /// Performs auto induction on division for all i s.t. f(i) exists 
// proof fn lemma_div_induction_auto_forall(n:int, f:int->bool)
//     requires n > 0
//     requires div_auto(n) ==> && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i))
//                             && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n))
//                             && (forall i {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n))
//     ensures  div_auto(n)
//     ensures  forall i {:trigger f(i)} :: f(i)
// {
//     lemma_div_auto(n);
//     assert forall i :: IsLe(0, i) && i < n ==> f(i);
//     assert forall i {:trigger f(i), f(i + n)} :: IsLe(0, i) && f(i) ==> f(i + n);
//     assert forall i {:trigger f(i), f(i - n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n);
//     lemma_mod_induction_forall(n, f);
// }

}