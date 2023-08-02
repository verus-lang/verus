#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus! {

use crate::nonlinear_arith::internals::general_internals::*;
use crate::nonlinear_arith::mul::*;
use crate::nonlinear_arith::internals::mul_internals::{lemma_mul_auto};
use crate::nonlinear_arith::internals::mul_internals_nonlinear;
use crate::nonlinear_arith::internals::mod_internals_nonlinear::{lemma_fundamental_div_mod, lemma_mod_range, lemma_small_mod};
use crate::nonlinear_arith::internals::div_internals_nonlinear;
use crate::nonlinear_arith::math::{add as add1, sub as sub1};

/// Performs modulus recursively
#[verifier(opaque)]
pub open spec fn mod_recursive(x: int, d: int) -> int
    recommends d > 0
    decreases (if x < 0 {(d - x)} else {x}) when d > 0
{
    if x < 0 {
        mod_recursive(d + x, d)
    } else if x < d {
        x
    } else {
        mod_recursive(x - d, d)
    }
}

/// performs induction on modulus
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_induction_forall(n: int, f: FnSpec(int) -> bool)
    requires 
        n > 0,
        forall |i: int| 0 <= i < n ==> #[trigger]f(i),
        forall |i: int| i >= 0 && #[trigger]f(i) ==> #[trigger]f(add1(i, n)),
        forall |i: int| i < n  && #[trigger]f(i) ==> #[trigger]f(sub1(i, n)),
        // TODO: this definition breaks lemma_mod_induction_forall2
        // forall |i: int, j:int| (i >= 0 && j == i + n && #[trigger] f(i)) ==> #[trigger] f(j),
        // forall |i: int, j:int| (i < n  && j == i - n && #[trigger] f(i)) ==> #[trigger] f(j),
    ensures  
        forall |i| #[trigger]f(i)
{
    assert forall |i: int| #[trigger]f(i) by {
        lemma_induction_helper(n, f, i);
    };
}

// same as dafny
/// given an integer x and divisor n, the remainder of x%n is equivalent to the remainder of (x+m)%n
/// where m is a multiple of n
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_induction_forall2(n: int, f:FnSpec(int, int)->bool)
    requires
        n > 0,
        forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger]f(i, j),
        forall |i: int, j: int| i >= 0 && #[trigger]f(i, j) ==> #[trigger]f(add1(i, n), j),
        forall |i: int, j: int| j >= 0 && #[trigger]f(i, j) ==> #[trigger]f(i, add1(j, n)),
        forall |i: int, j: int| i < n  && #[trigger]f(i, j) ==> #[trigger]f(sub1(i, n), j),
        forall |i: int, j: int| j < n  && #[trigger]f(i, j) ==> #[trigger]f(i, sub1(j, n)),
    ensures
        forall |i: int, j: int| #[trigger]f(i, j)
{
    assert forall |x: int, y: int| #[trigger]f(x, y) by {
        assert forall |i: int| 0 <= i < n implies #[trigger]f(i, y) by {
            let fj = |j| f(i, j);
            lemma_mod_induction_forall(n, fj);
            assert(fj(y));
        };
        let fi = |i| f(i, y);
        lemma_mod_induction_forall(n, fi);
        assert(fi(x));
    };
}

// same as dafny now
// #[verifier::spinoff_prover]
pub proof fn lemma_div_add_denominator(n: int, x: int)
    requires n > 0
    ensures (x + n) / n == x / n + 1
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x + n, n);

    let zp = (x + n) / n - x / n - 1;
    assert (0 == n * zp + ((x + n) % n) - (x % n)) by {

        lemma_mul_auto() 
    };
    if (zp > 0) { lemma_mul_inequality(1, zp, n); }
    if (zp < 0) { lemma_mul_inequality(zp, -1, n); }
}

// same as dafny now
// #[verifier::spinoff_prover]
pub proof fn lemma_div_sub_denominator(n: int, x: int)
    requires n > 0
    ensures (x - n) / n == x / n - 1
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x - n, n);
    let zm = (x - n) / n - x / n + 1;

    assert (0 == n * zm + ((x - n) % n) - (x % n)) by { 
        lemma_mul_auto(); 
    }
    if (zm > 0) { lemma_mul_inequality(1, zm, n); }
    if (zm < 0) { lemma_mul_inequality(zm, -1, n); }
}

// slightly longer than dafny
#[verifier::spinoff_prover]
pub proof fn lemma_mod_add_denominator(n: int, x: int)
    requires n > 0
    ensures (x + n) % n == x % n
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x + n, n);
    let zp = (x + n) / n - x / n - 1;
    assert (n * zp == n * ((x + n) / n - x / n) - n) by {
        assert( n * (((x + n) / n - x / n) - 1) == n * ((x + n) / n - x / n) - n) by {
            lemma_mul_is_distributive_auto();
        };
    };

    assert(0 == n * zp + ((x + n) % n) - (x % n)) by { 
        lemma_mul_auto(); 
    }

    if (zp > 0) { lemma_mul_inequality(1, zp, n); }
    if (zp < 0) { lemma_mul_inequality(zp, -1, n); }
}

// slightly longer than dafny
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_sub_denominator(n: int, x: int)
    requires n > 0
    ensures (x - n) % n == x % n
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x - n, n);
    let zm = (x - n) / n - x / n + 1;
    lemma_mul_is_distributive_auto(); // OBSERVE
    assert(0 == n * zm + ((x - n) % n) - (x % n)) by { 
        lemma_mul_auto(); 
    }
    if (zm > 0) { lemma_mul_inequality(1, zm, n); }
    if (zm < 0) { lemma_mul_inequality(zm, -1, n); }
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_below_denominator(n: int, x: int)
    requires n > 0
    ensures 0 <= x < n <==> x % n == x
{
    assert forall |x: int| 0 <= x < n <==> #[trigger](x % n) == x by
    {
        if (0 <= x < n) { lemma_small_mod(x as nat, n as nat); }
        lemma_mod_range(x, n);
    }
}

/// proves the basics of the modulus operation
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_basics_auto(n: int)
    requires n > 0
    ensures  
        forall |x: int| #[trigger]((x + n) % n) == x % n,
        forall |x: int| #[trigger]((x - n) % n) == x % n,
        forall |x: int| #[trigger]((x + n) / n) == x / n + 1,
        forall |x: int| #[trigger]((x - n) / n) == x / n - 1,
        forall |x: int| 0 <= x < n <==> #[trigger](x % n) == x,
{

    assert forall |x: int| #[trigger]((x + n) % n) == x % n by {
        lemma_mod_add_denominator(n, x);
    };

    assert forall |x: int| #[trigger]((x - n) % n) == x % n by {
        lemma_mod_sub_denominator(n, x);
        assert((x - n) % n == x % n);
    };

    assert forall |x: int| #[trigger]((x + n) / n) == x / n + 1 by
    {
        lemma_div_add_denominator(n, x);
    };
    
    assert forall |x: int| #[trigger]((x - n) / n) == x / n - 1 by {
        lemma_div_sub_denominator(n, x);
    };

    assert forall |x: int| 0 <= x < n <==> #[trigger](x % n) == x by
    {
        lemma_mod_below_denominator(n, x);
    };
}

/// proves the quotient remainder theorem
// #[verifier::spinoff_prover]
pub proof fn lemma_quotient_and_remainder(x: int, q: int, r: int, n: int)
    requires 
        n > 0,
        0 <= r < n,
        x == q * n + r,
    ensures  
        q == x / n,
        r == x % n,
    decreases (if q > 0 { q } else { -q })
{
    lemma_mod_basics_auto(n);

    if q > 0 {
        mul_internals_nonlinear::lemma_mul_is_distributive_add(n, q - 1, 1);
        lemma_mul_is_commutative_auto();
        assert(q * n + r == (q - 1) * n + n + r);
        lemma_quotient_and_remainder(x - n, q - 1, r, n);
    }
    else if q < 0 {
        lemma_mul_is_distributive_sub(n, q + 1, 1);
        lemma_mul_is_commutative_auto();
        assert(q * n + r == (q + 1) * n - n + r);
        lemma_quotient_and_remainder(x + n, q + 1, r, n);
    }
    else {
        div_internals_nonlinear::lemma_small_div();
        assert (r / n == 0);
    }
}

/// automates the modulus operator process
// #[verifier::spinoff_prover]
pub open spec fn mod_auto(n: int) -> bool
    recommends n > 0,
{
    &&& (n % n == 0 && (-n) % n == 0)
    &&& (forall |x: int| #[trigger]((x % n) % n) == x % n)
    &&& (forall |x: int| 0 <= x < n <==> #[trigger](x % n) == x)
    &&& (forall |x: int, y: int|
         {let z = (x % n) + (y % n);
         (  (0 <= z < n && #[trigger]((x + y) % n) == z)
             || (n <= z < n + n && #[trigger]((x + y) % n) == z - n))})
    &&& (forall |x: int, y: int|
        {let z = (x % n) - (y % n);
        (  (0 <= z < n && #[trigger]((x - y) % n) == z)
            || (-n <= z < 0  && #[trigger]((x - y) % n) == z + n))})
}

/// ensures that mod_auto is true
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_auto(n: int)
    requires n > 0
    ensures mod_auto(n)        
{
    lemma_mod_basics_auto(n);
    lemma_mul_auto();

    assert forall |x: int, y: int|
    {let z = (x % n) + (y % n);
        (  (0 <= z < n &&  #[trigger]((x + y) % n) == z)
            || (n <= z < n + n && #[trigger]((x + y) % n) == z - n))} by
    {
        let xq = x / n;
        let xr = x % n;
        lemma_fundamental_div_mod(x, n);
        assert(x == xq * n + xr);
        let yq = y / n;
        let yr = y % n;
        lemma_fundamental_div_mod(y, n);
        assert(y == yq * n + yr);
        if xr + yr < n {
            lemma_quotient_and_remainder(x + y, xq + yq, xr + yr, n);
        }
        else {
            lemma_quotient_and_remainder(x + y, xq + yq + 1, xr + yr - n, n);
        }
    }

    assert forall |x: int, y: int|
    {let z = (x % n) - (y % n);
        (  (0 <= z < n &&  #[trigger]((x - y) % n) == z)
            || (-n <= z < 0 && #[trigger]((x - y) % n) == z + n))} by
    {
        let xq = x / n;
        let xr = x % n;
        lemma_fundamental_div_mod(x, n);
        assert (x == n * ( x / n) + (x % n));
        let yq = y / n;
        let yr = y % n;
        lemma_fundamental_div_mod(y, n);
        assert(y == yq * n + yr);
        if xr - yr >= 0 {
            lemma_quotient_and_remainder(x - y, xq - yq, xr - yr, n);
        }
        else {  // xr - yr < 0
            lemma_quotient_and_remainder(x - y, xq - yq - 1, xr - yr + n, n);
        }
    }
}

/// performs auto induction for modulus
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_induction_auto(n: int, x: int, f: FnSpec(int) -> bool)
    requires 
        n > 0,
        mod_auto(n) ==>{&&& (forall |i: int| #[trigger]is_le(0, i) && i < n ==> f(i))
                        &&& (forall |i: int| #[trigger]is_le(0, i) && f(i) ==> f(i + n))
                        &&& (forall |i: int| #[trigger]is_le(i + 1, n) && f(i) ==> f(i - n))}
    ensures 
        mod_auto(n),
        f(x)
{
    lemma_mod_auto(n);
    assert(forall |i: int| is_le(0, i) && #[trigger]f(i) ==> #[trigger]f(add1(i, n)));
    assert(forall |i: int| is_le(i + 1, n) && #[trigger]f(i) ==> #[trigger]f(sub1(i, n)));
    assert forall |i: int| 0 <= i < n implies #[trigger]f(i) by {
        assert(forall |i: int| is_le(0, i) && i < n ==> f(i));
        assert(is_le(0, i) && i < n);
    };
    lemma_mod_induction_forall(n, f);
    assert(f(x));
}

// // not used in any other files, especially divmod
// /* performs auto induction on modulus for all i s.t. f(i) exists */
// proof fn lemma_mod_induction_auto_forall(n: int, f: int -> bool)
//     requires n > 0
//      mod_auto(n) ==> && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i))
//                             && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n))
//                             && (forall i {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n))
//     ensures  mod_auto(n)
//     ensures  forall i {:trigger f(i)} :: f(i)
// {
//     lemma_mod_auto(n);
//     assert forall i :: IsLe(0, i) && i < n ==> f(i);
//     assert forall i {:trigger f(i), f(i + n)} :: IsLe(0, i) && f(i) ==> f(i + n);
//     assert forall i {:trigger f(i), f(i - n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n);
//     lemma_mod_induction_forall(n, f);
// }

}