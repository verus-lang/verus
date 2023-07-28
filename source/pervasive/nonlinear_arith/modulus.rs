//! Lemma for modulus operation

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::calc_macro::*;


verus! {

#[allow(unused_imports)]
use crate::nonlinear_arith::internals::div_internals::{div_recursive, lemma_div_induction_auto, div_auto, div_pos, lemma_div_auto};
#[allow(unused_imports)]
use crate::nonlinear_arith::internals::div_internals_nonlinear as DivINL;
#[allow(unused_imports)]
use crate::nonlinear_arith::internals::mod_internals::{lemma_mod_auto, mod_recursive};
#[allow(unused_imports)]
use crate::nonlinear_arith::internals::mod_internals_nonlinear as ModINL;
#[allow(unused_imports)]
use crate::nonlinear_arith::internals::mul_internals::{lemma_mul_induction_auto, lemma_mul_auto, mul_auto, lemma_mul_induction};
#[allow(unused_imports)]
use crate::nonlinear_arith::mul::*;
// use crate::nonlinear_arith::Mul::{lemma_mul_strictly_positive_auto, lemma_mul_is_associative_auto, lemma_mul_is_distributive_auto, lemma_mul_is_commutative_auto, lemma_mul_strict_inequality_converse_auto, lemma_mul_inequality_auto, lemma_mul_increases_auto};
#[allow(unused_imports)]
use crate::nonlinear_arith::internals::general_internals::{is_le};
#[allow(unused_imports)]
use crate::nonlinear_arith::div::*;


// /*******************************************************************************
//  * Modulus:
//  *******************************************************************************/

/// the common syntax of the modulus operation results in the same remainder as recursively
/// calculating the modulus
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_is_mod_recursive(x: int, m: int)
    requires m > 0
    ensures mod_recursive(x, m) == x % m
    decreases (if x < 0 { -x + m } else { x })
{
    reveal(mod_recursive);
    if x < 0 {
        calc! {
            (==)
            mod_recursive(x, m); {}
            mod_recursive(x + m, m);
            { lemma_mod_is_mod_recursive(x + m, m); }
            (x + m) % m;
            { lemma_add_mod_noop(x, m, m); }
            ((x % m) + (m % m)) % m;
            { lemma_mod_basics_auto(); }
            (x % m) % m;
            { lemma_mod_basics_auto(); }
            x % m;
        }
    } else if x < m {
        lemma_small_mod(x as nat, m as nat);
    } else {
        calc! {
            (==)
            mod_recursive(x, m); {}
            mod_recursive(x - m, m);
            { lemma_mod_is_mod_recursive(x - m, m); }
            (x - m) % m;
            { lemma_sub_mod_noop(x, m, m); }
            ((x % m) - (m % m)) % m;
            { lemma_mod_basics_auto(); }
            (x % m) % m;
            { lemma_mod_basics_auto(); }
            x % m;
        }
    }
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_is_mod_recursive_auto()
    ensures forall |x: int, d: int| d > 0 ==> mod_recursive(x, d) == #[trigger](x % d)
{
    reveal(mod_recursive);
    assert forall |x: int, d: int| d > 0 implies mod_recursive(x, d) == #[trigger](x % d) by
    {
        lemma_mod_is_mod_recursive(x, d);
    };
}

/// proves basic properties of the modulus operation: any integer divided by itself does not have a
/// remainder; performing (x % m) % m gives the same result as simply perfoming x % m 
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_basics_auto()
    ensures 
        forall |m: int|  m > 0 ==> #[trigger](m % m) == 0,
        forall |x: int, m: int|  m > 0 ==> #[trigger]((x % m) % m) == x % m,
{
    assert forall |m: int| m > 0 implies #[trigger](m % m) == 0 by {
        lemma_mod_auto(m);
    };
    assert forall |x: int, m: int| m > 0 implies #[trigger]((x % m) % m) == x % m by {
        lemma_mod_auto(m);
    };
}

/// describes the properties of the modulus operation including those described in lemma_mod_basics_auto. 
/// This lemma also states that the remainder of any division will be less than the divisor's value
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_properties_auto()
    ensures 
        forall |m: int| m > 0 ==> #[trigger](m % m) == 0,
        forall |x: int, m: int| m > 0 ==> #[trigger]((x % m) % m) == x % m,
        forall |x: int, m: int| m > 0 ==> 0 <= #[trigger](x % m) < m,
{
    lemma_mod_basics_auto();

    assert forall |x: int, m: int| m > 0 implies 0 <= #[trigger](x % m) < m by
    {
    lemma_mod_auto(m);
    }
}

/// the remainder of a natural number x divided by a natural number d will be less
/// than or equal to x
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_decreases(x: nat, m: nat)
    requires 0 < m
    ensures x % m <= x
{
    lemma_mod_auto(m as int);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_decreases_auto()
    ensures forall |x: nat, m: nat| 0 < m ==> #[trigger](x % m) <= x,
{
    assert forall |x: nat, m: nat| 0 < m implies #[trigger](x % m) <= x by
    {
        lemma_mod_decreases(x, m);
    }
}

/// if x % y is zero and x is greater than zero, x is greater than y.
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_is_zero(x: nat, m: nat)
    requires
        x > 0 && m > 0,
        x % m == 0,
    ensures 
        x >= m
{
    if (x < m) {
        lemma_small_mod(x, m);
    }
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_is_zero_auto()
    ensures forall |x: nat, m: nat| x > 0 && m > 0 && #[trigger](x % m) == 0 ==> x >= m,
{
    assert forall |x: nat, m: nat| x > 0 && m > 0 && #[trigger](x % m) == 0 implies x >= m by
    {
        lemma_mod_is_zero(x, m);
    }
}

/// a dividend that is any multiple of the divisor will result in a remainder of 0
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_multiples_basic(x: int, m: int)
    requires m > 0
    ensures (x * m) % m == 0
{
    lemma_mod_auto(m);
    lemma_mul_auto();
    let f = |u: int| (u * m) % m == 0;
    lemma_mul_induction(f);
    assert(f(x));
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_multiples_basic_auto()
    ensures forall |x: int, m: int| m > 0 ==> #[trigger]((x * m) % m) == 0,
{
    assert forall |x: int, m: int| m > 0 implies #[trigger]((x * m) % m) == 0 by
    {
        lemma_mod_multiples_basic(x, m);
    }
}

/// the remainder of adding the divisor m to the dividend b will be the same
/// as simply performing b % m
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_add_multiples_vanish(b: int, m: int)
    requires 0 < m
    ensures (m + b) % m == b % m
{
    lemma_mod_auto(m);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_add_multiples_vanish_auto()
    ensures forall |b: int, m: int| m > 0 ==> ((m + b) % m) == #[trigger](b % m),
{
    assert forall |b: int, m: int| m > 0 implies ((m + b) % m) == #[trigger](b % m) by
    {
        lemma_mod_add_multiples_vanish(b, m);
    }
}

/// the remainder of subtracting the divisor m from the dividend b will be the same
/// as simply performing b % m
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_sub_multiples_vanish(b: int, m: int)
    requires 0 < m
    ensures (-m + b) % m == b % m
{
    lemma_mod_auto(m);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_sub_multiples_vanish_auto()
    ensures forall |b: int, m: int| m > 0 ==> ((-m + b) % m) == #[trigger](b % m),
{
    assert forall |b: int, m: int| m > 0 implies ((-m + b) % m) == #[trigger](b % m) by
    {
        lemma_mod_sub_multiples_vanish(b, m);
    }
}

/// the remainder of adding any multiple of the divisor m to the dividend b will be the same
/// as simply performing b % m
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_multiples_vanish(a: int, b: int, m: int)
    requires 0 < m
    ensures (m * a + b) % m == b % m
    decreases (if a > 0 { a } else { -a })
{
    lemma_mod_auto(m);
    lemma_mul_auto();
    let f = |u: int| (m * u + b) % m == b % m;
    lemma_mul_induction(f);
    assert(f(a));
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_multiples_vanish_auto()
    ensures forall |a: int, b: int, m: int| m > 0 ==> #[trigger]((m * a + b) % m) == b % m,
{
    assert forall |a: int, b: int, m: int| m > 0 implies #[trigger]((m * a + b) % m) == b % m by
    {
        lemma_mod_multiples_vanish(a, b, m);
    }
}

/// proves equivalent forms of modulus subtraction
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_subtraction(x: nat, s: nat, d: nat)
    requires 
        0 < d, 
        0 <= s <= x % d
    ensures 
        x % d - s % d == (x - s) % d as int
{
    lemma_mod_auto(d as int);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_subtraction_auto()
    ensures forall |x: nat, s: nat, d: nat| #![trigger ((x - s) % d as int)] 0 < d && 0 <= s <= x % d ==> x % d - s % d == (x - s) % d as int,
{
    assert forall |x: nat, s: nat, d: nat| 0 < d && 0 <= s <= x % d implies x % d - s % d == #[trigger]((x - s) % d as int) as int by
    {
        lemma_mod_subtraction(x, s, d);
    }
}

/// describes expanded and succinct version of modulus operator in relation to addition (read "ensures")
// #[verifier::spinoff_prover]
pub proof fn lemma_add_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) + (y % m)) % m == (x + y) % m
{
    lemma_mod_auto(m);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_add_mod_noop_auto()
    ensures forall |x: int, y: int, m: int| #![trigger (x + y) % m] 0 < m ==> ((x % m) + (y % m)) % m == (x + y) % m,
{
    assert forall |x: int, y: int, m: int| 0 < m implies ((x % m) + (y % m)) % m == #[trigger]((x + y) % m) by
    {
        lemma_add_mod_noop(x, y, m);
    }
}

/// describes expanded and succinct version of modulus operator in relation to addition (read "ensures")
// #[verifier::spinoff_prover]
pub proof fn lemma_add_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures (x + (y % m)) % m == (x + y) % m
{
    lemma_mod_auto(m);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_add_mod_noop_right_auto()
    ensures forall |x: int, y: int, m: int| #![trigger (x + y) % m] 0 < m ==> (x + (y % m)) % m == (x + y) % m,
{
    assert forall |x: int, y: int, m: int| 0 < m implies (x + (y % m)) % m == #[trigger]((x + y) % m) by
    {
        lemma_add_mod_noop_right(x, y, m);
    }
}

/// describes expanded and succinct version of modulus operator in relation to subtraction (read "ensures")
// #[verifier::spinoff_prover]
pub proof fn lemma_sub_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) - (y % m)) % m == (x - y) % m
{
    lemma_mod_auto(m);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_sub_mod_noop_auto()
    ensures forall |x: int, y: int, m: int| #![trigger (x - y) % m] 0 < m ==> ((x % m) - (y % m)) % m == (x - y) % m,
{
    assert forall |x: int, y: int, m: int| 0 < m implies ((x % m) - (y % m)) % m == #[trigger]((x - y) % m) by
    {
        lemma_sub_mod_noop(x, y, m);
    }
}

/// describes expanded and succinct version of modulus operator in relation to subtraction (read "ensures")
// #[verifier::spinoff_prover]
pub proof fn lemma_sub_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures (x - (y % m)) % m == (x - y) % m
{
    lemma_mod_auto(m);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_sub_mod_noop_right_auto()
    ensures forall |x: int, y: int, m: int| #![trigger ((x - y) % m)] 0 < m ==> (x - (y % m)) % m == (x - y) % m,
{
    assert forall |x: int, y: int, m: int| 0 < m implies (x - (y % m)) % m == #[trigger]((x - y) % m) by
    {
        lemma_sub_mod_noop_right(x, y, m);
    }
}

/// proves equivalent forms of modulus addition
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_adds(a: int, b: int, d: int)
    requires 0 < d
    ensures 
        a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d),
        (a % d + b % d) < d ==> a % d + b % d == (a + b) % d
{
    lemma_mul_auto();
    lemma_div_auto(d);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_adds_auto()
    ensures forall |a: int, b: int, d: int| #![trigger ((a + b) % d)] 0 < d ==> a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d),
{
    assert forall |a: int, b: int, d: int| 0 < d implies a % d + b % d == #[trigger]((a + b) % d) + d * ((a % d + b % d) / d) by
    {
        lemma_mod_adds(a, b, d);
    }
}

// {:vcs_split_on_every_assert}
/// The remainder of an integer `x` by a positive integer `d` is equivalent to
/// the remainder of `x * (1 - d)` by `d`.
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_neg_neg(x: int, d: int)
    requires 0 < d
    ensures x % d == (x * (1 - d)) % d
{
    assert ((x - x * d) % d == x % d) by {
        let f = |i: int| (x - i * d) % d == x % d;
        lemma_mul_auto();
        assert (  f(0)
                && (forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger]f(crate::nonlinear_arith::internals::mul_internals::add(i, 1)))
                && (forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger]f(crate::nonlinear_arith::internals::mul_internals::sub(i, 1))))
        by {
            lemma_mod_auto(d);
        };
        lemma_mul_induction(f);
        assert(f(x));
    }
    lemma_mul_auto();
}

/// proves the validity of the quotient and remainder
#[verifier::spinoff_prover]
pub proof fn lemma_fundamental_div_mod_converse(x: int, d: int, q: int, r: int)
    requires 
        d != 0,
        0 <= r < d,
        x == q * d + r,
    ensures 
        q == x / d,
        r == x % d
{
    lemma_mul_auto();
    lemma_div_auto(d);
    lemma_mul_induction_auto(q, |u: int| u == (u * d + r) / d);
    lemma_mul_induction_auto(q, |u: int| r == (u * d + r) % d);
}

// {:timeLimitMultiplier 5}
// TO DO, but when conjuncting
// #[verifier::spinoff_prover]
pub proof fn lemma_fundamental_div_mod_converse_auto()
    ensures 
        // forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) ==> q == (x / d) && r == #[trigger](x % d),
        forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) ==> q == #[trigger](x / d),
        forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) ==> r == #[trigger](x % d),
{
    // assert forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) implies q == (x / d) && r == #[trigger](x % d) by
    // {
    //     if ( d != 0 && 0 <= r < d && x == (q * d + r)) {
    //     lemma_fundamental_div_mod_converse(x, d, q, r);
    //     }
    // }
    assert forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) implies q == #[trigger](x / d) by {
        lemma_fundamental_div_mod_converse(x, d, q, r);
    };
    assert forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) implies r == #[trigger](x % d) by {
        lemma_fundamental_div_mod_converse(x, d, q, r);
    };
}


/// the remainder of any natural number x divided by a positive integer m is always less than m
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_pos_bound(x: int, m: int)
    requires 
        0 <= x,
        0 < m,
    ensures  0 <= x % m < m
    decreases x
{
    lemma_mod_auto(m);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_pos_bound_auto()
    ensures forall |x: int, m: int| 0 <= x && 0 < m ==> 0 <= #[trigger](x % m) < m,
{
    assert forall |x: int, m: int| 0 <= x && 0 < m implies 0 <= #[trigger](x % m) < m by
    {
        lemma_mod_pos_bound(x, m);
    }
}

/// For any integers `x` and `y` and positive integer `m`, the remainder of `x * y` divided by `m`
/// is equivalent to the remainder of `x` divided by `m` times the remainder of `y` divided by `m`.
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_left(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m) * y % m == x * y % m
{
    lemma_mod_auto(m);
    lemma_mul_induction_auto(y, |u: int| (x % m) * u % m == x * u % m);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_left_auto()
    ensures forall |x: int, y: int, m: int| 0 < m ==> (x % m) * y % m == #[trigger](x * y % m),
{
    assert forall |x: int, y: int, m: int| 0 < m implies (x % m) * y % m == #[trigger](x * y % m) by
    {
        lemma_mul_mod_noop_left(x, y, m);
    }
}

/// For any integers `x` and `y` and positive integer `m`, the remainder of `x * y` divided by `m`
/// is equivalent to the remainder of `x * (y % m)` divided by `m`.
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures x * (y % m) % m == (x * y) % m
{
    lemma_mod_auto(m);
    lemma_mul_induction_auto(x, |u: int| u * (y % m) % m == (u * y) % m);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_right_auto()
    ensures forall |x: int, y: int, m: int| 0 < m ==> x * (y % m) % m == #[trigger]((x * y) % m),
{
    assert forall |x: int, y: int, m: int| 0 < m implies x * (y % m) % m == #[trigger]((x * y) % m) by
    {
        lemma_mul_mod_noop_right(x, y, m);
    }
}

/// combines previous no-op mod lemmas into a general, overarching lemma
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_general(x: int, y: int, m: int)
    requires 0 < m
    ensures 
        ((x % m) * y      ) % m == (x * y) % m,
        ( x      * (y % m)) % m == (x * y) % m,
        ((x % m) * (y % m)) % m == (x * y) % m
{
    lemma_mod_properties_auto();
    lemma_mul_mod_noop_left(x, y, m);
    lemma_mul_mod_noop_right(x, y, m);
    lemma_mul_mod_noop_right(x % m, y, m);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_general_auto()
    ensures forall |x: int, y: int, m: int| 0 < m ==> (((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m == #[trigger]((x * y) % m)),
{
    assert forall |x: int, y: int, m: int| 0 < m implies (((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m == #[trigger]((x * y) % m)) by
    {
        lemma_mul_mod_noop_general(x, y, m);
    }
}

/// For any integers `x` and `y` and positive integer `m`, the product of 
/// `x` modulus `m` and `y` modulus `m`, all modulus `m`, is the same as just
/// the product of `x` and `y` modulus `m`.
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m) * (y % m) % m == (x * y) % m
{
    lemma_mul_mod_noop_general(x, y, m);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mul_mod_noop_auto()
    ensures forall |x: int, y: int, m: int| 0 < m ==> ((x % m) * (y % m) % m == #[trigger]((x * y) % m)),
{
    assert forall |x: int, y: int, m: int| 0 < m implies ((x % m) * (y % m) % m == #[trigger]((x * y) % m)) by
    {
        lemma_mul_mod_noop(x, y, m);
    }
}

/// proves modulus equivalence in two forms
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_equivalence(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m == y % m <==> (x - y) % m == 0
{
    lemma_mod_auto(m);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_equivalence_auto()
    ensures forall |x: int, y: int, m: int| #![trigger (x % m), (y % m)] 0 < m ==> (x % m == y % m <==> (x - y) % m == 0),
{
    assert forall |x: int, y: int, m: int| 0 < m implies (#[trigger](x % m) == #[trigger](y % m) <==> (x - y) % m == 0) by
    {
        lemma_mod_equivalence(x, y, m);
    }
}

// // TODO: the following two proofs are styled very differently from dafny
// /// true if x%n and y%n are equal */
// pub open spec fn is_mod_equivalent(x: int, y: int, m: int) -> bool
//     recommends m > 0
//     // ensures x % m == y % m <==> (x - y) % m == 0
// {
//     // lemma_mod_equivalence(x, y, m);
//     x % m == y % m <==> (x - y) % m == 0 // same as x % n == y % n, but easier to do induction on x - y than x and y separately
// }

///  true if x%n and y%n are equal
#[verifier::opaque]
pub closed spec fn is_mod_equivalent(x: int, y: int, m: int) -> bool
{
    x % m == y % m <==> (x - y) % m == 0
}

/// if x % m == y % m, then (x * z) % m == (y * z) % m.
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_mul_equivalent(x: int, y: int, z: int, m: int)
    requires
        m > 0,
        is_mod_equivalent(x, y, m),
    ensures
        is_mod_equivalent(x * z, y * z, m),
{
    reveal(is_mod_equivalent);
    lemma_mul_mod_noop_left(x, z, m);
    lemma_mul_mod_noop_left(y, z, m);
    lemma_mod_equivalence(x, y, m);
    lemma_mod_equivalence(x * z, y * z, m);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_mul_equivalent_auto()
    ensures forall |x: int, y: int, z: int, m: int|  m > 0 && ( x % m == y % m <==> (x - y) % m == 0) ==> #[trigger]is_mod_equivalent(x * z, y * z, m),
{
    reveal(is_mod_equivalent);
    assert forall |x: int, y: int, z: int, m: int| m > 0 && is_mod_equivalent(x, y, m) implies #[trigger]is_mod_equivalent(x * z, y * z, m) by
    {
        lemma_mod_mul_equivalent(x, y, z, m);
    }
}

/// the remainder can increase with a larger divisor
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_ordering(x: int, k: int, d: int)
    requires 
        1 < d,
        0 < k,
    ensures 
        0 < d * k,
        x % d <= x % (d * k)
{
    lemma_mul_strictly_increases(d,k);
    calc! {
    (==)
    x % d + d * (x / d);
    { lemma_fundamental_div_mod(x, d); }
    x;
    { lemma_fundamental_div_mod(x, d * k); }
    x % (d * k) + (d * k) * (x / (d * k));
    { lemma_mul_is_associative_auto(); }
    x % (d * k) + d * (k * (x / (d * k)));
    }
    calc! {
    (==)
    x % d;
    { lemma_mod_properties_auto(); }
    (x % d) % d;
    { lemma_mod_multiples_vanish(x / d  - k * (x / (d * k)), x % d, d); }
    (x % d + d * (x / d  - k * (x / (d * k)))) % d;
    { lemma_mul_is_distributive_sub_auto(); }
    (x % d + d * (x / d) - d * (k * (x / (d * k)))) % d; {}
    (x % (d * k)) % d;
    }

    assert( (x % (d * k)) % d <= x % (d * k)) by {
        lemma_mod_properties_auto();
        lemma_mod_decreases((x % (d * k)) as nat, d as nat);
    };
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mod_ordering_auto()
    ensures forall |x: int, k: int, d: int| 1 < d && 0 < k ==> (x % d <= #[trigger](x % (d * k))),
{
    assert forall |x: int, k: int, d: int| 1 < d && 0 < k implies (x % d <= #[trigger](x % (d * k))) by
    {
        lemma_mod_ordering(x, k, d);
    }
}

/// For any integer `x` and positive integers `a` and `b`, the remainder of `x` divided by `a * b`
/// modulus `a` is equivalent to the remainder of `x` divided by `a`.
#[verifier::spinoff_prover]
pub proof fn lemma_mod_mod(x: int, a: int, b: int)
    requires 
        0 < a,
        0 < b,
    ensures
        0 < a * b,
        (x % (a * b)) % a == x % a,
{
    lemma_mul_strictly_positive_auto();
    calc! {
    (==)
    x;
    { lemma_fundamental_div_mod(x, a * b); }
    (a * b) * (x / (a * b)) + x % (a * b);
    { lemma_mul_is_associative_auto(); }
    a * (b * (x / (a * b))) + x % (a * b);
    { lemma_fundamental_div_mod(x % (a * b), a); }
    a * (b * (x / (a * b))) + a * (x % (a * b) / a) + (x % (a * b)) % a;
    { lemma_mul_is_distributive_auto(); }
    a * (b * (x / (a * b)) + x % (a * b) / a) + (x % (a * b)) % a;
    }
    lemma_mod_properties_auto();
    lemma_mul_is_commutative_auto();
    lemma_fundamental_div_mod_converse(x, a, b * (x / (a * b)) + x % (a * b) / a, (x % (a * b)) % a);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_mod_auto()
    ensures forall |x: int, a: int, b: int| #![trigger (a * b), (x % a)](0 < a && 0 < b) ==> ((0 < a * b) && ((x % (a * b)) % a == (x % a))),
{
    assert forall |x: int, a: int, b: int| 0 < a && 0 < b implies 0 < #[trigger](a * b) && ((x % (a * b)) % a == #[trigger](x % a)) by
    {
        lemma_mod_mod(x, a, b);
    }
}

// #[verifier::spinoff_prover]
pub proof fn lemma_part_bound2(x: int, y: int, z: int)
    requires 
        0 <= x,
        0 < y,
        0 < z,
    ensures 
        y * z > 0,
        (x % y) % (y * z) < y,
{
    lemma_mul_strictly_positive_auto();
    lemma_mod_properties_auto();
    assert(x % y < y);
    lemma_mul_increases_auto();
    lemma_mul_is_commutative_auto();
    assert(y <= y * z);
    assert(0 <= x % y < y * z);
    lemma_mod_properties_auto();
    lemma_small_mod((x % y) as nat, (y * z) as nat);
    assert((x % y) % (y * z) == x % y);
}

/// The product of positive integers `y` and `z` is always positive
/// The remainder of nonnegative integer `x` modulus `y` divided by `y * z` is
/// strictly less than `y`
// #[verifier::spinoff_prover]
pub proof fn lemma_part_bound2_auto()
    ensures 
        forall |y: int, z: int| (0 < y && 0 < z) ==> #[trigger](y * z) > 0,
        forall |x: int, y: int, z: int| (0 <= x && 0 < y && 0 < z) ==> (#[trigger](x % y) % #[trigger](y * z) < y),    
{
    assert forall |y: int, z: int| 0 < y && 0 < z implies #[trigger](y * z) > 0 by
    {
        lemma_mul_strictly_positive_auto();
    };
    assert forall |x: int, y: int, z: int| 0 <= x && 0 < y && 0 < z implies #[trigger](x % y) % #[trigger](y * z) < y by
    {
        lemma_part_bound2(x, y, z);
    };
}

/// ensures the validity of an expanded form of the modulus operation,
/// as expressed in the pre and post conditions
// #[verifier::spinoff_prover]
pub proof fn lemma_mod_breakdown(x: int, y: int, z: int)
    requires
        0 <= x,
        0 < y,
        0 < z,
    ensures 
        y * z > 0,
        x % (y * z) == y * ((x / y) % z) + x % y
{
    lemma_mul_strictly_positive_auto();
    lemma_div_pos_is_pos(x, y);
    assert(0 <= x / y);

    assert((y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z) by {
        lemma_part_bound1(x, y, z);
        lemma_part_bound2(x, y, z);
        lemma_mul_basics_auto();
        lemma_mul_is_distributive_auto();
    };

    calc! {
    (==)
    x % (y * z);
    { lemma_fundamental_div_mod(x, y); }
    (y * (x / y) + x%  y) % (y * z);
    {
        lemma_mod_properties_auto();
        assert(0 <= x % y);
        lemma_mul_nonnegative(y, x / y);
        assert((y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z);
        lemma_mod_adds(y * (x / y), x % y, y * z);
    }
    (y * (x / y)) % (y * z) + (x % y) % (y * z);
    {
        lemma_mod_properties_auto();
        lemma_mul_increases(z, y);
        lemma_mul_is_commutative_auto();
        assert(x % y < y && y <= y * z);
        lemma_small_mod((x % y) as nat, (y * z) as nat);
        assert((x % y) % (y * z) == x % y);
    }
    (y * (x / y)) % (y * z) + x % y;
    { lemma_truncate_middle(x / y, y, z); }
    y * ((x / y) % z) + x % y;
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_mod_breakdown_auto()
    ensures forall |x: int, y: int, z: int| 0 <= x && 0 < y && 0 < z ==> y * z > 0 && #[trigger](x % (y * z)) == y * ((x / y) % z) + x % y,
{
    assert forall |x: int, y: int, z: int| 0 <= x && 0 < y && 0 < z implies y * z > 0 && #[trigger](x % (y * z)) == y * ((x / y) % z) + x % y by
    {
        lemma_mod_breakdown(x, y, z);
    }
}

}
