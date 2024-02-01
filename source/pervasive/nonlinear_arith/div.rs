//! This file contains proofs related to integer division. These are
//! part of the math standard library.
//!
//! It's based on the first part (since the second part is about
//! modulo) of the following file from the Dafny math standard
//! library:
//! `Source/DafnyStandardLibraries/src/Std/Arithmetic/DivMod.dfy`.
//! That file has the following copyright notice:
//! /*******************************************************************************
//! * Original: Copyright (c) Microsoft Corporation *
//! SPDX-License-Identifier: MIT * * Modifications and Extensions:
//! Copyright by the contributors to the Dafny Project *
//! SPDX-License-Identifier: MIT
//! *******************************************************************************/

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::calc_macro::*;

verus! {

#[allow(unused_imports)]
use crate::nonlinear_arith::internals::div_internals::{div_recursive, lemma_div_induction_auto, div_auto, div_pos, lemma_div_auto};
use crate::nonlinear_arith::internals::div_internals_nonlinear as DivINL;
use crate::nonlinear_arith::internals::mod_internals_nonlinear as ModINL;
use crate::nonlinear_arith::internals::mul_internals::{lemma_mul_auto, lemma_mul_induction};
use crate::nonlinear_arith::mul::*;
use crate::nonlinear_arith::internals::general_internals::{is_le};
use crate::nonlinear_arith::modulus::*;
use crate::nonlinear_arith::math::{add as add1, sub as sub1, div as div1};

/// Proof that, for the case of `x / d`, division using `/` is
/// equivalent to division using [`div_recursive`]
pub proof fn lemma_div_is_div_recursive(x: int, d: int)
    requires 0 < d
    ensures div_recursive(x, d) == x / d
{
    reveal(div_recursive);
    reveal(div_pos);
    lemma_div_induction_auto(d, x, |u: int| div_recursive(u, d) == u / d);
}

/// Proof that division using `/` is equivalent to division using
/// [`div_recursive`] as long as the divisor is positive
pub proof fn lemma_div_is_div_recursive_auto()
    ensures forall |x: int, d: int| d > 0 ==> div_recursive(x, d) == #[trigger](x / d)
{
    reveal(div_recursive);
    assert forall |x: int, d: int| d > 0 implies div_recursive(x, d) == #[trigger](x / d) by
    {
        lemma_div_is_div_recursive(x, d);
    }
}

/// Proof that the quotient of an integer divided by itself is 1,
/// specifically that `d / d == 1`
pub proof fn lemma_div_by_self(d: int)
    requires d != 0
    ensures d / d == 1
{
    DivINL::lemma_div_by_self(d);
}

/// Proof that 0 divided by a nonzero integer is 0, specifically `0 / d == 0`
pub proof fn lemma_div_of0(d: int)
    requires d != 0
    ensures 0 as int  / d == 0
{
    DivINL::lemma_div_of0(d);
}

/// Proof establishing basic properties of division using `x`: 0
/// divided by `x` is 0; `x` divided by 1 is itself; and `x` divided
/// by itself is 1.
pub proof fn lemma_div_basics(x: int)
    ensures 
        x != 0 as int ==> 0 as int / x == 0,
        x / 1 == x,
        x != 0 ==> x / x == 1,
{
    if (x != 0) {
        lemma_div_by_self(x);
        lemma_div_of0(x);
    }
}

/// Proof establishing basic properties of division: 0 divided by any
/// integer is 0; any integer divided by 1 is itself; any integer
/// divided by itself is 1.
pub proof fn lemma_div_basics_auto()
    ensures
        forall |x: int| x != 0 ==> #[trigger](0int / x) == 0,
        forall |x: int| #[trigger](x / 1) == x,
        forall |x: int, y: int| x >= 0 && y > 0 ==> #[trigger](x / y) >= 0,
        forall |x: int, y: int| x >= 0 && y > 0 ==> #[trigger](x / y) <= x,
{
    assert forall |x: int| x != 0 implies #[trigger](0int / x) / x == 0 by
    {
        lemma_div_basics(x);
    };
    
    assert forall |x: int| x != 0 implies #[trigger](x / 1) == x by
    {
        lemma_div_basics(x);
    };
    
    assert forall |x: int, y: int| x >= 0 && y > 0 implies 0 <= #[trigger](x / y) <= x by
    {
        lemma_div_pos_is_pos(x, y);
        lemma_div_is_ordered_by_denominator(x, 1, y);
    };
}

/// Proof that if a dividend is a whole number, the divisor is a
/// natural number, and their quotient is 0, then the dividend is
/// smaller than the divisor
// #[verifier::spinoff_prover]
pub proof fn lemma_small_div_converse_auto()
    ensures forall |x: int, d:int| 0 <= x && 0 < d && #[trigger](x / d) == 0 ==> x < d,
{
    assert forall |x: int, d: int| 0 <= x && 0 < d &&  #[trigger](x / d) == 0 implies x < d by
    {
        lemma_div_induction_auto(d, x, |u: int| 0 <= u && 0 < d && u / d == 0 ==> u < d); 
    }
}

/// Proof that division of a positive integer by a positive integer
/// less than or equal to it is nonzero. Specifically, given that `x
/// >= d`, we can conclude that `x / d > 0`.
pub proof fn lemma_div_non_zero(x: int, d: int)
    requires x >= d > 0
    ensures x / d > 0
{
    lemma_div_pos_is_pos_auto();
    if x / d == 0 {
        lemma_small_div_converse_auto();
    }
}

/// Proof that division of a positive integer by a positive integer
/// less than or equal to it is nonzero
pub proof fn lemma_div_non_zero_auto()
    ensures forall |x: int, d: int| x >= d > 0 ==> #[trigger] (x / d) > 0
{
    assert forall |x: int, d: int| x >= d > 0 implies #[trigger] (x / d) > 0 by
    {
        lemma_div_non_zero(x, d);
    }
}

/// Proof that given two fractions with the same numerator, the order
/// of the fractions is determined by the denominators. However, if
/// the numerator is 0, the fractions are equal regardless of the
/// denominators' values. Specifically, given that `1 <= y <= z`, we
/// know `x / y >= x / z`.
pub proof fn lemma_div_is_ordered_by_denominator(x: int, y: int, z: int)
    requires 
        0 <= x,
        1 <= y <= z
    ensures 
        x / y >= x / z
    decreases x
{
    reveal(div_recursive);
    reveal(div_pos);
    lemma_div_is_div_recursive_auto();

    assert(forall |u: int, d: int| #![trigger div_recursive(u, d)] #![trigger div1(u, d)]
               d > 0 ==> div_recursive(u, d) == div1(u, d));

    if (x < z)
    {
        lemma_div_is_ordered(0, x, y);
    }
    else
    {
        lemma_div_is_ordered(x - z, x - y, y);
        lemma_div_is_ordered_by_denominator(x - z, y, z);
    }
  
}

/// Proof that given two fractions with the same numerator, the order
/// of the fractions is determined by the denominators. However, if
/// the numerator is 0, the fractions are equal regardless of the
/// denominators' values.
pub proof fn lemma_div_is_ordered_by_denominator_auto()
    ensures forall |x: int, y: int, z: int| 0 <= x && 1 <= y <= z ==> #[trigger](x / y) >= #[trigger](x / z)
{
    assert forall |x: int, y: int, z: int| 0 <= x && 1 <= y <= z implies #[trigger](x / y) >= #[trigger](x / z) by
    {
        lemma_div_is_ordered_by_denominator(x, y, z);
    }
}

/// Proof that a number gets strictly smaller when divided by a number
/// greater than one. Specifically, `x / d < x`.
pub proof fn lemma_div_is_strictly_smaller(x: int, d: int)
    requires 
        0 < x, 
        1 < d
    ensures 
        x / d  < x
    decreases x
{
    lemma_div_induction_auto(d, x, |u: int| 0 < u ==> u / d < u);
}

/// Proof that a number gets strictly smaller when divided by a number
/// greater than one
pub proof fn lemma_div_is_strictly_smaller_auto()
    ensures forall |x: int, d: int|  0 < x && 1 < d ==> #[trigger](x / d) < x,
{
    assert forall |x: int, d: int|  0 < x && 1 < d implies #[trigger](x / d) < x by
    {
        lemma_div_is_strictly_smaller(x, d);
    }
}

/// Proof that, given `r == a % d + b % d - (a + b) % d`, `r` can also
/// be expressed as `d * ((a + b) / d) - d * (a / d) - d * (b / d)`.
pub proof fn lemma_dividing_sums(a: int, b: int, d: int, r: int)
    requires 
        0 < d,
        r == a % d + b % d - (a + b) % d,
    ensures 
        d * ((a + b) / d) - r == d * (a / d) + d * (b / d)
{
    ModINL::lemma_fundamental_div_mod(a + b, d);
    ModINL::lemma_fundamental_div_mod(a, d);
    ModINL::lemma_fundamental_div_mod(b, d);
}

/// Proof that for any values of the following variables, `r == a % d
/// + b % d - (a + b) % d` implies `r == d * ((a + b) / d) - d * (a /
/// d) - d * (b / d)`.
pub proof fn lemma_dividing_sums_auto()
    ensures forall |a: int, b: int, d: int, r: int| 
    #![trigger (d * ((a + b) / d) - r), (d * (a / d) + d * (b / d))] 
    0 < d && r == a % d + b % d - (a + b) % d ==> 
        d * ((a + b) / d) - r == d * (a / d) + d * (b / d),
{
    assert forall |a: int, b: int, d: int, r: int| 
    0 < d && r == a % d + b % d - (a + b) % d implies
        #[trigger](d * ((a + b) / d) - r) == #[trigger](d * (a / d) + d * (b / d)) by
    {
        lemma_dividing_sums(a, b, d, r);
    }
}

/// Proof that dividing a whole number by a natural number will result
/// in a quotient that is greater than or equal to 0. Specifically,
/// `x / d >= 0`.
pub proof fn lemma_div_pos_is_pos(x: int, d: int)
    requires 
        0 <= x,
        0 < d
    ensures 
        0 <= x / d
{
    lemma_div_auto(d);
    assert(div_auto(d));
    let f = |u: int| 0 <= u ==> u / d >= 0;

    assert forall |i: int| #[trigger]is_le(0, i) && f(i) implies f(i + d) by {
        assert(i / d >= 0);
    };

    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u / d >= 0);
}

/// Proof that dividing a whole number by a natural number will result
/// in a quotient that is greater than or equal to 0
pub proof fn lemma_div_pos_is_pos_auto()
    ensures
        forall |x: int, d: int|  0 <= x && 0 < d ==> 0 <= #[trigger](x / d)
{
    assert forall |x: int, d: int| 0 <= x && 0 < d implies 0 <= #[trigger] (x / d) by
    {
        lemma_div_pos_is_pos(x, d);
    }
}

/// Proof that dividing a number then adding 1 gives the same result
/// as adding the divisor and then doing the division. Specifically,
/// `1 + (x / d)` is equal to `(d + x) / d`.
pub proof fn lemma_div_plus_one(x: int, d: int)
    requires 0 < d
    ensures 1 + x / d == (d + x) / d
{
    lemma_div_auto(d);
}

/// Proof that dividing a number then adding 1 gives the same result
/// as adding the divisor and then doing the division
pub proof fn lemma_div_plus_one_auto()
    ensures
        forall |x: int, d: int| #![trigger (1 + x / d), ((d + x) / d)] 0 < d ==> 1 + (x / d) == (d + x) / d,
{
    assert forall |x: int, d: int|  0 < d implies  #[trigger](1 + x / d) == #[trigger]((d + x) / d) by
    {
        lemma_div_plus_one(x, d);
    }
}

/// Proof that dividing a number then subtracting 1 gives the same result
/// as subtracting the divisor and then doing the division. Specifically,
/// `-1 + (x / d)` is equal to `(-d + x) / d`.
pub proof fn lemma_div_minus_one(x: int, d: int)
    requires 0 < d
    ensures -1 + x / d == (-d + x) / d
{
    lemma_div_auto(d);
}

/// Proof that dividing a number then subtracting 1 gives the same result
/// as subtracting the divisor and then doing the division
pub proof fn lemma_div_minus_one_auto()
    ensures forall |x: int, d: int| 
        #![trigger (-1 + x / d), ((-d + x) / d)] 
        0 < d ==> -1 + x / d == (-d + x) / d,
{
    assert forall |x: int, d: int|  0 < d implies  #[trigger](-1 + x / d) == #[trigger]((-d + x) / d) by
    {
        lemma_div_minus_one(x, d);
    }
}

/// Proof that dividing any non-negative integer less than `d` by `d`
/// produces a quotient of 0
pub proof fn lemma_basic_div(d: int)
    requires 0 < d
    ensures forall |x: int| 0 <= x < d ==> #[trigger](x / d) == 0
{
    lemma_div_auto(d);
}

/// Proof that dividing any non-negative integer by a larger integer
/// produces a quotient of 0
pub proof fn lemma_basic_div_auto()
    ensures forall |x: int, d: int| 0 <= x < d ==> #[trigger](x / d) == 0
{
    assert forall |x: int, d: int| 0 <= x < d implies #[trigger](x / d) == 0 by
    {
        lemma_basic_div(d);
    }
}

/// Proof that numerical order is preserved when dividing two seperate
/// integers by a common positive divisor. Specifically, given that
/// `z > 0` and `x <= y`, we know `x / z <= y / z`.
pub proof fn lemma_div_is_ordered(x: int, y: int, z: int)
    requires 
        x <= y,
        0 < z,
    ensures x / z <= y / z
{
    lemma_div_auto(z);
    let f = |xy: int| xy <= 0 ==> (xy + y) / z <= y / z;

    assert forall |i: int| #[trigger]is_le(i + 1, z) && f(i) implies f(i - z) by {
        if (i - z <= 0) {
            assert( f(i) );
            assert( i <= 0 ==> (i + y) / z <= y / z );
            if (i > 0) {
                assert ( z > 0 );
                assert( i <= z );
                assert ( ((i + y) - z) / z <= y / z );
            } else {
                assert( (i + y) / z <= y / z );
            }
            assert( (i - z + y) / z <= y / z );
        }
    };

    lemma_div_induction_auto(z, x - y, |xy: int| xy <= 0 ==> (xy + y) / z <= y / z);
}

/// Proof that numerical order is preserved when dividing two seperate
/// integers by a common positive divisor
pub proof fn lemma_div_is_ordered_auto()
    ensures forall |x: int, y: int, z: int| x <= y && 0 < z ==> #[trigger](x / z) <= #[trigger](y / z)
{
    assert forall |x: int, y: int, z: int| x <= y && 0 < z implies #[trigger](x / z) <= #[trigger](y / z) by
    {
        lemma_div_is_ordered(x, y, z);
    }
}

/// Proof that dividing an integer by 2 or more results in a quotient
/// that is smaller than the original dividend. Specifically, `x / d < x`.
pub proof fn lemma_div_decreases(x: int, d: int)
    requires 
        0 < x,
        1 < d,
    ensures 
        x / d  < x
{
    lemma_div_induction_auto(d, x, |u: int| 0 < u ==> u / d < u);
}

/// Proof that dividing an integer by 2 or more results in a quotient
/// that is smaller than the original dividend
pub proof fn lemma_div_decreases_auto()
    ensures 
        forall |x: int, d: int| 0 < x && 1 < d ==> #[trigger](x / d) < x,
{
    assert forall |x: int, d: int| 0 < x && 1 < d implies #[trigger](x / d) < x by
    {
        lemma_div_decreases(x, d);
    };
}

/// Proof that dividing an integer by 1 or more results in a quotient
/// that is less than or equal to the original dividend. Specifically,
/// `x / d <= x`.
pub proof fn lemma_div_nonincreasing(x: int, d: int)
    requires 
        0 <= x,
        0 < d,
    ensures 
        x / d  <= x
{
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u / d <= u);
}

/// Proof that dividing an integer by 1 or more results in a quotient
/// that is less than or equal to the original dividend
proof fn lemma_div_nonincreasing_auto()
    ensures forall |x: int, d: int| 0 <= x && 0 < d ==> #[trigger](x / d) <= x,
{
    assert forall |x: int, d: int| 0 <= x && 0 < d implies #[trigger](x / d) <= x by
    {
        lemma_div_nonincreasing(x, d);
    }
}

/// Proof that a natural number x divided by a larger natural number
/// gives a remainder equal to x. Specifically, because `x < m`, we
/// know `x % m == x`.
pub proof fn lemma_small_mod(x: nat, m: nat)
    requires 
        x < m,
        0 < m
    ensures 
        x % m == x
{
    ModINL::lemma_small_mod(x, m);
}

/// The remainder of a nonnegative integer `x` divided by the product of two positive integers
/// `y` and `z` is equivalent to dividing `x` by `y`, dividing the quotient by `z`, multiplying
/// the remainder by `y`, and then adding the product to the remainder of `x` divided by `y`.
/// In mathematical terms, `(x % (y * z)) == y * ((x / y) % z) + x % y`.
pub proof fn lemma_breakdown(x: int, y: int, z: int)
    requires 
        0 <= x,
        0 < y,
        0 < z,
    ensures 
        0 < y * z,
        (x % (y * z)) == y * ((x / y) % z) + x % y,
{
    lemma_mul_strictly_positive_auto();
    lemma_div_pos_is_pos(x, y);

    calc! {
        (<)
        (y * (x / y)) % (y * z) + (x % y) % (y * z);
        (<=)    { lemma_part_bound1(x, y, z); }
        y * (z - 1) + (x % y) % (y * z);
        (<)    { lemma_part_bound2(x, y, z); }
        y * (z - 1) + y;
        (==)    { lemma_mul_basics_auto(); }
        y * (z - 1) + y * 1;
        (==)    { lemma_mul_is_distributive_auto(); }
        y * (z - 1 + 1);
        (==) {}
        y * z;
    }

    calc! {
        (==)
        x % (y * z);
        { ModINL::lemma_fundamental_div_mod(x,y); }
        (y * (x / y) + x % y) % (y * z);
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
            // comparison op can't be chained in calc!
            // assert forall is also not avaialable in calc!
            assert((x % y) < y && y <= (y * z)); 
            lemma_small_mod((x % y) as nat, (y * z) as nat);
            assert((x % y) % (y * z) == x % y);
        }
        (y * (x / y)) % (y * z) + x % y;
        { lemma_truncate_middle(x / y, y, z); }
        y * ((x / y) % z) + x % y;
    }
}

/// Proof that, for all `x`, `y`, and `z`, `(x % (y * z)) == y * ((x / y) % z) + x % y`
pub proof fn lemma_breakdown_auto()
    ensures
        forall |y: int, z: int| #![trigger y * z] 0 < y && 0 < z ==> 0 < y * z,
        forall |x: int, y: int, z: int| #![trigger y * z, x % (y * z), y * ((x / y) % z) + x % y]
                0 <= x && 0 < y && 0 < z ==> x % (y * z) == y * ((x / y) % z) + x % y,
{
    assert forall |y: int, z: int| #![trigger y * z] 0 < y && 0 < z implies 0 < y * z by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall |x: int, y: int, z: int| #![trigger y * z, x % (y * z), y * ((x / y) % z) + x % y]
               0 <= x && 0 < y && 0 < z implies x % (y * z) == y * ((x / y) % z) + x % y by {
        lemma_breakdown(x, y, z);
    }
}

/// Proof that the difference between a nonnegative integer `x` and a
/// positive integer `d` must be strictly less than the quotient of
/// `x` divided by `d` and then multiplied by `d`
pub proof fn lemma_remainder_upper(x: int, d: int)
    requires 
        0 <= x,
        0 < d,
    ensures 
        x - d < x / d * d
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u - d < u / d * d);
}

/// Proof that for any nonnegative integer `x` and positive integer
/// `d`, their difference `x - d` must be strictly less than the
/// quotient of `x` divided by `d` and then multiplied by `d`
pub proof fn lemma_remainder_upper_auto()
    ensures forall |x: int, d: int| #![trigger (x - d), (x / d * d)] 0 <= x && 0 < d ==> (x - d) < (x / d * d)
{
    assert forall |x: int, d: int| 0 <= x && 0 < d implies #[trigger](x - d) < #[trigger](x / d * d) by
    {
        lemma_remainder_upper(x, d);
    }
}

/// Proof that the division of a nonnegative integer `x` by a positive
/// integer `d` multiplied by `d` is less than or equal to the value
/// of `x`.
pub proof fn lemma_remainder_lower(x: int, d: int)
    requires 
        0 <= x,
        0 < d
    ensures
        x >= x / d * d
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u >= u / d * d);
}

/// Proof that, for all nonnegative `x` and positive `d`, `(x / d) * d <= x`
pub proof fn lemma_remainder_lower_auto()
    ensures
        forall |x: int, d: int| 0 <= x && 0 < d ==> x >= #[trigger](x / d * d)
{
    assert forall |x: int, d: int| (0 <= x && 0 < d) implies x >= #[trigger](x / d * d) by
    {
        lemma_remainder_lower(x, d);
    }
}

/// Proof that the difference between a nonnegative integer `x` and
/// the division of `x` by a positive integer `d` multiplied by `d` is
/// lower bounded (inclusively) by 0 and upper bounded (exclusively)
/// by `d`
pub proof fn lemma_remainder(x: int, d: int)
    requires 
        0 <= x,
        0 < d,
    ensures
        0 <= x - (x / d * d) < d
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x,|u: int| 0 <= u - u / d * d < d);
}

/// Proof that, for any nonnegative integer `x` and positive `d`,
/// `0 <= (x - (x / d * d)) < d`
pub proof fn lemma_remainder_auto()
    ensures 
        forall |x: int, d: int| 0 <= x && 0 < d ==> 0 <= #[trigger](x - (x / d * d)) < d,
{
    assert forall |x: int, d: int| 0 <= x && 0 < d implies 0 <= #[trigger](x - (x / d * d)) < d by
    {
        lemma_remainder(x, d);
    }
}

/// Proof of the fundamental theorem of division and modulo, namely
/// that `x` can be expressed as `d` times the quotient `x / d` plus
/// the remainder `x % d`.
pub proof fn lemma_fundamental_div_mod(x: int, d: int)
    requires d != 0
    ensures x == d * (x / d) + (x % d)
{
    ModINL::lemma_fundamental_div_mod(x, d);
}

/// Proof of the fundamental theorem of division and modulo, namely
/// that for any `x` and nonzero `d`, `x == d * (x / d) + x % d`
pub proof fn lemma_fundamental_div_mod_auto()
    ensures forall |x: int, d: int| d != 0 ==> x == #[trigger](d * (x / d) + (x % d))
{
    assert forall |x: int, d: int| d != 0 implies x == #[trigger](d * (x / d) + (x % d)) by
    {
        lemma_fundamental_div_mod(x, d);
    }
}

/// Proof that dividing `x` by `c * d` is equivalent to first dividing
/// `x` by `c` and then dividing the result by `d`
pub proof fn lemma_div_denominator(x: int, c: int, d: int)
    requires 
        0 <= x,
        0 < c,
        0 < d
    ensures 
        c * d != 0,
        (x / c) / d == x / (c * d)
{
    lemma_mul_strictly_positive(c, d);
    let r = x % (c as int * d as int);

    lemma_div_pos_is_pos(r, c as int);
    if (r / c as int >= d) {
        ModINL::lemma_fundamental_div_mod(r, c as int);
        lemma_mul_inequality(d as int, r / c as int, c as int);
        lemma_mul_is_commutative(d, c);
    }
    assert(r / (c as int) < d);

    lemma_fundamental_div_mod_converse(r / c, d, 0, r / c);

    assert((r / c as int) % d as int == r / c as int);

    lemma_fundamental_div_mod(r, c);
    assert(c * (r / c) + r % c == r);
    
    assert(c * ((r / c as int) % d as int) + r % c as int == r);
    
    let k = x / (c as int * d as int);
    lemma_fundamental_div_mod(x, c * d);
    assert(x == (c * d) * (x / (c * d)) + x % (c * d));
    assert(r == x - (c * d) * (x / (c * d)));
    assert(r == x - (c * d) * k);

    calc! {
        (==)
        c * ((x / c) % d) + x % c;
        {
            lemma_mod_multiples_vanish(-k, x / c, d);
            lemma_mul_is_commutative_auto();
        }
        c * ((x / c + (-k) * d) % d) + x % c;
        { lemma_hoist_over_denominator(x, (-k) * d, c as nat); }
        c * (((x + (((-k) * d) * c)) / c) % d) + x % c;
        { lemma_mul_is_associative(-k, d, c); }
        c * (((x + ((-k) * (d * c))) / c) % d) + x % c;
        { lemma_mul_unary_negation(k, d * c); }
        c * (((x + (-(k * (d * c)))) / c) % d) + x % c;
        { lemma_mul_is_associative(k, d, c); }
        c * (((x + (-(k * d * c))) / c) % d) + x % c;
        { }
        c * (((x - k * d * c) / c) % d) + x % c;
        {
            lemma_mul_is_associative_auto();
            lemma_mul_is_commutative_auto();
        }
        c * ((r / c) % d) + x % c;
        { }
        c * (r / c) + x % c;
        {
            lemma_fundamental_div_mod(r, c);
            assert(r == c * (r / c) + r % c);
            lemma_mod_mod(x, c, d);
            assert(r % c == x % c);
        }
        r;
        { lemma_mod_properties_auto(); lemma_mod_is_mod_recursive_auto(); }
        r % (c * d);
        { }
        (x - (c * d) * k) % (c * d);
        { lemma_mul_unary_negation(c * d, k); }
        (x + (c * d) * (-k)) % (c * d);
        { lemma_mod_multiples_vanish(-k, x, c * d); }
        x % (c * d);
    }
    
    assert (c * (x / c) + x % c - r == c * (x / c) - c * ((x / c) % d) ==>
            x - r == c * (x / c) - c * ((x / c) % d)) by {
        lemma_fundamental_div_mod(x, c);
    };

    assert(c * (x / c) + x % c - r == c * (x / c) - c * ((x / c) % d));
    assert(x - r == c * (x / c) - c * ((x / c) % d));
    
    assert((x / c) / d == x / (c * d)) by {
        lemma_fundamental_div_mod(x / c, d);
        assert(d * ((x / c) / d) == x / c - ((x / c) % d));
        lemma_fundamental_div_mod(x, c * d);
        assert(x == (c * d) * (x / (c * d)) + (x % (c * d)));
        lemma_mul_is_distributive_sub(c, x / c, (x / c) % d);
        assert(c * (d * ((x / c) / d)) == c * (x / c) - c * ((x / c) % d));
        lemma_mul_is_associative(c, d, (x / c) / d);
        assert((c * d) * ((x / c) / d) == c * (x / c) - c * ((x / c) % d));
        assert((c * d) * ((x / c) / d) == x - r);
        assert((c * d) * ((x / c) / d) == (c * d) * (x / (c * d)));
        lemma_mul_equality_converse(c * d, (x / c) / d, x / (c * d));
    }

    assert(c * d != 0) by {
        assert(0 < c * d);
    }
}

/// Proof that dividing a fraction by a divisor is equivalent to multiplying the fraction's 
/// denominator by the divisor
pub proof fn lemma_div_denominator_auto()
    ensures
        forall |c: int, d: int| 0 < c && 0 < d ==> #[trigger](c * d) != 0,
        forall |x: int, c: int, d: int| 0 <= x && 0 < c && 0 < d ==> #[trigger]((x / c) / d) == x / (c * d),
{
    lemma_mul_nonzero_auto();
    assert forall |x: int, c: int, d: int| 0 <= x && 0 < c && 0 < d implies #[trigger]((x / c) / d) == x / (c * d) by
    {
        lemma_div_denominator(x, c, d);
    }
}

/// Proof that multiplying an integer by a fraction is equivalent to
/// multiplying the fraction's numerator by the integer. Specifically,
/// `x * (y / z) == (x * y) / z`.
pub proof fn lemma_mul_hoist_inequality(x: int, y: int, z: int)
    requires 
        0 <= x,
        0 < z
    ensures x * (y / z) <= (x * y) / z
{
    calc! {
    (==)
    (x * y) / z;
    (==)   { lemma_fundamental_div_mod(y, z); }
    (x * (z * (y / z) + y % z)) / z;
    (==)    { lemma_mul_is_distributive_auto(); }
    (x * (z * (y / z)) + x * (y % z)) / z;
    }

    assert ((x * (z * (y / z)) + x * (y % z)) / z >=  x * (y / z)) by {
        lemma_mod_properties_auto();
        lemma_mul_nonnegative(x, y % z);
        lemma_div_is_ordered(x * (z * (y / z)), x * (z * (y / z)) + x * (y % z), z);
        lemma_mul_is_associative_auto();
        lemma_mul_is_commutative_auto();
        lemma_div_multiples_vanish(x * (y / z), z);
    };
}

/// Proof that multiplying an integer by a fraction is equivalent to
/// multiplying the fraction's numerator by the integer
pub proof fn lemma_mul_hoist_inequality_auto()
    ensures
        forall |x: int, y: int, z: int| #![trigger (x * (y / z)), ((x * y) / z)] 0 <= x && 0 < z ==> (x * (y / z)) <= ((x * y) / z),
{
    assert forall |x: int, y: int, z: int| 0 <= x && 0 < z implies #[trigger](x * (y / z)) <= #[trigger]((x * y) / z) by
    {
        lemma_mul_hoist_inequality(x, y, z);
    }
}

/// Proof that for a positive integer `d`, if `a - a % d` is less than
/// or equal to `b` and `b` is less than `a + d - a % d`, then the
/// quotient of `a` divided by `d` is equivalent to the quotient of
/// `b` divided by `d`.
/// 
/// In other words, if `a` and `b` occur between the same two
/// multiples of `d`, then their quotient with `d` is equivalent.
pub proof fn lemma_indistinguishable_quotients(a: int, b: int, d: int)
    requires
        0 < d,
        0 <= a - a % d <= b < a + d - a % d,
    ensures a / d == b / d
{
    lemma_div_induction_auto(d, a - b, |ab: int| {let u = ab + b; 0 <= u - u % d <= b < u + d - u % d ==> u / d == b / d});
}

/// Proof that for any `a`, `b`, and positive integer `d`, if `a - a %
/// d` is less than or equal to `b` and `b` is less than `a + d - a %
/// d`, then the quotient of `a` divided by `d` is equivalent to the
/// quotient of `b` divided by `d`.
/// 
/// In other words, if `a` and `b` occur between the same two
/// multiples of `d`, then their quotient with `d` is equivalent.
pub proof fn lemma_indistinguishable_quotients_auto()
    ensures
        forall |a: int, b: int, d: int| #![trigger (a / d), (b / d)] 0 < d && 0 <= a - a % d <= b < a + d - a % d ==> (a / d) == (b / d)
{
    assert forall |a: int, b: int, d: int| 0 < d && 0 <= a - a % d <= b < a + d - a % d implies #[trigger](a / d) == #[trigger](b / d) by
    {
        lemma_indistinguishable_quotients(a, b, d);
    }
}

/// Proof that common factors from the dividend and divisor of a modulus operation can be factored out.
/// Specifically, `(b * x) % (b * c) == b * (x % c)`.
pub proof fn lemma_truncate_middle(x: int, b: int, c: int)
    requires 
        0 <= x,
        0 < b,
        0 < c,
    ensures
        0 < b * c,
        (b * x) % (b * c) == b * (x % c)
{
    lemma_mul_strictly_positive_auto();
    lemma_mul_nonnegative_auto();
    calc! {
    (==)
    b * x;
    { ModINL::lemma_fundamental_div_mod(b * x, b * c); }
    (b * c) * ((b * x) / (b * c)) + (b * x) % (b * c);
    { lemma_div_denominator(b * x, b, c); }
    (b * c) * (((b * x) / b) / c) + (b * x) % (b * c);
    { lemma_mul_is_commutative_auto(); lemma_div_by_multiple(x, b); }
    (b * c) * (x / c) + (b * x) % (b * c);
    }

    assert(b * x == (b * c) * (x / c) + b * (x % c)) by {
        ModINL::lemma_fundamental_div_mod(x, c);
        lemma_mul_is_distributive_auto();
        lemma_mul_is_associative_auto();
    };
}

/// Proof that common factors from the dividend and divisor of a modulus operation can be factored out
pub proof fn lemma_truncate_middle_auto()
    ensures forall |x: int, b: int, c: int| #![trigger (b * (x % c))] 0 <= x && 0 < b && 0 < c && 0 < b * c ==> (b * x) % (b * c) == b * (x % c)
{
    assert forall |x: int, b: int, c: int| 0 <= x && 0 < b && 0 < c && 0 < b * c implies #[trigger](b * (x % c)) == ((b * x) % (b * c)) by
    {
        lemma_truncate_middle(x, b, c);
    }
}

/// Proof that multiplying the numerator and denominator by an integer does not change the quotient.
/// Specifically, `a / d == (x * a) / (x * d)`.
pub proof fn lemma_div_multiples_vanish_quotient(x: int, a: int, d: int)
    requires
        0 < x,
        0 <= a,
        0 < d,
    ensures
        0 < x * d,
        a / d == (x * a) / (x * d),
{
    lemma_mul_strictly_positive(x,d);
    calc! { (==)
        (x * a) / (x * d);
        {
            lemma_mul_nonnegative(x, a);
            lemma_div_denominator(x * a, x, d); 
        }
        ((x * a) / x) / d;
        { lemma_div_multiples_vanish(a, x); }
        a / d;
    }
}

/// Proof that multiplying the numerator and denominator by an integer does not change the quotient
pub proof fn lemma_div_multiples_vanish_quotient_auto()
    ensures
        forall |x: int, d: int| #![trigger x * d] 0 < x && 0 < d ==> 0 < x * d,
        forall |x: int, a: int, d: int| #![trigger a / d, x * a, x * d]
            0 < x && 0 <= a && 0 < d ==> a / d == (x * a) / (x * d),
{
    assert forall |x: int, d: int| #![trigger x * d] 0 < x && 0 < d implies 0 < x * d by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall |x: int, a: int, d: int| #![trigger a / d, x * a, x * d]
               0 < x && 0 <= a && 0 < d implies a / d == (x * a) / (x * d) by {
        lemma_div_multiples_vanish_quotient(x, a, d);
    }
}

/// Proof that, since `a % d == 0` and `0 <= r < d`, we can conclude
/// `a == d * (a + r) / d`.
pub proof fn lemma_round_down(a: int, r: int, d: int)
    requires
        0 < d,
        a % d == 0,
        0 <= r < d,
    ensures
        a == d * ((a + r) / d),
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, a, |u: int| u % d == 0 ==> u == d * ((u + r) / d));
}

/// Proof that for all `a`, `d`, and `r`, if `a % d == 0` and `0 <= r
/// < d`, then `a == d * (a + r) / d`.
pub proof fn lemma_round_down_auto()
    ensures forall |a: int, r: int, d: int| #![trigger (d * ((a + r) / d))] 0 < d && a % d == 0 && 0 <= r < d ==> a == d * ((a + r) / d),
{
    assert forall |a: int, r: int, d: int| 0 < d && a % d == 0 && 0 <= r < d implies #[trigger](d * ((a + r) / d)) == a by
    {
        lemma_round_down(a, r, d);
    }
}

/// Proof that, since `0 <= b < d`, we have `(d * x + b) / d == x`.
pub proof fn lemma_div_multiples_vanish_fancy(x: int, b: int, d: int)
    requires 
        0 < d,
        0 <= b < d,
    ensures 
        (d * x + b) / d == x
{
    let f = |u: int| (d * u + b) / d == u;
  
    assert(f(0)) by { lemma_div_auto(d); }
    assert forall |i: int| i >= 0 && #[trigger] f(i) implies #[trigger] f(add1(i, 1)) by {
        assert(d * (i + 1) + b == d * i + b + d) by {
            assert(d * (i + 1) == d * i + d) by {
                lemma_mul_is_distributive_add(d, i, 1);
                lemma_mul_basics(d);
            }
        }
        crate::nonlinear_arith::internals::div_internals::lemma_div_basics(d);
    }
    assert forall |i: int| i <= 0 && #[trigger] f(i) implies #[trigger] f(sub1(i, 1)) by {
        assert(d * (i - 1) + b == d * i + b - d) by {
            assert(d * (i - 1) == d * i - d) by {
                lemma_mul_is_distributive_sub(d, i, 1);
                lemma_mul_basics(d);
            }
        }
        crate::nonlinear_arith::internals::div_internals::lemma_div_basics(d);
    }
    lemma_mul_auto();
    lemma_mul_induction(f);
    assert(f(x));
}

/// Proof that, for any `x`, `b`, and `d` satisfying `0 <= b < d`, we have `(d * x + b) / d == x`
pub proof fn lemma_div_multiples_vanish_fancy_auto()
    ensures forall |x: int, b: int, d: int| #![trigger (d * x + b) / d] 0 < d && 0 <= b < d ==> (d * x + b) / d == x,
{
    assert forall |x: int, b: int, d: int| 0 < d && 0 <= b < d implies #[trigger]((d * x + b) / d) == x by
    {
        lemma_div_multiples_vanish_fancy(x, b, d);
    }
}

/// Proof that multiplying an integer by a common numerator and
/// denominator results in the original integer. Specifically,
/// `(d * x) / d == x`.
pub proof fn lemma_div_multiples_vanish(x: int, d: int)
    requires 0 < d
    ensures (d * x) / d == x
{
    lemma_div_multiples_vanish_fancy(x, 0, d);
}

/// Proof that multiplying an integer by a common numerator and
/// denominator results in the original integer
pub proof fn lemma_div_multiples_vanish_auto()
    ensures forall |x: int, d: int| #![trigger (d * x) / d] 0 < d ==> (d * x) / d == x,
{
    assert forall |x: int, d: int| 0 < d implies #[trigger]((d * x) / d) == x by
    {
        lemma_div_multiples_vanish(x, d);
    }
}

/// Proof that multiplying a whole number by a common numerator and
/// denominator results in the original integer. Specifically,
/// `(b * d) / d == b`.
pub proof fn lemma_div_by_multiple(b: int, d: int)
    requires
        0 <= b,
        0 < d,
    ensures
        (b * d) / d == b
{
    lemma_div_multiples_vanish(b, d);
    lemma_mul_auto();
}

/// Proof that multiplying a whole number by a common numerator and
/// denominator results in the original integer
pub proof fn lemma_div_by_multiple_auto()
    ensures forall |b: int, d: int| #![trigger ((b * d) / d)] 0 <= b && 0 < d ==> (b * d) / d == b,
{
    assert forall |b: int, d: int| 0 <= b && 0 < d implies #[trigger]((b * d) / d) == b by
    {
        lemma_div_by_multiple(b, d);
    }
}

/// Proof that a dividend that is a positive multiple of a divisor
/// will always yield a greater quotient than a smaller dividend.
/// Specifically, `x / z < y / z` because `y == m * z` and `x < y`.
pub proof fn lemma_div_by_multiple_is_strongly_ordered(x: int, y: int, m: int, z: int)
    requires
        x < y,
        y == m * z,
        0 < z,
    ensures
        x / z < y / z
{
    lemma_mod_multiples_basic(m, z);
    lemma_div_induction_auto(z, y - x, |yx: int| {let u = yx + x; x < u && u % z == 0 ==> x / z < u / z});
}

/// Proof that a dividend that is a positive multiple of a divisor
/// will always yield a greater quotient than a smaller dividend
pub proof fn lemma_div_by_multiple_is_strongly_ordered_auto()
    ensures forall |x: int, y: int, m: int, z: int| #![trigger x / z, m * z, y / z] x < y && y == m * z && 0 < z ==> x / z < y / z,
{
    assert forall |x: int, y: int, m: int, z: int| x < y && y == #[trigger](m * z) && 0 < z implies #[trigger](x / z) < #[trigger](y / z) by
    {
        lemma_div_by_multiple_is_strongly_ordered(x, y, m, z);
    }
}

/// Proof that if an integer is less than or equal to the product of
/// two other integers, then the quotient with one of them will be
/// less than or equal to the other of them. Specifically, because
/// `a <= b * c`, we know `a / b <= c`.
pub proof fn lemma_multiply_divide_le(a: int, b: int, c: int)
    requires
        0 < b,
        a <= b * c,
    ensures
        a / b <= c
{
    lemma_mod_multiples_basic(c, b);
    let f = |i: int| 0 <= i && (i + a) % b == 0 ==> a / b <= (i + a) / b;
    lemma_div_induction_auto(b, b * c - a, f);
    lemma_div_multiples_vanish(c, b);
}

/// Proof that if an integer is less than or equal to the product of
/// two other integers, then the quotient with one of them will be
/// less than or equal to the other of them
proof fn lemma_multiply_divide_le_auto()
    ensures forall |a: int, b: int, c: int| #![trigger a / b, b * c] 0 < b && a <= b * c ==> a / b <= c,
{
    assert forall |a: int, b: int, c: int| 0 < b && a <= #[trigger](b * c) implies #[trigger](a / b) <= c by
    {
        lemma_multiply_divide_le(a, b, c);
    }
}

/// Proof that if an integer is less than the product of two other
/// integers, then the quotient with one of them will be less than the
/// other. Specifically, because `a < b * c`, we know `a / b < c`.
pub proof fn lemma_multiply_divide_lt(a: int, b: int, c: int)
    requires 
        0 < b,
        a < b * c,
    ensures
        a / b < c
{
    assert(((b * c - a) + a) % b == 0 ==> a / b < ((b * c - a) + a) / b) by {
        let f = |i: int| 0 < i && (i + a) % b == 0 ==> a / b < (i + a) / b;
        lemma_div_induction_auto(b, b * c - a, f);
    }
    assert(b * c == c * b) by {
        lemma_mul_is_commutative(b, c);
    }
    assert((b * c) % b == 0) by {
        lemma_mod_multiples_basic(c, b);
    }
    assert((b * c) / b == c) by {
        lemma_div_multiples_vanish(c, b);
    }
}

/// Proof that if an integer is less than the product of two other
/// integers, then the quotient with one of them will be less than the
/// other
pub proof fn lemma_multiply_divide_lt_auto()
    ensures forall |a: int, b: int, c: int| #![trigger a / b, b * c] 0 < b && a < b * c ==> a / b < c,
{
    assert forall |a: int, b: int, c: int| 0 < b && a < #[trigger](b * c) implies #[trigger](a / b) < c by
    {
        lemma_multiply_divide_lt(a, b, c);
    }
}

/// Proof that adding an integer to a fraction is equivalent to adding
/// that integer times the denominator to the numerator. Specifically,
/// `x / d + j == (x + j * d) / d`.
pub proof fn lemma_hoist_over_denominator(x: int, j: int, d: nat)
    requires 0 < d
    ensures x / d as int + j == (x + j * d) / d as int
{
    lemma_div_auto(d as int);
    let f = |u: int| x / d as int + u == (x + u * d) / d as int;
    // OBSERVE: push precondition on its on scope
    assert (  f(0)
        && (forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger]f(add1(i, 1)))
        && (forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger]f(sub1(i, 1)))) by {
            lemma_mul_auto();
    }
    lemma_mul_induction(f);
    assert(f(j));
}

/// Proof that adding an integer to a fraction is equivalent to adding
/// that integer times the denominator to the numerator
pub proof fn lemma_hoist_over_denominator_auto()
    ensures forall |x: int, j: int, d: nat| #![trigger x / d as int + j] 0 < d ==> x / d as int + j == (x + j * d) / d as int,
{
    assert forall |x: int, j: int, d: nat| 0 < d implies #[trigger](x / d as int + j) == (x + j * d) / d as int by
    {
        lemma_hoist_over_denominator(x, j, d);
    }
}

/// Proof that, for nonnegative integer `a` and positive integers `b` and `c`, 
/// the remainder of `b * (a / b)` divided by `b * c` is less than or equal to `b * (c - 1)`.
/// This accounts for the rounding down that occurs in integer division.
pub proof fn lemma_part_bound1(a: int, b: int, c: int)
    requires 
        0 <= a,
        0 < b,
        0 < c,
    ensures
        0 < b * c,
        (b * (a / b) % (b * c)) <= b * (c - 1)
{
    lemma_mul_strictly_positive_auto();
    calc! {
        (==)
        b * (a / b) % (b * c);
        { ModINL::lemma_fundamental_div_mod(b * (a / b), b * c); }
        b * (a / b) - (b * c) * ((b * (a / b)) / (b * c));
        { lemma_mul_is_associative_auto(); }
        b * (a / b) - b * (c * ((b * (a / b)) / (b * c)));
        { lemma_mul_is_distributive_auto(); }
        b * ((a / b) - (c * ((b * (a / b)) / (b * c))));
    }

    assert(b * (a / b) % (b * c) <= b * (c - 1)) by
        { lemma_mul_is_commutative_auto(); lemma_mul_inequality_auto(); };
}

/// Proof that, for any nonnegative integer `a` and positive integers `b` and `c`, 
/// the remainder of `b * (a / b)` divided by `b * c` is less than or equal to `b * (c - 1)`.
/// This accounts for the rounding down that occurs in integer division.
pub proof fn lemma_part_bound1_auto()
    ensures
        forall |b: int, c: int| #![trigger b * c] 0 < b && 0 < c ==> 0 < b * c,
        forall |a: int, b: int, c: int| #![trigger (b * (a / b) % (b * c))] 0 <= a && 0 < b && 0 < c ==> b * (a / b) % (b * c) <= b * (c - 1),
{
    assert forall |b: int, c: int| #![trigger b * c] 0 < b && 0 < c implies 0 < b * c by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall |a: int, b: int, c: int| #![trigger (b * (a / b) % (b * c))]
        0 <= a && 0 < b && 0 < c implies
        b * (a / b) % (b * c) <= b * (c - 1) by
    {
        lemma_part_bound1(a, b, c);
    }
}

}
