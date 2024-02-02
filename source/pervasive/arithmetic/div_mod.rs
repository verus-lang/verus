//! This file contains proofs related to integer division (`/`) and
//! remainder aka mod (`%`). These are part of the math standard library.
//!
//! It's based on the following file from the Dafny math standard
//! library:
//! `Source/DafnyStandardLibraries/src/Std/Arithmetic/DivMod.dfy`.
//! That file has the following copyright notice:
//! /*******************************************************************************
//! * Original: Copyright (c) Microsoft Corporation *
//! SPDX-License-Identifier: MIT * * Modifications and Extensions:
//! Copyright by the contributors to the Dafny Project *
//! SPDX-License-Identifier: MIT
//! *******************************************************************************/
use crate::calc_macro::*;
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus! {

#[allow(unused_imports)]
use crate::arithmetic::internals::div_internals::{
    div_recursive,
    lemma_div_induction_auto,
    div_auto,
    div_pos,
    lemma_div_auto,
};
use crate::arithmetic::internals::div_internals_nonlinear as DivINL;
use crate::arithmetic::internals::mod_internals::{
    lemma_div_add_denominator,
    lemma_mod_auto,
    mod_recursive,
};
use crate::arithmetic::internals::mod_internals_nonlinear as ModINL;
use crate::arithmetic::internals::mul_internals::{
    lemma_mul_auto,
    lemma_mul_induction,
    lemma_mul_induction_auto,
};
use crate::arithmetic::internals::general_internals::{is_le};
use crate::arithmetic::math::{add as add1, sub as sub1, div as div1};
use crate::arithmetic::mul::*;

/*****************************************************************************
   * Division:
   *****************************************************************************/

/// Proof that, for the case of `x / d`, division using `/` is
/// equivalent to division using [`div_recursive`]
pub proof fn lemma_div_is_div_recursive(x: int, d: int)
    requires
        0 < d,
    ensures
        div_recursive(x, d) == x / d,
{
    reveal(div_recursive);
    reveal(div_pos);
    lemma_div_induction_auto(d, x, |u: int| div_recursive(u, d) == u / d);
}

/// Proof that division using `/` is equivalent to division using
/// [`div_recursive`] as long as the divisor is positive
pub proof fn lemma_div_is_div_recursive_auto()
    ensures
        forall|x: int, d: int|
            d > 0 ==> div_recursive(x, d) == #[trigger]
            (x / d),
{
    reveal(div_recursive);
    assert forall|x: int, d: int| d > 0 implies div_recursive(x, d) == #[trigger]
    (x / d) by {
        lemma_div_is_div_recursive(x, d);
    }
}

/// Proof that the quotient of an integer divided by itself is 1,
/// specifically that `d / d == 1`
pub proof fn lemma_div_by_self(d: int)
    requires
        d != 0,
    ensures
        d / d == 1,
{
    DivINL::lemma_div_by_self(d);
}

/// Proof that 0 divided by a nonzero integer is 0, specifically `0 / d == 0`
pub proof fn lemma_div_of0(d: int)
    requires
        d != 0,
    ensures
        0 as int / d == 0,
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
        forall|x: int|
            x != 0 ==> #[trigger]
            (0int / x) == 0,
        forall|x: int| #[trigger] (x / 1) == x,
        forall|x: int, y: int|
            x >= 0 && y > 0 ==> #[trigger]
            (x / y) >= 0,
        forall|x: int, y: int|
            x >= 0 && y > 0 ==> #[trigger]
            (x / y) <= x,
{
    assert forall|x: int| x != 0 implies #[trigger]
    (0int / x) / x == 0 by {
        lemma_div_basics(x);
    };
    assert forall|x: int| x != 0 implies #[trigger]
    (x / 1) == x by {
        lemma_div_basics(x);
    };
    assert forall|x: int, y: int| x >= 0 && y > 0 implies 0 <= #[trigger]
    (x / y) <= x by {
        lemma_div_pos_is_pos(x, y);
        lemma_div_is_ordered_by_denominator(x, 1, y);
    };
}

/// Proof that if a dividend is a whole number, the divisor is a
/// natural number, and their quotient is 0, then the dividend is
/// smaller than the divisor
// #[verifier::spinoff_prover]
pub proof fn lemma_small_div_converse_auto()
    ensures
        forall|x: int, d: int|
            0 <= x && 0 < d && #[trigger]
            (x / d) == 0 ==> x < d,
{
    assert forall|x: int, d: int|
        0 <= x && 0 < d && #[trigger]
        (x / d) == 0 implies x < d by {
        lemma_div_induction_auto(d, x, |u: int| 0 <= u && 0 < d && u / d == 0 ==> u < d);
    }
}

/// Proof that division of a positive integer by a positive integer
/// less than or equal to it is nonzero. Specifically, given that `x
/// >= d`, we can conclude that `x / d > 0`.
pub proof fn lemma_div_non_zero(x: int, d: int)
    requires
        x >= d > 0,
    ensures
        x / d > 0,
{
    lemma_div_pos_is_pos_auto();
    if x / d == 0 {
        lemma_small_div_converse_auto();
    }
}

/// Proof that division of a positive integer by a positive integer
/// less than or equal to it is nonzero
pub proof fn lemma_div_non_zero_auto()
    ensures
        forall|x: int, d: int|
            x >= d > 0 ==> #[trigger]
            (x / d) > 0,
{
    assert forall|x: int, d: int| x >= d > 0 implies #[trigger]
    (x / d) > 0 by {
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
        1 <= y <= z,
    ensures
        x / y >= x / z,
    decreases x,
{
    reveal(div_recursive);
    reveal(div_pos);
    lemma_div_is_div_recursive_auto();
    assert(forall|u: int, d: int|
        #![trigger div_recursive(u, d)]
        #![trigger div1(u, d)]
        d > 0 ==> div_recursive(u, d) == div1(u, d));
    if (x < z) {
        lemma_div_is_ordered(0, x, y);
    } else {
        lemma_div_is_ordered(x - z, x - y, y);
        lemma_div_is_ordered_by_denominator(x - z, y, z);
    }
}

/// Proof that given two fractions with the same numerator, the order
/// of the fractions is determined by the denominators. However, if
/// the numerator is 0, the fractions are equal regardless of the
/// denominators' values.
pub proof fn lemma_div_is_ordered_by_denominator_auto()
    ensures
        forall|x: int, y: int, z: int|
            0 <= x && 1 <= y <= z ==> #[trigger]
            (x / y) >= #[trigger]
            (x / z),
{
    assert forall|x: int, y: int, z: int| 0 <= x && 1 <= y <= z implies #[trigger]
    (x / y) >= #[trigger]
    (x / z) by {
        lemma_div_is_ordered_by_denominator(x, y, z);
    }
}

/// Proof that a number gets strictly smaller when divided by a number
/// greater than one. Specifically, `x / d < x`.
pub proof fn lemma_div_is_strictly_smaller(x: int, d: int)
    requires
        0 < x,
        1 < d,
    ensures
        x / d < x,
    decreases x,
{
    lemma_div_induction_auto(d, x, |u: int| 0 < u ==> u / d < u);
}

/// Proof that a number gets strictly smaller when divided by a number
/// greater than one
pub proof fn lemma_div_is_strictly_smaller_auto()
    ensures
        forall|x: int, d: int|
            0 < x && 1 < d ==> #[trigger]
            (x / d) < x,
{
    assert forall|x: int, d: int| 0 < x && 1 < d implies #[trigger]
    (x / d) < x by {
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
        d * ((a + b) / d) - r == d * (a / d) + d * (b / d),
{
    ModINL::lemma_fundamental_div_mod(a + b, d);
    ModINL::lemma_fundamental_div_mod(a, d);
    ModINL::lemma_fundamental_div_mod(b, d);
}

/// Proof that for any values of the following variables, `r == a % d
/// + b % d - (a + b) % d` implies `r == d * ((a + b) / d) - d * (a /
/// d) - d * (b / d)`.
pub proof fn lemma_dividing_sums_auto()
    ensures
        forall|a: int, b: int, d: int, r: int|
            #![trigger (d * ((a + b) / d) - r), (d * (a / d) + d * (b / d))]
            0 < d && r == a % d + b % d - (a + b) % d ==> d * ((a + b) / d) - r == d * (a / d) + d
                * (b / d),
{
    assert forall|a: int, b: int, d: int, r: int|
        0 < d && r == a % d + b % d - (a + b) % d implies #[trigger]
    (d * ((a + b) / d) - r) == #[trigger]
    (d * (a / d) + d * (b / d)) by {
        lemma_dividing_sums(a, b, d, r);
    }
}

/// Proof that dividing a whole number by a natural number will result
/// in a quotient that is greater than or equal to 0. Specifically,
/// `x / d >= 0`.
pub proof fn lemma_div_pos_is_pos(x: int, d: int)
    requires
        0 <= x,
        0 < d,
    ensures
        0 <= x / d,
{
    lemma_div_auto(d);
    assert(div_auto(d));
    let f = |u: int| 0 <= u ==> u / d >= 0;
    assert forall|i: int| #[trigger] is_le(0, i) && f(i) implies f(i + d) by {
        assert(i / d >= 0);
    };
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u / d >= 0);
}

/// Proof that dividing a whole number by a natural number will result
/// in a quotient that is greater than or equal to 0
pub proof fn lemma_div_pos_is_pos_auto()
    ensures
        forall|x: int, d: int|
            0 <= x && 0 < d ==> 0 <= #[trigger]
            (x / d),
{
    assert forall|x: int, d: int| 0 <= x && 0 < d implies 0 <= #[trigger]
    (x / d) by {
        lemma_div_pos_is_pos(x, d);
    }
}

/// Proof that dividing a number then adding 1 gives the same result
/// as adding the divisor and then doing the division. Specifically,
/// `1 + (x / d)` is equal to `(d + x) / d`.
pub proof fn lemma_div_plus_one(x: int, d: int)
    requires
        0 < d,
    ensures
        1 + x / d == (d + x) / d,
{
    lemma_div_auto(d);
}

/// Proof that dividing a number then adding 1 gives the same result
/// as adding the divisor and then doing the division
pub proof fn lemma_div_plus_one_auto()
    ensures
        forall|x: int, d: int|
            #![trigger (1 + x / d), ((d + x) / d)]
            0 < d ==> 1 + (x / d) == (d + x) / d,
{
    assert forall|x: int, d: int| 0 < d implies #[trigger]
    (1 + x / d) == #[trigger]
    ((d + x) / d) by {
        lemma_div_plus_one(x, d);
    }
}

/// Proof that dividing a number then subtracting 1 gives the same result
/// as subtracting the divisor and then doing the division. Specifically,
/// `-1 + (x / d)` is equal to `(-d + x) / d`.
pub proof fn lemma_div_minus_one(x: int, d: int)
    requires
        0 < d,
    ensures
        -1 + x / d == (-d + x) / d,
{
    lemma_div_auto(d);
}

/// Proof that dividing a number then subtracting 1 gives the same result
/// as subtracting the divisor and then doing the division
pub proof fn lemma_div_minus_one_auto()
    ensures
        forall|x: int, d: int|
            #![trigger (-1 + x / d), ((-d + x) / d)]
            0 < d ==> -1 + x / d == (-d + x) / d,
{
    assert forall|x: int, d: int| 0 < d implies #[trigger]
    (-1 + x / d) == #[trigger]
    ((-d + x) / d) by {
        lemma_div_minus_one(x, d);
    }
}

/// Proof that dividing any non-negative integer less than `d` by `d`
/// produces a quotient of 0
pub proof fn lemma_basic_div(d: int)
    requires
        0 < d,
    ensures
        forall|x: int|
            0 <= x < d ==> #[trigger]
            (x / d) == 0,
{
    lemma_div_auto(d);
}

/// Proof that dividing any non-negative integer by a larger integer
/// produces a quotient of 0
pub proof fn lemma_basic_div_auto()
    ensures
        forall|x: int, d: int|
            0 <= x < d ==> #[trigger]
            (x / d) == 0,
{
    assert forall|x: int, d: int| 0 <= x < d implies #[trigger]
    (x / d) == 0 by {
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
    ensures
        x / z <= y / z,
{
    lemma_div_auto(z);
    let f = |xy: int| xy <= 0 ==> (xy + y) / z <= y / z;
    assert forall|i: int| #[trigger] is_le(i + 1, z) && f(i) implies f(i - z) by {
        if (i - z <= 0) {
            assert(f(i));
            assert(i <= 0 ==> (i + y) / z <= y / z);
            if (i > 0) {
                assert(z > 0);
                assert(i <= z);
                assert(((i + y) - z) / z <= y / z);
            } else {
                assert((i + y) / z <= y / z);
            }
            assert((i - z + y) / z <= y / z);
        }
    };
    lemma_div_induction_auto(z, x - y, |xy: int| xy <= 0 ==> (xy + y) / z <= y / z);
}

/// Proof that numerical order is preserved when dividing two seperate
/// integers by a common positive divisor
pub proof fn lemma_div_is_ordered_auto()
    ensures
        forall|x: int, y: int, z: int|
            x <= y && 0 < z ==> #[trigger]
            (x / z) <= #[trigger]
            (y / z),
{
    assert forall|x: int, y: int, z: int| x <= y && 0 < z implies #[trigger]
    (x / z) <= #[trigger]
    (y / z) by {
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
        x / d < x,
{
    lemma_div_induction_auto(d, x, |u: int| 0 < u ==> u / d < u);
}

/// Proof that dividing an integer by 2 or more results in a quotient
/// that is smaller than the original dividend
pub proof fn lemma_div_decreases_auto()
    ensures
        forall|x: int, d: int|
            0 < x && 1 < d ==> #[trigger]
            (x / d) < x,
{
    assert forall|x: int, d: int| 0 < x && 1 < d implies #[trigger]
    (x / d) < x by {
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
        x / d <= x,
{
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u / d <= u);
}

/// Proof that dividing an integer by 1 or more results in a quotient
/// that is less than or equal to the original dividend
proof fn lemma_div_nonincreasing_auto()
    ensures
        forall|x: int, d: int|
            0 <= x && 0 < d ==> #[trigger]
            (x / d) <= x,
{
    assert forall|x: int, d: int| 0 <= x && 0 < d implies #[trigger]
    (x / d) <= x by {
        lemma_div_nonincreasing(x, d);
    }
}

/// Proof that a natural number x divided by a larger natural number
/// gives a remainder equal to x. Specifically, because `x < m`, we
/// know `x % m == x`.
pub proof fn lemma_small_mod(x: nat, m: nat)
    requires
        x < m,
        0 < m,
    ensures
        x % m == x,
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
        forall|y: int, z: int| #![trigger y * z] 0 < y && 0 < z ==> 0 < y * z,
        forall|x: int, y: int, z: int|
            #![trigger y * z, x % (y * z), y * ((x / y) % z) + x % y]
            0 <= x && 0 < y && 0 < z ==> x % (y * z) == y * ((x / y) % z) + x % y,
{
    assert forall|y: int, z: int| #![trigger y * z] 0 < y && 0 < z implies 0 < y * z by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall|x: int, y: int, z: int|
        #![trigger y * z, x % (y * z), y * ((x / y) % z) + x % y]
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
        x - d < x / d * d,
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u - d < u / d * d);
}

/// Proof that for any nonnegative integer `x` and positive integer
/// `d`, their difference `x - d` must be strictly less than the
/// quotient of `x` divided by `d` and then multiplied by `d`
pub proof fn lemma_remainder_upper_auto()
    ensures
        forall|x: int, d: int|
            #![trigger (x - d), (x / d * d)]
            0 <= x && 0 < d ==> (x - d) < (x / d * d),
{
    assert forall|x: int, d: int| 0 <= x && 0 < d implies #[trigger]
    (x - d) < #[trigger]
    (x / d * d) by {
        lemma_remainder_upper(x, d);
    }
}

/// Proof that the division of a nonnegative integer `x` by a positive
/// integer `d` multiplied by `d` is less than or equal to the value
/// of `x`.
pub proof fn lemma_remainder_lower(x: int, d: int)
    requires
        0 <= x,
        0 < d,
    ensures
        x >= x / d * d,
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u >= u / d * d);
}

/// Proof that, for all nonnegative `x` and positive `d`, `(x / d) * d <= x`
pub proof fn lemma_remainder_lower_auto()
    ensures
        forall|x: int, d: int|
            0 <= x && 0 < d ==> x >= #[trigger]
            (x / d * d),
{
    assert forall|x: int, d: int| (0 <= x && 0 < d) implies x >= #[trigger]
    (x / d * d) by {
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
        0 <= x - (x / d * d) < d,
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, |u: int| 0 <= u - u / d * d < d);
}

/// Proof that, for any nonnegative integer `x` and positive `d`,
/// `0 <= (x - (x / d * d)) < d`
pub proof fn lemma_remainder_auto()
    ensures
        forall|x: int, d: int|
            0 <= x && 0 < d ==> 0 <= #[trigger]
            (x - (x / d * d)) < d,
{
    assert forall|x: int, d: int| 0 <= x && 0 < d implies 0 <= #[trigger]
    (x - (x / d * d)) < d by {
        lemma_remainder(x, d);
    }
}

/// Proof of the fundamental theorem of division and modulo, namely
/// that `x` can be expressed as `d` times the quotient `x / d` plus
/// the remainder `x % d`.
pub proof fn lemma_fundamental_div_mod(x: int, d: int)
    requires
        d != 0,
    ensures
        x == d * (x / d) + (x % d),
{
    ModINL::lemma_fundamental_div_mod(x, d);
}

/// Proof of the fundamental theorem of division and modulo, namely
/// that for any `x` and nonzero `d`, `x == d * (x / d) + x % d`
pub proof fn lemma_fundamental_div_mod_auto()
    ensures
        forall|x: int, d: int|
            d != 0 ==> x == #[trigger]
            (d * (x / d) + (x % d)),
{
    assert forall|x: int, d: int| d != 0 implies x == #[trigger]
    (d * (x / d) + (x % d)) by {
        lemma_fundamental_div_mod(x, d);
    }
}

/// Proof that dividing `x` by `c * d` is equivalent to first dividing
/// `x` by `c` and then dividing the result by `d`
pub proof fn lemma_div_denominator(x: int, c: int, d: int)
    requires
        0 <= x,
        0 < c,
        0 < d,
    ensures
        c * d != 0,
        (x / c) / d == x / (c * d),
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
    assert(c * (x / c) + x % c - r == c * (x / c) - c * ((x / c) % d) ==> x - r == c * (x / c) - c
        * ((x / c) % d)) by {
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
        forall|c: int, d: int|
            0 < c && 0 < d ==> #[trigger]
            (c * d) != 0,
        forall|x: int, c: int, d: int|
            0 <= x && 0 < c && 0 < d ==> #[trigger]
            ((x / c) / d) == x / (c * d),
{
    lemma_mul_nonzero_auto();
    assert forall|x: int, c: int, d: int| 0 <= x && 0 < c && 0 < d implies #[trigger]
    ((x / c) / d) == x / (c * d) by {
        lemma_div_denominator(x, c, d);
    }
}

/// Proof that multiplying an integer by a fraction is equivalent to
/// multiplying the fraction's numerator by the integer. Specifically,
/// `x * (y / z) == (x * y) / z`.
pub proof fn lemma_mul_hoist_inequality(x: int, y: int, z: int)
    requires
        0 <= x,
        0 < z,
    ensures
        x * (y / z) <= (x * y) / z,
{
    calc! {
    (==)
    (x * y) / z;
    (==)   { lemma_fundamental_div_mod(y, z); }
    (x * (z * (y / z) + y % z)) / z;
    (==)    { lemma_mul_is_distributive_auto(); }
    (x * (z * (y / z)) + x * (y % z)) / z;
    }
    assert((x * (z * (y / z)) + x * (y % z)) / z >= x * (y / z)) by {
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
        forall|x: int, y: int, z: int|
            #![trigger (x * (y / z)), ((x * y) / z)]
            0 <= x && 0 < z ==> (x * (y / z)) <= ((x * y) / z),
{
    assert forall|x: int, y: int, z: int| 0 <= x && 0 < z implies #[trigger]
    (x * (y / z)) <= #[trigger]
    ((x * y) / z) by {
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
    ensures
        a / d == b / d,
{
    lemma_div_induction_auto(
        d,
        a - b,
        |ab: int|
            {
                let u = ab + b;
                0 <= u - u % d <= b < u + d - u % d ==> u / d == b / d
            },
    );
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
        forall|a: int, b: int, d: int|
            #![trigger (a / d), (b / d)]
            0 < d && 0 <= a - a % d <= b < a + d - a % d ==> (a / d) == (b / d),
{
    assert forall|a: int, b: int, d: int|
        0 < d && 0 <= a - a % d <= b < a + d - a % d implies #[trigger]
    (a / d) == #[trigger]
    (b / d) by {
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
        (b * x) % (b * c) == b * (x % c),
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
    ensures
        forall|x: int, b: int, c: int|
            #![trigger (b * (x % c))]
            0 <= x && 0 < b && 0 < c && 0 < b * c ==> (b * x) % (b * c) == b * (x % c),
{
    assert forall|x: int, b: int, c: int| 0 <= x && 0 < b && 0 < c && 0 < b * c implies #[trigger]
    (b * (x % c)) == ((b * x) % (b * c)) by {
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
    lemma_mul_strictly_positive(x, d);
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
        forall|x: int, d: int| #![trigger x * d] 0 < x && 0 < d ==> 0 < x * d,
        forall|x: int, a: int, d: int|
            #![trigger a / d, x * a, x * d]
            0 < x && 0 <= a && 0 < d ==> a / d == (x * a) / (x * d),
{
    assert forall|x: int, d: int| #![trigger x * d] 0 < x && 0 < d implies 0 < x * d by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall|x: int, a: int, d: int|
        #![trigger a / d, x * a, x * d]
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
    ensures
        forall|a: int, r: int, d: int|
            #![trigger (d * ((a + r) / d))]
            0 < d && a % d == 0 && 0 <= r < d ==> a == d * ((a + r) / d),
{
    assert forall|a: int, r: int, d: int| 0 < d && a % d == 0 && 0 <= r < d implies #[trigger]
    (d * ((a + r) / d)) == a by {
        lemma_round_down(a, r, d);
    }
}

/// Proof that, since `0 <= b < d`, we have `(d * x + b) / d == x`.
pub proof fn lemma_div_multiples_vanish_fancy(x: int, b: int, d: int)
    requires
        0 < d,
        0 <= b < d,
    ensures
        (d * x + b) / d == x,
{
    let f = |u: int| (d * u + b) / d == u;
    assert(f(0)) by {
        lemma_div_auto(d);
    }
    assert forall|i: int|
        i >= 0 && #[trigger]
        f(i) implies #[trigger]
    f(add1(i, 1)) by {
        assert(d * (i + 1) + b == d * i + b + d) by {
            assert(d * (i + 1) == d * i + d) by {
                lemma_mul_is_distributive_add(d, i, 1);
                lemma_mul_basics(d);
            }
        }
        crate::arithmetic::internals::div_internals::lemma_div_basics(d);
    }
    assert forall|i: int|
        i <= 0 && #[trigger]
        f(i) implies #[trigger]
    f(sub1(i, 1)) by {
        assert(d * (i - 1) + b == d * i + b - d) by {
            assert(d * (i - 1) == d * i - d) by {
                lemma_mul_is_distributive_sub(d, i, 1);
                lemma_mul_basics(d);
            }
        }
        crate::arithmetic::internals::div_internals::lemma_div_basics(d);
    }
    lemma_mul_auto();
    lemma_mul_induction(f);
    assert(f(x));
}

/// Proof that, for any `x`, `b`, and `d` satisfying `0 <= b < d`, we have `(d * x + b) / d == x`
pub proof fn lemma_div_multiples_vanish_fancy_auto()
    ensures
        forall|x: int, b: int, d: int|
            #![trigger (d * x + b) / d]
            0 < d && 0 <= b < d ==> (d * x + b) / d == x,
{
    assert forall|x: int, b: int, d: int| 0 < d && 0 <= b < d implies #[trigger]
    ((d * x + b) / d) == x by {
        lemma_div_multiples_vanish_fancy(x, b, d);
    }
}

/// Proof that multiplying an integer by a common numerator and
/// denominator results in the original integer. Specifically,
/// `(d * x) / d == x`.
pub proof fn lemma_div_multiples_vanish(x: int, d: int)
    requires
        0 < d,
    ensures
        (d * x) / d == x,
{
    lemma_div_multiples_vanish_fancy(x, 0, d);
}

/// Proof that multiplying an integer by a common numerator and
/// denominator results in the original integer
pub proof fn lemma_div_multiples_vanish_auto()
    ensures
        forall|x: int, d: int| #![trigger (d * x) / d] 0 < d ==> (d * x) / d == x,
{
    assert forall|x: int, d: int| 0 < d implies #[trigger]
    ((d * x) / d) == x by {
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
        (b * d) / d == b,
{
    lemma_div_multiples_vanish(b, d);
    lemma_mul_auto();
}

/// Proof that multiplying a whole number by a common numerator and
/// denominator results in the original integer
pub proof fn lemma_div_by_multiple_auto()
    ensures
        forall|b: int, d: int| #![trigger ((b * d) / d)] 0 <= b && 0 < d ==> (b * d) / d == b,
{
    assert forall|b: int, d: int| 0 <= b && 0 < d implies #[trigger]
    ((b * d) / d) == b by {
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
        x / z < y / z,
{
    lemma_mod_multiples_basic(m, z);
    lemma_div_induction_auto(
        z,
        y - x,
        |yx: int|
            {
                let u = yx + x;
                x < u && u % z == 0 ==> x / z < u / z
            },
    );
}

/// Proof that a dividend that is a positive multiple of a divisor
/// will always yield a greater quotient than a smaller dividend
pub proof fn lemma_div_by_multiple_is_strongly_ordered_auto()
    ensures
        forall|x: int, y: int, m: int, z: int|
            #![trigger x / z, m * z, y / z]
            x < y && y == m * z && 0 < z ==> x / z < y / z,
{
    assert forall|x: int, y: int, m: int, z: int|
        x < y && y == #[trigger]
        (m * z) && 0 < z implies #[trigger]
    (x / z) < #[trigger]
    (y / z) by {
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
        a / b <= c,
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
    ensures
        forall|a: int, b: int, c: int| #![trigger a / b, b * c] 0 < b && a <= b * c ==> a / b <= c,
{
    assert forall|a: int, b: int, c: int|
        0 < b && a <= #[trigger]
        (b * c) implies #[trigger]
    (a / b) <= c by {
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
        a / b < c,
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
    ensures
        forall|a: int, b: int, c: int| #![trigger a / b, b * c] 0 < b && a < b * c ==> a / b < c,
{
    assert forall|a: int, b: int, c: int|
        0 < b && a < #[trigger]
        (b * c) implies #[trigger]
    (a / b) < c by {
        lemma_multiply_divide_lt(a, b, c);
    }
}

/// Proof that adding an integer to a fraction is equivalent to adding
/// that integer times the denominator to the numerator. Specifically,
/// `x / d + j == (x + j * d) / d`.
pub proof fn lemma_hoist_over_denominator(x: int, j: int, d: nat)
    requires
        0 < d,
    ensures
        x / d as int + j == (x + j * d) / d as int,
{
    lemma_div_auto(d as int);
    let f = |u: int| x / d as int + u == (x + u * d) / d as int;
    // OBSERVE: push precondition on its on scope
    assert(f(0) && (forall|i: int|
        i >= 0 && #[trigger]
        f(i) ==> #[trigger]
        f(add1(i, 1))) && (forall|i: int|
        i <= 0 && #[trigger]
        f(i) ==> #[trigger]
        f(sub1(i, 1)))) by {
        lemma_mul_auto();
    }
    lemma_mul_induction(f);
    assert(f(j));
}

/// Proof that adding an integer to a fraction is equivalent to adding
/// that integer times the denominator to the numerator
pub proof fn lemma_hoist_over_denominator_auto()
    ensures
        forall|x: int, j: int, d: nat|
            #![trigger x / d as int + j]
            0 < d ==> x / d as int + j == (x + j * d) / d as int,
{
    assert forall|x: int, j: int, d: nat| 0 < d implies #[trigger]
    (x / d as int + j) == (x + j * d) / d as int by {
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
        (b * (a / b) % (b * c)) <= b * (c - 1),
{
    lemma_mul_strictly_positive(b, a / b);
    lemma_mul_strictly_positive(b, c);
    lemma_mul_strictly_positive(b, c - 1);
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
    assert(b * (a / b) % (b * c) <= b * (c - 1)) by {
        lemma_mul_is_commutative_auto();
        lemma_mul_inequality_auto();
    };
}

/// Proof that, for any nonnegative integer `a` and positive integers `b` and `c`,
/// the remainder of `b * (a / b)` divided by `b * c` is less than or equal to `b * (c - 1)`.
/// This accounts for the rounding down that occurs in integer division.
pub proof fn lemma_part_bound1_auto()
    ensures
        forall|b: int, c: int| #![trigger b * c] 0 < b && 0 < c ==> 0 < b * c,
        forall|a: int, b: int, c: int|
            #![trigger (b * (a / b) % (b * c))]
            0 <= a && 0 < b && 0 < c ==> b * (a / b) % (b * c) <= b * (c - 1),
{
    assert forall|b: int, c: int| #![trigger b * c] 0 < b && 0 < c implies 0 < b * c by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall|a: int, b: int, c: int|
        #![trigger (b * (a / b) % (b * c))]
        0 <= a && 0 < b && 0 < c implies b * (a / b) % (b * c) <= b * (c - 1) by {
        lemma_part_bound1(a, b, c);
    }
}

/*******************************************************************************
   * Modulus:
   *******************************************************************************/

/// Proof that computing the modulus using `%` is equivalent to
/// computing it with [`mod_recursive`]. Specifically,
/// `x % m == mod_recursive(x, m)`.
pub proof fn lemma_mod_is_mod_recursive(x: int, m: int)
    requires
        m > 0,
    ensures
        mod_recursive(x, m) == x % m,
    decreases
            (if x < 0 {
                -x + m
            } else {
                x
            }),
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

/// Proof that computing the modulus using `%` is equivalent to
/// computing it with [`mod_recursive`]
pub proof fn lemma_mod_is_mod_recursive_auto()
    ensures
        forall|x: int, d: int|
            d > 0 ==> mod_recursive(x, d) == #[trigger]
            (x % d),
{
    reveal(mod_recursive);
    assert forall|x: int, d: int| d > 0 implies mod_recursive(x, d) == #[trigger]
    (x % d) by {
        lemma_mod_is_mod_recursive(x, d);
    };
}

/// Proof of basic properties of the modulus operation: any integer
/// divided by itself produces a remainder of 0; performing `(x % m) %
/// m` gives the same result as simply perfoming `x % m`.
pub proof fn lemma_mod_basics_auto()
    ensures
        forall|m: int|
            m > 0 ==> #[trigger]
            (m % m) == 0,
        forall|x: int, m: int|
            m > 0 ==> #[trigger]
            ((x % m) % m) == x % m,
{
    assert forall|m: int| m > 0 implies #[trigger]
    (m % m) == 0 by {
        lemma_mod_auto(m);
    };
    assert forall|x: int, m: int| m > 0 implies #[trigger]
    ((x % m) % m) == x % m by {
        lemma_mod_auto(m);
    };
}

/// Proof of properties of the modulus operation including those
/// described in `lemma_mod_basics_auto`. This lemma also states that
/// the remainder of any division will be less than the divisor's
/// value.
pub proof fn lemma_mod_properties_auto()
    ensures
        forall|m: int|
            m > 0 ==> #[trigger]
            (m % m) == 0,
        forall|x: int, m: int|
            m > 0 ==> #[trigger]
            ((x % m) % m) == x % m,
        forall|x: int, m: int|
            m > 0 ==> 0 <= #[trigger]
            (x % m) < m,
{
    lemma_mod_basics_auto();
    assert forall|x: int, m: int| m > 0 implies 0 <= #[trigger]
    (x % m) < m by {
        lemma_mod_auto(m);
    }
}

/// Proof that when natural number `x` is divided by natural number
/// `m`, the remainder will be less than or equal to `x`.
pub proof fn lemma_mod_decreases(x: nat, m: nat)
    requires
        0 < m,
    ensures
        x % m <= x,
{
    lemma_mod_auto(m as int);
}

/// Proof that dividing any natural number `x` by any divisor produces
/// a quotient less than or equal to `x`.
pub proof fn lemma_mod_decreases_auto()
    ensures
        forall|x: nat, m: nat|
            0 < m ==> #[trigger]
            (x % m) <= x,
{
    assert forall|x: nat, m: nat| 0 < m implies #[trigger]
    (x % m) <= x by {
        lemma_mod_decreases(x, m);
    }
}

/// Proof that if `x % m` is zero and `x` is positive, then `x >= m`.
pub proof fn lemma_mod_is_zero(x: nat, m: nat)
    requires
        x > 0 && m > 0,
        x % m == 0,
    ensures
        x >= m,
{
    if (x < m) {
        lemma_small_mod(x, m);
    }
}

/// Proof that if a remainder is zero and the dividend is positive,
/// then the dividend is greater than or equal to the divisor. In
/// other words, if `x % m == 0` and `x > 0`, then `x >= m`.
pub proof fn lemma_mod_is_zero_auto()
    ensures
        forall|x: nat, m: nat|
            x > 0 && m > 0 && #[trigger]
            (x % m) == 0 ==> x >= m,
{
    assert forall|x: nat, m: nat|
        x > 0 && m > 0 && #[trigger]
        (x % m) == 0 implies x >= m by {
        lemma_mod_is_zero(x, m);
    }
}

/// Proof that multiplying by a number then dividing by that same
/// number produces a remainder of 0. Specifically, `(x * m) % m == 0`.
pub proof fn lemma_mod_multiples_basic(x: int, m: int)
    requires
        m > 0,
    ensures
        (x * m) % m == 0,
{
    lemma_mod_auto(m);
    lemma_mul_auto();
    let f = |u: int| (u * m) % m == 0;
    lemma_mul_induction(f);
    assert(f(x));
}

/// Proof that multiplying by a number then dividing by that same
/// number produces a remainder of 0
pub proof fn lemma_mod_multiples_basic_auto()
    ensures
        forall|x: int, m: int|
            m > 0 ==> #[trigger]
            ((x * m) % m) == 0,
{
    assert forall|x: int, m: int| m > 0 implies #[trigger]
    ((x * m) % m) == 0 by {
        lemma_mod_multiples_basic(x, m);
    }
}

/// Proof that adding the divisor to the dividend doesn't change the
/// remainder. Specifically, `(m + b) % m == b % m`.
pub proof fn lemma_mod_add_multiples_vanish(b: int, m: int)
    requires
        0 < m,
    ensures
        (m + b) % m == b % m,
{
    lemma_mod_auto(m);
}

/// Proof that adding the divisor to the dividend doesn't change the
/// remainder. In other words, for all `m` and `b`, `(m + b) % m == b % m`.
pub proof fn lemma_mod_add_multiples_vanish_auto()
    ensures
        forall|b: int, m: int|
            m > 0 ==> ((m + b) % m) == #[trigger]
            (b % m),
{
    assert forall|b: int, m: int| m > 0 implies ((m + b) % m) == #[trigger]
    (b % m) by {
        lemma_mod_add_multiples_vanish(b, m);
    }
}

/// Proof that subtracting the divisor from the dividend doesn't
/// change the remainder. Specifically, `(-m + b) % m == b % m`.
pub proof fn lemma_mod_sub_multiples_vanish(b: int, m: int)
    requires
        0 < m,
    ensures
        (-m + b) % m == b % m,
{
    lemma_mod_auto(m);
}

/// Proof that subtracting the divisor from the dividend doesn't
/// change the remainder. In other words, for all `m` and `b`,
/// `(-m + b) % m == b % m`.
pub proof fn lemma_mod_sub_multiples_vanish_auto()
    ensures
        forall|b: int, m: int|
            m > 0 ==> ((-m + b) % m) == #[trigger]
            (b % m),
{
    assert forall|b: int, m: int| m > 0 implies ((-m + b) % m) == #[trigger]
    (b % m) by {
        lemma_mod_sub_multiples_vanish(b, m);
    }
}

/// Proof that adding any multiple of the divisor to the dividend will produce the
/// same remainder. In other words, `(m * a + b) % m == b % m`.
pub proof fn lemma_mod_multiples_vanish(a: int, b: int, m: int)
    requires
        0 < m,
    ensures
        (m * a + b) % m == b % m,
    decreases
            (if a > 0 {
                a
            } else {
                -a
            }),
{
    lemma_mod_auto(m);
    lemma_mul_auto();
    let f = |u: int| (m * u + b) % m == b % m;
    lemma_mul_induction(f);
    assert(f(a));
}

/// Proof that adding any multiple of the divisor to the dividend will produce the
/// same remainder. In other words, for all `m`, `a`, and `b`,
/// `(m * a + b) % m == b % m`.
pub proof fn lemma_mod_multiples_vanish_auto()
    ensures
        forall|a: int, b: int, m: int|
            m > 0 ==> #[trigger]
            ((m * a + b) % m) == b % m,
{
    assert forall|a: int, b: int, m: int| m > 0 implies #[trigger]
    ((m * a + b) % m) == b % m by {
        lemma_mod_multiples_vanish(a, b, m);
    }
}

/// Proof that modulo distributes over subtraction if the subtracted value is
/// less than or equal to the modulo of the number it's being subtracted from.
/// Specifically, because `0 <= s <= x % d`, we can conclude that
/// `x % d - s % d == (x - s) % d`.
pub proof fn lemma_mod_subtraction(x: nat, s: nat, d: nat)
    requires
        0 < d,
        0 <= s <= x % d,
    ensures
        x % d - s % d == (x - s) % d as int,
{
    lemma_mod_auto(d as int);
}

/// Proof that modulo distributes over subtraction if the subtracted
/// value is less than or equal to the modulo of the number it's being
/// subtracted from. In other words, for all `s`, `x`, and `d`
/// satisfying `0 <= s <= x % d`, we can conclude that `x % d - s % d
/// == (x - s) % d`.
pub proof fn lemma_mod_subtraction_auto()
    ensures
        forall|x: nat, s: nat, d: nat|
            #![trigger ((x - s) % d as int)]
            0 < d && 0 <= s <= x % d ==> x % d - s % d == (x - s) % d as int,
{
    assert forall|x: nat, s: nat, d: nat| 0 < d && 0 <= s <= x % d implies x % d - s % d
        == #[trigger]
    ((x - s) % d as int) as int by {
        lemma_mod_subtraction(x, s, d);
    }
}

/// Proof that modulo distributes over addition, provided you do an extra modulo after adding the remainders.
/// Specifically, `((x % m) + (y % m)) % m == (x + y) % m`.
pub proof fn lemma_add_mod_noop(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        ((x % m) + (y % m)) % m == (x + y) % m,
{
    lemma_mod_auto(m);
}

/// Proof that modulo distributes over addition, provided you do an extra modulo after adding the remainders.
/// In other words, for all `x`, `y`, and `m`, `((x % m) + (y % m)) % m == (x + y) % m`.
pub proof fn lemma_add_mod_noop_auto()
    ensures
        forall|x: int, y: int, m: int|
            #![trigger (x + y) % m]
            0 < m ==> ((x % m) + (y % m)) % m == (x + y) % m,
{
    assert forall|x: int, y: int, m: int| 0 < m implies ((x % m) + (y % m)) % m == #[trigger]
    ((x + y) % m) by {
        lemma_add_mod_noop(x, y, m);
    }
}

/// Proof that describes an expanded and succinct version of modulus operator in relation to addition.
/// Specifically, `(x + (y % m)) % m == (x + y) % m`.
pub proof fn lemma_add_mod_noop_right(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        (x + (y % m)) % m == (x + y) % m,
{
    lemma_mod_auto(m);
}

/// Proof that describes an expanded and succinct version of modulus operator in relation to addition.
/// That is, for all `x`, `y`, and `m`, `(x + (y % m)) % m == (x + y) % m`.
pub proof fn lemma_add_mod_noop_right_auto()
    ensures
        forall|x: int, y: int, m: int|
            #![trigger (x + y) % m]
            0 < m ==> (x + (y % m)) % m == (x + y) % m,
{
    assert forall|x: int, y: int, m: int| 0 < m implies (x + (y % m)) % m == #[trigger]
    ((x + y) % m) by {
        lemma_add_mod_noop_right(x, y, m);
    }
}

/// Proof that modulo distributes over subtraction provided you do an extra modulo operation after
/// subtracting the remainders. Specifically, `((x % m) - (y % m)) % m == (x - y) % m`.
pub proof fn lemma_sub_mod_noop(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        ((x % m) - (y % m)) % m == (x - y) % m,
{
    lemma_mod_auto(m);
}

/// Proof that modulo distributes over subtraction provided you do an extra modulo operation after
/// subtracting the remainders. In other words, for all `x`, `y`, and `m`,
/// `((x % m) - (y % m)) % m == (x - y) % m`.
pub proof fn lemma_sub_mod_noop_auto()
    ensures
        forall|x: int, y: int, m: int|
            #![trigger (x - y) % m]
            0 < m ==> ((x % m) - (y % m)) % m == (x - y) % m,
{
    assert forall|x: int, y: int, m: int| 0 < m implies ((x % m) - (y % m)) % m == #[trigger]
    ((x - y) % m) by {
        lemma_sub_mod_noop(x, y, m);
    }
}

/// Proof that describes an expanded and succinct version of modulus operator in relation to subtraction.
/// Specifically, `(x - (y % m)) % m == (x - y) % m`.
pub proof fn lemma_sub_mod_noop_right(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        (x - (y % m)) % m == (x - y) % m,
{
    lemma_mod_auto(m);
}

/// Proof that describes an expanded and succinct version of modulus operator in relation to subtraction.
/// That is, for all `x`, `y`, and `m`, `(x - (y % m)) % m == (x - y) % m`.
pub proof fn lemma_sub_mod_noop_right_auto()
    ensures
        forall|x: int, y: int, m: int|
            #![trigger ((x - y) % m)]
            0 < m ==> (x - (y % m)) % m == (x - y) % m,
{
    assert forall|x: int, y: int, m: int| 0 < m implies (x - (y % m)) % m == #[trigger]
    ((x - y) % m) by {
        lemma_sub_mod_noop_right(x, y, m);
    }
}

/// Proof of two properties of the sum of two remainders with the same dividend:
/// 1) `a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d)`.
/// 2) `(a % d + b % d) < d ==> a % d + b % d == (a + b) % d`.
pub proof fn lemma_mod_adds(a: int, b: int, d: int)
    requires
        0 < d,
    ensures
        a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d),
        (a % d + b % d) < d ==> a % d + b % d == (a + b) % d,
{
    lemma_mul_auto();
    lemma_div_auto(d);
}

/// Proof of two properties of the sum of two remainders with the same dividend,
/// i.e., that for all `a`, `b`, and `d`:
/// 1) `a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d)`.
/// 2) `(a % d + b % d) < d ==> a % d + b % d == (a + b) % d`.
pub proof fn lemma_mod_adds_auto()
    ensures
        forall|a: int, b: int, d: int|
            #![trigger ((a + b) % d)]
            0 < d ==> a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d),
{
    assert forall|a: int, b: int, d: int| 0 < d implies a % d + b % d == #[trigger]
    ((a + b) % d) + d * ((a % d + b % d) / d) by {
        lemma_mod_adds(a, b, d);
    }
}

/// Proof that the remainder when dividing integer `x` by positive
/// integer `d` is equivalent to the remainder of `x * (1 - d)` by
/// `d`.
#[verifier::spinoff_prover]
pub proof fn lemma_mod_neg_neg(x: int, d: int)
    requires
        0 < d,
    ensures
        x % d == (x * (1 - d)) % d,
{
    assert((x - x * d) % d == x % d) by {
        let f = |i: int| (x - i * d) % d == x % d;
        lemma_mul_auto();
        assert(f(0) && (forall|i: int|
            i >= 0 && #[trigger]
            f(i) ==> #[trigger]
            f(add1(i, 1))) && (forall|i: int|
            i <= 0 && #[trigger]
            f(i) ==> #[trigger]
            f(sub1(i, 1)))) by {
            lemma_mod_auto(d);
        };
        lemma_mul_induction(f);
        assert(f(x));
    }
    lemma_mul_auto();
}

/// This proof isn't exported from this module. It's just used in
/// the proof of `lemma_fundamental_div_mod_converse`.
proof fn lemma_fundamental_div_mod_converse_helper_1(u: int, d: int, r: int)
    requires
        d != 0,
        0 <= r < d,
    ensures
        u == (u * d + r) / d,
    decreases
            if u >= 0 {
                u
            } else {
                -u
            },
{
    if u < 0 {
        lemma_fundamental_div_mod_converse_helper_1(u + 1, d, r);
        lemma_div_add_denominator(d, u * d + r);
        lemma_mul_is_distributive_add_other_way(d, u + 1, -1);
        assert(u == (u * d + r) / d);
    } else if u == 0 {
        DivINL::lemma_small_div();
        assert(u == 0 ==> u * d == 0) by (nonlinear_arith);
        assert(u == (u * d + r) / d);
    } else {
        lemma_fundamental_div_mod_converse_helper_1(u - 1, d, r);
        lemma_div_add_denominator(d, (u - 1) * d + r);
        lemma_mul_is_distributive_add_other_way(d, u - 1, 1);
        assert(u * d + r == (u - 1) * d + r + d);
        assert(u == (u * d + r) / d);
    }
}

/// This proof isn't exported from this module. It's just used in
/// the proof of `lemma_fundamental_div_mod_converse`.
proof fn lemma_fundamental_div_mod_converse_helper_2(u: int, d: int, r: int)
    requires
        d != 0,
        0 <= r < d,
    ensures
        r == (u * d + r) % d,
    decreases
            if u >= 0 {
                u
            } else {
                -u
            },
{
    if u < 0 {
        lemma_fundamental_div_mod_converse_helper_2(u + 1, d, r);
        lemma_mod_add_multiples_vanish(u * d + r, d);
        lemma_mul_is_distributive_add_other_way(d, u + 1, -1);
        assert(u * d == (u + 1) * d + (-1) * d);
        assert(u * d + r == (u + 1) * d + r - d);
        assert(r == (u * d + r) % d);
    } else if u == 0 {
        assert(u == 0 ==> u * d == 0) by (nonlinear_arith);
        if d > 0 {
            lemma_small_mod(r as nat, d as nat);
        } else {
            lemma_small_mod(r as nat, (-d) as nat);
        }
        assert(r == (u * d + r) % d);
    } else {
        lemma_fundamental_div_mod_converse_helper_2(u - 1, d, r);
        lemma_mod_add_multiples_vanish((u - 1) * d + r, d);
        lemma_mul_is_distributive_add_other_way(d, u - 1, 1);
        assert(u * d + r == (u - 1) * d + r + d);
        assert(r == (u * d + r) % d);
    }
}

/// Proof of the converse of the fundamental property of division and modulo.
/// Specifically, if we know `0 <= r < d` and `x == q * d + r`, then we
/// know that `q` is the quotient `x / d` and `r` is the remainder `x % d`.
pub proof fn lemma_fundamental_div_mod_converse(x: int, d: int, q: int, r: int)
    requires
        d != 0,
        0 <= r < d,
        x == q * d + r,
    ensures
        q == x / d,
        r == x % d,
{
    lemma_fundamental_div_mod_converse_helper_1(q, d, r);
    assert(q == (q * d + r) / d);
    lemma_fundamental_div_mod_converse_helper_2(q, d, r);
}

/// Proof of the converse of the fundamental property of division and
/// modulo. That is, whenever `0 <= r < d` and `x == q * d + r`, we
/// know that `q` is the quotient `x / d` and `r` is the remainder `x % d`.
pub proof fn lemma_fundamental_div_mod_converse_auto()
    ensures// forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) ==> q == (x / d) && r == #[trigger](x % d),

        forall|x: int, d: int, q: int, r: int|
            d != 0 && 0 <= r < d && x == #[trigger]
            (q * d + r) ==> q == #[trigger]
            (x / d),
        forall|x: int, d: int, q: int, r: int|
            d != 0 && 0 <= r < d && x == #[trigger]
            (q * d + r) ==> r == #[trigger]
            (x % d),
{
    assert forall|x: int, d: int, q: int, r: int|
        d != 0 && 0 <= r < d && x == #[trigger]
        (q * d + r) implies q == #[trigger]
    (x / d) by {
        lemma_fundamental_div_mod_converse(x, d, q, r);
    };
    assert forall|x: int, d: int, q: int, r: int|
        d != 0 && 0 <= r < d && x == #[trigger]
        (q * d + r) implies r == #[trigger]
    (x % d) by {
        lemma_fundamental_div_mod_converse(x, d, q, r);
    };
}

/// Proof that the remainder, when natural number `x` is divided by
/// positive integer `m`, is less than `m`.
pub proof fn lemma_mod_pos_bound(x: int, m: int)
    requires
        0 <= x,
        0 < m,
    ensures
        0 <= x % m < m,
{
    lemma_mod_auto(m);
}

/// Proof that the remainder, when any number `x` is divided by
/// positive integer `m`, is less than `m`.
pub proof fn lemma_mod_bound(x: int, m: int)
    requires
        0 < m,
    ensures
        0 <= x % m < m,
{
    ModINL::lemma_mod_range(x, m);
}

/// Proof that the remainder, when any natural number `x` is divided by
/// any positive integer `m`, is less than `m`.
pub proof fn lemma_mod_pos_bound_auto()
    ensures
        forall|x: int, m: int|
            0 <= x && 0 < m ==> 0 <= #[trigger]
            (x % m) < m,
{
    assert forall|x: int, m: int| 0 <= x && 0 < m implies 0 <= #[trigger]
    (x % m) < m by {
        lemma_mod_pos_bound(x, m);
    }
}

/// Proof that the remainder when `x * y` is divided by `m` is
/// equivalent to the remainder when `(x % m) * y` is divided by `m`
pub proof fn lemma_mul_mod_noop_left(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        (x % m) * y % m == x * y % m,
{
    lemma_mod_auto(m);
    lemma_mul_induction_auto(y, |u: int| (x % m) * u % m == x * u % m);
}

/// Proof that for any `x`, `y`, and `m`, the remainder when `x * y`
/// is divided by `m` is equivalent to the remainder when `(x % m) *
/// y` is divided by `m`
pub proof fn lemma_mul_mod_noop_left_auto()
    ensures
        forall|x: int, y: int, m: int|
            0 < m ==> (x % m) * y % m == #[trigger]
            (x * y % m),
{
    assert forall|x: int, y: int, m: int| 0 < m implies (x % m) * y % m == #[trigger]
    (x * y % m) by {
        lemma_mul_mod_noop_left(x, y, m);
    }
}

/// Proof that the remainder when `x * y` is divided by `m` is
/// equivalent to the remainder when `x * (y % m)` is divided by `m`.
pub proof fn lemma_mul_mod_noop_right(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        x * (y % m) % m == (x * y) % m,
{
    lemma_mod_auto(m);
    lemma_mul_induction_auto(x, |u: int| u * (y % m) % m == (u * y) % m);
}

/// Proof that for all `x`, `y`, and `m`, the remainder when `x * y`
/// is divided by `m` is equivalent to the remainder when `x * (y % m)`
/// is divided by `m`.
pub proof fn lemma_mul_mod_noop_right_auto()
    ensures
        forall|x: int, y: int, m: int|
            0 < m ==> x * (y % m) % m == #[trigger]
            ((x * y) % m),
{
    assert forall|x: int, y: int, m: int| 0 < m implies x * (y % m) % m == #[trigger]
    ((x * y) % m) by {
        lemma_mul_mod_noop_right(x, y, m);
    }
}

/// Proof of various properties about modulo equivalence with respect
/// to multiplication, specifically various expressions that `(x * y)
/// % m` is equivalent to.
pub proof fn lemma_mul_mod_noop_general(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        ((x % m) * y) % m == (x * y) % m,
        (x * (y % m)) % m == (x * y) % m,
        ((x % m) * (y % m)) % m == (x * y) % m,
{
    lemma_mod_properties_auto();
    lemma_mul_mod_noop_left(x, y, m);
    lemma_mul_mod_noop_right(x, y, m);
    lemma_mul_mod_noop_right(x % m, y, m);
}

/// Proof of various properties about modulo equivalence with respect to multiplication
pub proof fn lemma_mul_mod_noop_general_auto()
    ensures
        forall|x: int, y: int, m: int|
            0 < m ==> (((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m
                == #[trigger]
            ((x * y) % m)),
{
    assert forall|x: int, y: int, m: int| 0 < m implies (((x % m) * y) % m == (x * (y % m)) % m == (
    (x % m) * (y % m)) % m == #[trigger]
    ((x * y) % m)) by {
        lemma_mul_mod_noop_general(x, y, m);
    }
}

/// Proof that modulo distributes over multiplication, provided you do
/// an extra modulo operation after multiplying the remainders. Specifically,
/// `(x % m) * (y % m) % m == (x * y) % m`.
pub proof fn lemma_mul_mod_noop(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        (x % m) * (y % m) % m == (x * y) % m,
{
    lemma_mul_mod_noop_general(x, y, m);
}

/// Proof that modulo distributes over multiplication, provided you do
/// an extra modulo operation after multiplying the remainders
pub proof fn lemma_mul_mod_noop_auto()
    ensures
        forall|x: int, y: int, m: int|
            0 < m ==> ((x % m) * (y % m) % m == #[trigger]
            ((x * y) % m)),
{
    assert forall|x: int, y: int, m: int| 0 < m implies ((x % m) * (y % m) % m == #[trigger]
    ((x * y) % m)) by {
        lemma_mul_mod_noop(x, y, m);
    }
}

/// Proof that `x` and `y` are congruent modulo `m` if and only if `x
/// - y` is congruent to 0 modulo `m`. In other words, `x % m == y % m
/// <==> (x - y) % m == 0`.
pub proof fn lemma_mod_equivalence(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        x % m == y % m <==> (x - y) % m == 0,
{
    lemma_mod_auto(m);
}

/// Proof that for all `x`, `y`, and `m`, `x` and `y` are congruent
/// modulo `m` if and only if `x - y` is congruent to 0 modulo `m`. In
/// other words, `x % m == y % m <==> (x - y) % m == 0`.
///
/// Note: The Dafny standard library uses the triggers `x % m, y % m`
/// for this forall quantifier. But this can lead to a trigger loop,
/// so we don't do that here.
pub proof fn lemma_mod_equivalence_auto()
    ensures
        forall|x: int, y: int, m: int|
            #![trigger (x - y) % m]
            0 < m ==> (x % m == y % m <==> (x - y) % m == 0),
{
    assert forall|x: int, y: int, m: int| #![trigger (x - y) % m] 0 < m implies ((x % m) == (y % m)
        <==> (x - y) % m == 0) by {
        lemma_mod_equivalence(x, y, m);
    }
}

/// This function says that `x` is congruent to `y` modulo `m` if and
/// only if their difference `x - y` is congruent to 0 modulo `m`.
pub open spec fn is_mod_equivalent(x: int, y: int, m: int) -> bool
    recommends
        m > 0,
{
    x % m == y % m <==> (x - y) % m == 0
}

/// Proof that if `is_mod_equivalent` holds for `x`, `y`, and `m`,
/// then it holds for `x * z`, `y * z`, and `m`
pub proof fn lemma_mod_mul_equivalent(x: int, y: int, z: int, m: int)
    requires
        m > 0,
        is_mod_equivalent(x, y, m),
    ensures
        is_mod_equivalent(x * z, y * z, m),
{
    lemma_mul_mod_noop_left(x, z, m);
    lemma_mul_mod_noop_left(y, z, m);
    lemma_mod_equivalence(x, y, m);
    lemma_mod_equivalence(x * z, y * z, m);
}

/// Proof that if `is_mod_equivalent` holds for any `x`, `y`, and `m`,
/// then it holds for `x * z`, `y * z`, and `m`
pub proof fn lemma_mod_mul_equivalent_auto()
    ensures
        forall|x: int, y: int, z: int, m: int|
            m > 0 && (x % m == y % m <==> (x - y) % m == 0) ==> #[trigger]
            is_mod_equivalent(x * z, y * z, m),
{
    assert forall|x: int, y: int, z: int, m: int|
        m > 0 && is_mod_equivalent(x, y, m) implies #[trigger]
    is_mod_equivalent(x * z, y * z, m) by {
        lemma_mod_mul_equivalent(x, y, z, m);
    }
}

/// Proof that multiplying the divisor by a positive number can't
/// decrease the remainder. Specifically, because `k > 0`, we have
/// `x % d <= x % (d * k)`.
pub proof fn lemma_mod_ordering(x: int, k: int, d: int)
    requires
        1 < d,
        0 < k,
    ensures
        0 < d * k,
        x % d <= x % (d * k),
{
    lemma_mul_strictly_increases(d, k);
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
    assert((x % (d * k)) % d <= x % (d * k)) by {
        lemma_mod_properties_auto();
        lemma_mod_decreases((x % (d * k)) as nat, d as nat);
    };
}

/// Proof that multiplying the divisor by a positive number can't
/// decrease the remainder. That is, for any `x`, `d > 1`, and `k > 0`,
/// `x % d <= x % (d * k)`.
pub proof fn lemma_mod_ordering_auto()
    ensures
        forall|x: int, k: int, d: int|
            1 < d && 0 < k ==> (x % d <= #[trigger]
            (x % (d * k))),
{
    assert forall|x: int, k: int, d: int| 1 < d && 0 < k implies (x % d <= #[trigger]
    (x % (d * k))) by {
        lemma_mod_ordering(x, k, d);
    }
}

/// Proof that the remainder when `x` is divided by `a * b`, taken
/// modulo `a`, is equivalent to `x` modulo `a`. That is,
/// `(x % (a * b)) % a == x % a`.
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
    calc! { (==)
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
    lemma_fundamental_div_mod_converse(
        x,
        a,
        b * (x / (a * b)) + x % (a * b) / a,
        (x % (a * b)) % a,
    );
}

/// Proof that for any integer `x` and positive integers `a` and `b`,
/// the remainder when `x` is divided by `a * b`, taken modulo `a`,
/// is equivalent to `x` modulo `a`. In other words,
/// `(x % (a * b)) % a == x % a`.
pub proof fn lemma_mod_mod_auto()
    ensures
        forall|a: int, b: int| #![trigger a * b] 0 < a && 0 < b ==> 0 < a * b,
        forall|x: int, a: int, b: int|
            #![trigger (x % (a * b)) % a, x % a]
            0 < a && 0 < b ==> (x % (a * b)) % a == x % a,
{
    assert forall|a: int, b: int| #![trigger a * b] 0 < a && 0 < b implies 0 < a * b by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall|x: int, a: int, b: int| #![trigger x % (a * b)] 0 < a && 0 < b implies (x % (a
        * b)) % a == x % a by {
        lemma_mod_mod(x, a, b);
    }
}

/// Proof that `(x % y) % (y * z) < y`.
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

/// Proof that any nonnegative integer `x` modulo `y` modulo `y * z` is less than `y`
pub proof fn lemma_part_bound2_auto()
    ensures
        forall|y: int, z: int|
            (0 < y && 0 < z) ==> #[trigger]
            (y * z) > 0,
        forall|x: int, y: int, z: int|
            (0 <= x && 0 < y && 0 < z) ==> (#[trigger]
            (x % y) % #[trigger]
            (y * z) < y),
{
    assert forall|y: int, z: int| 0 < y && 0 < z implies #[trigger]
    (y * z) > 0 by {
        lemma_mul_strictly_positive_auto();
    };
    assert forall|x: int, y: int, z: int| 0 <= x && 0 < y && 0 < z implies #[trigger]
    (x % y) % #[trigger]
    (y * z) < y by {
        lemma_part_bound2(x, y, z);
    };
}

/// Proof of the validity of an expanded form of the modulus operation.
/// Specifically, `x % (y * z) == y * ((x / y) % z) + x % y`.
pub proof fn lemma_mod_breakdown(x: int, y: int, z: int)
    requires
        0 <= x,
        0 < y,
        0 < z,
    ensures
        y * z > 0,
        x % (y * z) == y * ((x / y) % z) + x % y,
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
    calc! { (==)
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

/// Proof of the validity of an expanded form of the modulus operation.
/// That is, for any nonnegative `x`, positive `y`, and positive `z`, we know
/// `x % (y * z) == y * ((x / y) % z) + x % y`.
pub proof fn lemma_mod_breakdown_auto()
    ensures
        forall|y: int, z: int| #![trigger y * z] 0 < y && 0 < z ==> y * z > 0,
        forall|x: int, y: int, z: int|
            #![trigger x % (y * z)]
            0 <= x && 0 < y && 0 < z ==> x % (y * z) == y * ((x / y) % z) + x % y,
{
    assert forall|y: int, z: int| #![trigger y * z] 0 < y && 0 < z implies y * z > 0 by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall|x: int, y: int, z: int| #![trigger x % (y * z)] 0 <= x && 0 < y && 0 < z implies x
        % (y * z) == y * ((x / y) % z) + x % y by {
        lemma_mod_breakdown(x, y, z);
    }
}

} // verus!
