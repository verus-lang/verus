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
use super::super::calc_macro::*;
#[allow(unused_imports)]
use super::super::prelude::*;

verus! {

#[allow(unused_imports)]
#[cfg(verus_keep_ghost)]
use super::super::arithmetic::internals::div_internals::{
    div_recursive,
    lemma_div_induction_auto,
    div_auto,
    div_pos,
    lemma_div_auto,
};
use super::super::arithmetic::internals::div_internals_nonlinear as DivINL;
#[cfg(verus_keep_ghost)]
use super::super::arithmetic::internals::mod_internals::{
    lemma_div_add_denominator,
    lemma_mod_auto,
    mod_recursive,
};
use super::super::arithmetic::internals::mod_internals_nonlinear as ModINL;
#[cfg(verus_keep_ghost)]
use super::internals::mul_internals::{
    group_mul_properties_internal,
    lemma_mul_induction,
    lemma_mul_induction_auto,
};
#[cfg(verus_keep_ghost)]
use super::super::arithmetic::internals::general_internals::{is_le};
#[cfg(verus_keep_ghost)]
use super::super::math::{add as add1, sub as sub1, div as div1};
use super::super::arithmetic::mul::*;

/*****************************************************************************
* Division
*****************************************************************************/

/// Proof that, for the case of `x / d`, division using `/` is
/// equivalent to a recursive definition of division
pub broadcast proof fn lemma_div_is_div_recursive(x: int, d: int)
    requires
        0 < d,
    ensures
        div_recursive(x, d) == #[trigger] (x / d),
{
    reveal(div_recursive);
    reveal(div_pos);
    lemma_div_induction_auto(d, x, |u: int| div_recursive(u, d) == u / d);
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

pub broadcast proof fn lemma_div_basics_1(x: int)
    ensures
        x != 0 as int ==> #[trigger] (0int / x) == 0,
{
    lemma_div_basics(x);
}

pub broadcast proof fn lemma_div_basics_2(x: int)
    ensures
        #[trigger] (x / 1) == x,
{
    lemma_div_basics(x);
}

pub broadcast proof fn lemma_div_basics_3(x: int)
    ensures
        x != 0 ==> #[trigger] (x / x) == 1,
{
    lemma_div_basics(x);
}

pub broadcast proof fn lemma_div_basics_4(x: int, y: int)
    ensures
        x >= 0 && y > 0 ==> #[trigger] (x / y) >= 0,
{
}

pub broadcast proof fn lemma_div_basics_5(x: int, y: int)
    ensures
        x >= 0 && y > 0 ==> #[trigger] (x / y) <= x,
{
    assert forall|x: int, y: int| x >= 0 && y > 0 implies 0 <= #[trigger] (x / y) <= x by {
        lemma_div_pos_is_pos(x, y);
        lemma_div_is_ordered_by_denominator(x, 1, y);
    };
}

pub broadcast group group_div_basics {
    lemma_div_basics_1,
    lemma_div_basics_2,
    lemma_div_basics_3,
    lemma_div_basics_4,
    lemma_div_basics_5,
}

// Check that the group_div_basics broadcast group group_provides the same properties as the _auto lemma it replaces
proof fn lemma_div_basics_prove_auto()
    ensures
        forall|x: int| x != 0 ==> #[trigger] (0int / x) == 0,
        forall|x: int| #[trigger] (x / 1) == x,
        forall|x: int, y: int| x >= 0 && y > 0 ==> #[trigger] (x / y) >= 0,
        forall|x: int, y: int| x >= 0 && y > 0 ==> #[trigger] (x / y) <= x,
{
    broadcast use group_div_basics;

}

/// Proof that if a dividend is a whole number, the divisor is a
/// natural number, and their quotient is 0, then the dividend is
/// smaller than the divisor
pub broadcast proof fn lemma_small_div_converse(x: int, d: int)
    ensures
        0 <= x && 0 < d && #[trigger] (x / d) == 0 ==> x < d,
{
    assert forall|x: int, d: int| 0 <= x && 0 < d && #[trigger] (x / d) == 0 implies x < d by {
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
        #[trigger] (x / d) > 0,
{
    broadcast use lemma_div_pos_is_pos;

    if x / d == 0 {
        broadcast use lemma_small_div_converse;

    }
}

/// Proof that given two fractions with the same numerator, the order
/// of the fractions is determined by the denominators. However, if
/// the numerator is 0, the fractions are equal regardless of the
/// denominators' values. Specifically, given that `1 <= y <= z`, we
/// know `x / y >= x / z`.
pub broadcast proof fn lemma_div_is_ordered_by_denominator(x: int, y: int, z: int)
    requires
        0 <= x,
        1 <= y <= z,
    ensures
        #[trigger] (x / y) >= #[trigger] (x / z),
    decreases x,
{
    reveal(div_recursive);
    reveal(div_pos);
    broadcast use lemma_div_is_div_recursive;

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

/// Proof that a number gets strictly smaller when divided by a number
/// greater than one. Specifically, `x / d < x`.
pub broadcast proof fn lemma_div_is_strictly_smaller(x: int, d: int)
    requires
        0 < x,
        1 < d,
    ensures
        #[trigger] (x / d) < x,
    decreases x,
{
    lemma_div_induction_auto(d, x, |u: int| 0 < u ==> u / d < u);
}

/// Proof that, given `r == a % d + b % d - (a + b) % d`, `r` can also
/// be expressed as `d * ((a + b) / d) - d * (a / d) - d * (b / d)`
pub broadcast proof fn lemma_dividing_sums(a: int, b: int, d: int, r: int)
    requires
        0 < d,
        r == a % d + b % d - (a + b) % d,
    ensures
        #![trigger (d * ((a + b) / d) - r), (d * (a / d) + d * (b / d))]
        d * ((a + b) / d) - r == d * (a / d) + d * (b / d),
{
    ModINL::lemma_fundamental_div_mod(a + b, d);
    ModINL::lemma_fundamental_div_mod(a, d);
    ModINL::lemma_fundamental_div_mod(b, d);
}

/// Proof that dividing a whole number by a natural number will result
/// in a quotient that is greater than or equal to 0. Specifically,
/// `x / d >= 0`.
pub broadcast proof fn lemma_div_pos_is_pos(x: int, d: int)
    requires
        0 <= x,
        0 < d,
    ensures
        0 <= #[trigger] (x / d),
{
    lemma_div_auto(d);
    assert(div_auto(d));
    let f = |u: int| 0 <= u ==> u / d >= 0;
    assert forall|i: int| #[trigger] is_le(0, i) && f(i) implies f(i + d) by {
        assert(i / d >= 0);
    };
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u / d >= 0);
}

/// Proof that dividing a number then adding 1 gives the same result
/// as adding the divisor and then doing the division. Specifically,
/// `1 + (x / d)` is equal to `(d + x) / d`.
pub broadcast proof fn lemma_div_plus_one(x: int, d: int)
    requires
        0 < d,
    ensures
        #![trigger (1 + x / d), ((d + x) / d)]
        1 + x / d == (d + x) / d,
{
    lemma_div_auto(d);
}

/// Proof that dividing a number then subtracting 1 gives the same result
/// as subtracting the divisor and then doing the division. Specifically,
/// `-1 + (x / d)` is equal to `(-d + x) / d`.
pub broadcast proof fn lemma_div_minus_one(x: int, d: int)
    requires
        0 < d,
    ensures
        #![trigger (-1 + x / d), ((-d + x) / d)]
        -1 + x / d == (-d + x) / d,
{
    lemma_div_auto(d);
}

/// Proof that dividing any non-negative integer less than `d` by `d`
/// produces a quotient of 0
pub proof fn lemma_basic_div_specific_divisor(d: int)
    requires
        0 < d,
    ensures
        forall|x: int| 0 <= x < d ==> #[trigger] (x / d) == 0,
{
    lemma_div_auto(d);
}

/// Proof that dividing any non-negative integer by a larger integer
/// produces a quotient of 0
pub broadcast proof fn lemma_basic_div(x: int, d: int)
    requires
        0 <= x < d,
    ensures
        #[trigger] (x / d) == 0,
{
    lemma_basic_div_specific_divisor(d);
}

/// Proof that numerical order is preserved when dividing two seperate
/// integers by a common positive divisor. Specifically, given that
/// `z > 0` and `x <= y`, we know `x / z <= y / z`.
pub broadcast proof fn lemma_div_is_ordered(x: int, y: int, z: int)
    requires
        x <= y,
        0 < z,
    ensures
        #[trigger] (x / z) <= #[trigger] (y / z),
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

/// Proof that dividing an integer by 2 or more results in a quotient
/// that is smaller than the original dividend. Specifically, `x / d < x`.
pub broadcast proof fn lemma_div_decreases(x: int, d: int)
    requires
        0 < x,
        1 < d,
    ensures
        #[trigger] (x / d) < x,
{
    lemma_div_induction_auto(d, x, |u: int| 0 < u ==> u / d < u);
}

/// Proof that dividing an integer by 1 or more results in a quotient
/// that is less than or equal to the original dividend. Specifically,
/// `x / d <= x`.
pub broadcast proof fn lemma_div_nonincreasing(x: int, d: int)
    requires
        0 <= x,
        0 < d,
    ensures
        #[trigger] (x / d) <= x,
{
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u / d <= u);
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

// TODO: temporarily needed until `broadcast use` can be used in calc!
proof fn lemma_mul_is_distributive_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * (y + z)) == x * y + x * z,
        forall|x: int, y: int, z: int| #[trigger] ((y + z) * x) == y * x + z * x,
        forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z,
        forall|x: int, y: int, z: int| #[trigger] ((y - z) * x) == y * x - z * x,
{
    broadcast use group_mul_is_distributive;

}

// TODO: temporarily needed until `broadcast use` can be used in calc!
proof fn lemma_mul_is_commutative_auto()
    ensures
        forall|x: int, y: int| #[trigger] (x * y) == y * x,
{
    broadcast use lemma_mul_is_commutative;

}

// TODO: temporarily needed until `broadcast use` can be used in calc!
proof fn lemma_mul_basics_auto()
    ensures
        forall|x: int| #[trigger] (0 * x) == 0,
        forall|x: int| #[trigger] (x * 0) == 0,
        forall|x: int| #[trigger] (x * 1) == x,
        forall|x: int| #[trigger] (1 * x) == x,
{
    broadcast use group_mul_basics;

}

/// The remainder of a nonnegative integer `x` divided by the product of two positive integers
/// `y` and `z` is equivalent to dividing `x` by `y`, dividing the quotient by `z`, multiplying
/// the remainder by `y`, and then adding the product to the remainder of `x` divided by `y`.
/// In mathematical terms, `(x % (y * z)) == y * ((x / y) % z) + x % y`.
pub broadcast proof fn lemma_breakdown(x: int, y: int, z: int)
    requires
        0 <= x,
        0 < y,
        0 < z,
    ensures
        #![trigger y * z, x % (y * z), y * ((x / y) % z) + x % y]
        0 < y * z,
        (x % (y * z)) == y * ((x / y) % z) + x % y,
{
    broadcast use lemma_mul_strictly_positive;

    lemma_div_pos_is_pos(x, y);
    calc! {
        (<)
        (y * (x / y)) % (y * z) + (x % y) % (y * z); (<=) {
            lemma_part_bound1(x, y, z);
        }
        y * (z - 1) + (x % y) % (y * z); (<) {
            lemma_part_bound2(x, y, z);
        }
        y * (z - 1) + y; (==) {
            lemma_mul_basics_auto();
        }
        y * (z - 1) + y * 1; (==) {  /* TODO(broadcast_use) */
            lemma_mul_is_distributive_auto();
        }
        y * (z - 1 + 1); (==) {}
        y * z;
    }
    calc! {
        (==)
        x % (y * z); {
            ModINL::lemma_fundamental_div_mod(x, y);
        }
        (y * (x / y) + x % y) % (y * z); {
            lemma_mod_properties_auto();
            assert(0 <= x % y);
            lemma_mul_nonnegative(y, x / y);
            assert((y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z);
            lemma_mod_adds(y * (x / y), x % y, y * z);
        }
        (y * (x / y)) % (y * z) + (x % y) % (y * z); {
            lemma_mod_properties_auto();
            lemma_mul_increases(z, y);
            lemma_mul_is_commutative_auto();
            // comparison op can't be chained in calc!
            // assert forall is also not avaialable in calc!
            assert((x % y) < y && y <= (y * z));
            lemma_small_mod((x % y) as nat, (y * z) as nat);
            assert((x % y) % (y * z) == x % y);
        }
        (y * (x / y)) % (y * z) + x % y; {
            lemma_truncate_middle(x / y, y, z);
        }
        y * ((x / y) % z) + x % y;
    }
}

/// Proof that the difference between a nonnegative integer `x` and a
/// positive integer `d` must be strictly less than the quotient of
/// `x` divided by `d` and then multiplied by `d`
pub broadcast proof fn lemma_remainder_upper(x: int, d: int)
    requires
        0 <= x,
        0 < d,
    ensures
        #![trigger (x - d), (x / d * d)]
        x - d < x / d * d,
{
    broadcast use group_mul_properties_internal;

    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u - d < u / d * d);
}

/// Proof that the division of a nonnegative integer `x` by a positive
/// integer `d` multiplied by `d` is less than or equal to the value
/// of `x`
pub broadcast proof fn lemma_remainder_lower(x: int, d: int)
    requires
        0 <= x,
        0 < d,
    ensures
        x >= #[trigger] (x / d * d),
{
    broadcast use group_mul_properties_internal;

    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u >= u / d * d);
}

/// Proof that the difference between a nonnegative integer `x` and
/// the division of `x` by a positive integer `d` multiplied by `d` is
/// lower bounded (inclusively) by 0 and upper bounded (exclusively)
/// by `d
pub broadcast proof fn lemma_remainder(x: int, d: int)
    requires
        0 <= x,
        0 < d,
    ensures
        0 <= #[trigger] (x - (x / d * d)) < d,
{
    broadcast use group_mul_properties_internal;

    lemma_div_induction_auto(d, x, |u: int| 0 <= u - u / d * d < d);
}

/// Proof of the fundamental theorem of division and modulo, namely
/// that `x` can be expressed as `d` times the quotient `x / d` plus
/// the remainder `x % d`.
pub broadcast proof fn lemma_fundamental_div_mod(x: int, d: int)
    requires
        d != 0,
    ensures
        x == #[trigger] (d * (x / d) + (x % d)),
{
    assert(x == d * (x / d) + (x % d)) by {
        ModINL::lemma_fundamental_div_mod(x, d);
    }
}

// TODO: temporarily needed until `broadcast use` can be used in calc!
proof fn lemma_mul_is_associative_auto()
    ensures
        forall|x: int, y: int, z: int|
            #![trigger x * (y * z)]
            #![trigger (x * y) * z]
            x * (y * z) == (x * y) * z,
{
    broadcast use lemma_mul_is_associative;

}

/// Proof that dividing `x` by `c * d` is equivalent to first dividing
/// `x` by `c` and then dividing the result by `d`
pub broadcast proof fn lemma_div_denominator(x: int, c: int, d: int)
    requires
        0 <= x,
        0 < c,
        0 < d,
    ensures
        c * d != 0,
        #[trigger] ((x / c) / d) == x / (c * d),
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
        c * ((x / c) % d) + x % c; {
            lemma_mod_multiples_vanish(-k, x / c, d);
            lemma_mul_is_commutative_auto();
        }
        c * ((x / c + (-k) * d) % d) + x % c; {
            lemma_hoist_over_denominator(x, (-k) * d, c as nat);
        }
        c * (((x + (((-k) * d) * c)) / c) % d) + x % c; {
            lemma_mul_is_associative(-k, d, c);
        }
        c * (((x + ((-k) * (d * c))) / c) % d) + x % c; {
            lemma_mul_unary_negation(k, d * c);
        }
        c * (((x + (-(k * (d * c)))) / c) % d) + x % c; {
            lemma_mul_is_associative(k, d, c);
        }
        c * (((x + (-(k * d * c))) / c) % d) + x % c; {}
        c * (((x - k * d * c) / c) % d) + x % c; {
            lemma_mul_is_associative_auto();
            lemma_mul_is_commutative_auto();
        }
        c * ((r / c) % d) + x % c; {}
        c * (r / c) + x % c; {
            lemma_fundamental_div_mod(r, c);
            assert(r == c * (r / c) + r % c);
            lemma_mod_mod(x, c, d);
            assert(r % c == x % c);
        }
        r; {
            lemma_mod_properties_auto();
            lemma_mod_is_mod_recursive_auto();
        }
        r % (c * d); {}
        (x - (c * d) * k) % (c * d); {
            lemma_mul_unary_negation(c * d, k);
        }
        (x + (c * d) * (-k)) % (c * d); {
            lemma_mod_multiples_vanish(-k, x, c * d);
        }
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

/// Proof that multiplying an integer by a fraction is equivalent to
/// multiplying the fraction's numerator by the integer. Specifically,
/// `x * (y / z) == (x * y) / z`.
pub broadcast proof fn lemma_mul_hoist_inequality(x: int, y: int, z: int)
    requires
        0 <= x,
        0 < z,
    ensures
        #![trigger (x * (y / z)), ((x * y) / z)]
        x * (y / z) <= (x * y) / z,
{
    calc! {
        (==)
        (x * y) / z; (==) {
            lemma_fundamental_div_mod(y, z);
        }
        (x * (z * (y / z) + y % z)) / z; (==) {
            lemma_mul_is_distributive_auto();
        }
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

/// Proof that for a positive integer `d`, if `a - a % d` is less than
/// or equal to `b` and `b` is less than `a + d - a % d`, then the
/// quotient of `a` divided by `d` is equivalent to the quotient of
/// `b` divided by `d`.
///
/// In other words, if `a` and `b` occur between the same two
/// multiples of `d`, then their quotient with `d` is equivalent.
pub broadcast proof fn lemma_indistinguishable_quotients(a: int, b: int, d: int)
    requires
        0 < d,
        0 <= a - a % d <= b < a + d - a % d,
    ensures
        #![trigger (a / d), (b / d)]
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

/// Proof that common factors from the dividend and divisor of a
/// modulus operation can be factored out. Specifically,
/// `(b * x) % (b * c) == b * (x % c)`.
pub proof fn lemma_truncate_middle(x: int, b: int, c: int)
    requires
        0 <= x,
        0 < b,
        0 < c,
    ensures
        #![trigger (b * (x % c))]
        0 < b * c,
        (b * x) % (b * c) == b * (x % c),
{
    broadcast use lemma_mul_strictly_positive, lemma_mul_nonnegative;

    calc! {
        (==)
        b * x; {
            ModINL::lemma_fundamental_div_mod(b * x, b * c);
        }
        (b * c) * ((b * x) / (b * c)) + (b * x) % (b * c); {
            lemma_div_denominator(b * x, b, c);
        }
        (b * c) * (((b * x) / b) / c) + (b * x) % (b * c); {
            lemma_mul_is_commutative_auto();
            lemma_div_by_multiple(x, b);
        }
        (b * c) * (x / c) + (b * x) % (b * c);
    }
    assert(b * x == (b * c) * (x / c) + b * (x % c)) by {
        ModINL::lemma_fundamental_div_mod(x, c);
        lemma_mul_is_distributive_auto();
        lemma_mul_is_associative_auto();
    };
}

/// Proof that multiplying the numerator and denominator by an integer
/// does not change the quotient. Specifically,
/// `a / d == (x * a) / (x * d)`.
pub broadcast proof fn lemma_div_multiples_vanish_quotient(x: int, a: int, d: int)
    requires
        0 < x,
        0 <= a,
        0 < d,
    ensures
        #![trigger a / d, x * a, x * d]
        0 < x * d,
        a / d == (x * a) / (x * d),
{
    lemma_mul_strictly_positive(x, d);
    calc! {
        (==)
        (x * a) / (x * d); {
            lemma_mul_nonnegative(x, a);
            lemma_div_denominator(x * a, x, d);
        }
        ((x * a) / x) / d; {
            lemma_div_multiples_vanish(a, x);
        }
        a / d;
    }
}

/// Proof that, since `a % d == 0` and `0 <= r < d`, we can conclude
/// `a == d * (a + r) / d`
pub broadcast proof fn lemma_round_down(a: int, r: int, d: int)
    requires
        0 < d,
        a % d == 0,
        0 <= r < d,
    ensures
        #![trigger (d * ((a + r) / d))]
        a == d * ((a + r) / d),
{
    broadcast use group_mul_properties_internal;

    lemma_div_induction_auto(d, a, |u: int| u % d == 0 ==> u == d * ((u + r) / d));
}

/// Proof that, since `0 <= b < d`, we have `(d * x + b) / d == x`
pub broadcast proof fn lemma_div_multiples_vanish_fancy(x: int, b: int, d: int)
    requires
        0 < d,
        0 <= b < d,
    ensures
        #![trigger (d * x + b) / d]
        (d * x + b) / d == x,
{
    let f = |u: int| (d * u + b) / d == u;
    assert(f(0)) by {
        lemma_div_auto(d);
    }
    assert forall|i: int| i >= 0 && #[trigger] f(i) implies #[trigger] f(add1(i, 1)) by {
        assert(d * (i + 1) + b == d * i + b + d) by {
            assert(d * (i + 1) == d * i + d) by {
                lemma_mul_is_distributive_add(d, i, 1);
                lemma_mul_basics(d);
            }
        }
        super::internals::div_internals::lemma_div_basics(d);
    }
    assert forall|i: int| i <= 0 && #[trigger] f(i) implies #[trigger] f(sub1(i, 1)) by {
        assert(d * (i - 1) + b == d * i + b - d) by {
            assert(d * (i - 1) == d * i - d) by {
                lemma_mul_is_distributive_sub(d, i, 1);
                lemma_mul_basics(d);
            }
        }
        super::internals::div_internals::lemma_div_basics(d);
    }
    broadcast use group_mul_properties_internal;

    lemma_mul_induction(f);
    assert(f(x));
}

/// Proof that multiplying an integer by a common numerator and
/// denominator results in the original integer. Specifically,
/// `(d * x) / d == x`.
pub broadcast proof fn lemma_div_multiples_vanish(x: int, d: int)
    requires
        0 < d,
    ensures
        #![trigger (d * x) / d]
        (d * x) / d == x,
{
    lemma_div_multiples_vanish_fancy(x, 0, d);
}

/// Proof that multiplying a whole number by a common numerator and
/// denominator results in the original integer. Specifically,
/// `(b * d) / d == b`.
pub broadcast proof fn lemma_div_by_multiple(b: int, d: int)
    requires
        0 <= b,
        0 < d,
    ensures
        #![trigger ((b * d) / d)]
        (b * d) / d == b,
{
    lemma_div_multiples_vanish(b, d);
    broadcast use group_mul_properties_internal;

}

/// Proof that a dividend that is a positive multiple of a divisor
/// will always yield a greater quotient than a smaller dividend.
/// Specifically, `x / z < y / z` because `y == m * z` and `x < y`.
pub broadcast proof fn lemma_div_by_multiple_is_strongly_ordered(x: int, y: int, m: int, z: int)
    requires
        x < y,
        y == m * z,
        0 < z,
    ensures
        #![trigger x / z, m * z, y / z]
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

/// Proof that if an integer is less than or equal to the product of
/// two other integers, then the quotient with one of them will be
/// less than or equal to the other of them. Specifically, because
/// `a <= b * c`, we know `a / b <= c`.
pub broadcast proof fn lemma_multiply_divide_le(a: int, b: int, c: int)
    requires
        0 < b,
        a <= b * c,
    ensures
        #![trigger a / b, b * c]
        a / b <= c,
{
    lemma_mod_multiples_basic(c, b);
    let f = |i: int| 0 <= i && (i + a) % b == 0 ==> a / b <= (i + a) / b;
    lemma_div_induction_auto(b, b * c - a, f);
    lemma_div_multiples_vanish(c, b);
}

/// Proof that if an integer is less than the product of two other
/// integers, then the quotient with one of them will be less than the
/// other. Specifically, because `a < b * c`, we know `a / b < c`.
pub broadcast proof fn lemma_multiply_divide_lt(a: int, b: int, c: int)
    requires
        0 < b,
        a < b * c,
    ensures
        #![trigger a / b, b * c]
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

/// Proof that adding an integer to a fraction is equivalent to adding
/// that integer times the denominator to the numerator. Specifically,
/// `x / d + j == (x + j * d) / d`.
pub broadcast proof fn lemma_hoist_over_denominator(x: int, j: int, d: nat)
    requires
        0 < d,
    ensures
        #![trigger x / d as int + j]
        x / d as int + j == (x + j * d) / d as int,
{
    let dd = d as int;
    let q = x / dd;
    let r = x % dd;
    assert(x == dd * q + r) by {
        lemma_fundamental_div_mod(x, dd);
    }
    assert(j * dd == dd * j) by {
        lemma_mul_is_commutative(j, dd);
    }
    assert(x + j * dd == dd * (q + j) + r) by {
        lemma_mul_is_distributive_add(dd, q, j);
    }
    assert((x + j * dd) / dd == q + j) by {
        lemma_fundamental_div_mod_converse(x + j * d, dd, q + j, r);
    }
}

/// Proof that, for nonnegative integer `a` and positive integers `b` and `c`,
/// the remainder of `b * (a / b)` divided by `b * c` is less than or equal to `b * (c - 1)`.
/// This accounts for the rounding down that occurs in integer division.
pub broadcast proof fn lemma_part_bound1(a: int, b: int, c: int)
    requires
        0 <= a,
        0 < b,
        0 < c,
    ensures
        #![trigger (b * (a / b) % (b * c))]
        0 < b * c,
        (b * (a / b) % (b * c)) <= b * (c - 1),
{
    lemma_mul_strictly_positive(b, a / b);
    lemma_mul_strictly_positive(b, c);
    lemma_mul_strictly_positive(b, c - 1);
    calc! {
        (==)
        b * (a / b) % (b * c); {
            ModINL::lemma_fundamental_div_mod(b * (a / b), b * c);
        }
        b * (a / b) - (b * c) * ((b * (a / b)) / (b * c)); {
            lemma_mul_is_associative_auto();
        }
        b * (a / b) - b * (c * ((b * (a / b)) / (b * c))); {
            lemma_mul_is_distributive_auto();
        }
        b * ((a / b) - (c * ((b * (a / b)) / (b * c))));
    }
    assert(b * (a / b) % (b * c) <= b * (c - 1)) by {
        broadcast use lemma_mul_is_commutative, lemma_mul_inequality;

    };
}

/*******************************************************************************
* Modulus
*******************************************************************************/

/// Proof that computing the modulus using `%` is equivalent to
/// computing it with a recursive definition of modulus. Specifically,
/// `x % m` is equivalent in that way.
pub broadcast proof fn lemma_mod_is_mod_recursive(x: int, m: int)
    requires
        m > 0,
    ensures
        mod_recursive(x, m) == #[trigger] (x % m),
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
            mod_recursive(x + m, m); {
                lemma_mod_is_mod_recursive(x + m, m);
            }
            (x + m) % m; {
                lemma_add_mod_noop(x, m, m);
            }
            ((x % m) + (m % m)) % m; {
                lemma_mod_basics_auto();
            }
            (x % m) % m; {
                lemma_mod_basics_auto();
            }
            x % m;
        }
    } else if x < m {
        lemma_small_mod(x as nat, m as nat);
    } else {
        calc! {
            (==)
            mod_recursive(x, m); {}
            mod_recursive(x - m, m); {
                lemma_mod_is_mod_recursive(x - m, m);
            }
            (x - m) % m; {
                lemma_sub_mod_noop(x, m, m);
            }
            ((x % m) - (m % m)) % m; {
                lemma_mod_basics_auto();
            }
            (x % m) % m; {
                lemma_mod_basics_auto();
            }
            x % m;
        }
    }
}

// TODO: temporarily needed until `broadcast use` can be used in calc!
proof fn lemma_mod_is_mod_recursive_auto()
    ensures
        forall|x: int, d: int| d > 0 ==> mod_recursive(x, d) == #[trigger] (x % d),
{
    broadcast use lemma_mod_is_mod_recursive;

}

// TODO: temporarily needed until `broadcast use` can be used in calc!
proof fn lemma_mod_basics_auto()
    ensures
        forall|m: int| m > 0 ==> #[trigger] (m % m) == 0,
        forall|x: int, m: int| m > 0 ==> #[trigger] ((x % m) % m) == x % m,
{
    broadcast use lemma_mod_self_0, lemma_mod_twice;

}

/// Proof that any integer divided by itself produces a remainder of 0.
pub broadcast proof fn lemma_mod_self_0(m: int)
    requires
        m > 0,
    ensures
        #[trigger] (m % m) == 0,
{
    lemma_mod_auto(m);
}

/// Proof that performing `(x % m) % m` gives the same result as simply perfoming `x % m`.
pub broadcast proof fn lemma_mod_twice(x: int, m: int)
    requires
        m > 0,
    ensures
        #[trigger] ((x % m) % m) == x % m,
{
    lemma_mod_auto(m);
}

pub broadcast group group_mod_basics {
    lemma_mod_self_0,
    lemma_mod_twice,
}

/// Proof that the remainder of any division will be less than the divisor's value.
pub broadcast proof fn lemma_mod_division_less_than_divisor(x: int, m: int)
    requires
        m > 0,
    ensures
        0 <= #[trigger] (x % m) < m,
{
    lemma_mod_auto(m);
}

pub broadcast group group_mod_properties {
    group_mod_basics,
    lemma_mod_division_less_than_divisor,
}

// Check that the mod_properties_auto broadcast group group_provides the same properties as the _auto lemma it replaces
// TODO: temporarily needed until `broadcast use` can be used in calc!
proof fn lemma_mod_properties_auto()
    ensures
        forall|m: int| m > 0 ==> #[trigger] (m % m) == 0,
        forall|x: int, m: int| m > 0 ==> #[trigger] ((x % m) % m) == x % m,
        forall|x: int, m: int| m > 0 ==> 0 <= #[trigger] (x % m) < m,
{
    broadcast use group_mod_properties;

}

/// Proof that when natural number `x` is divided by natural number
/// `m`, the remainder will be less than or equal to `x`.
pub broadcast proof fn lemma_mod_decreases(x: nat, m: nat)
    requires
        0 < m,
    ensures
        #[trigger] (x % m) <= x,
{
    lemma_mod_auto(m as int);
}

/// Proof that if `x % m` is zero and `x` is positive, then `x >= m`.
pub broadcast proof fn lemma_mod_is_zero(x: nat, m: nat)
    requires
        x > 0 && m > 0,
        #[trigger] (x % m) == 0,
    ensures
        x >= m,
{
    if (x < m) {
        lemma_small_mod(x, m);
    }
}

/// Proof that multiplying by a number then dividing by that same
/// number produces a remainder of 0. Specifically, `(x * m) % m == 0`.
#[verifier::spinoff_prover]
pub broadcast proof fn lemma_mod_multiples_basic(x: int, m: int)
    requires
        m > 0,
    ensures
        #[trigger] ((x * m) % m) == 0,
{
    lemma_mod_auto(m);
    broadcast use group_mul_properties_internal;

    let f = |u: int| (u * m) % m == 0;
    lemma_mul_induction(f);
    assert(f(x));
}

/// Proof that adding the divisor to the dividend doesn't change the
/// remainder. Specifically, `(m + b) % m == b % m`.
pub broadcast proof fn lemma_mod_add_multiples_vanish(b: int, m: int)
    requires
        0 < m,
    ensures
        (m + b) % m == #[trigger] (b % m),
{
    lemma_mod_auto(m);
}

/// Proof that subtracting the divisor from the dividend doesn't
/// change the remainder. Specifically, `(-m + b) % m == b % m`.
pub broadcast proof fn lemma_mod_sub_multiples_vanish(b: int, m: int)
    requires
        0 < m,
    ensures
        (-m + b) % m == #[trigger] (b % m),
{
    lemma_mod_auto(m);
}

/// Proof that adding any multiple of the divisor to the dividend will produce the
/// same remainder. In other words, `(m * a + b) % m == b % m`.
#[verifier::spinoff_prover]
pub broadcast proof fn lemma_mod_multiples_vanish(a: int, b: int, m: int)
    requires
        0 < m,
    ensures
        #[trigger] ((m * a + b) % m) == b % m,
    decreases
            (if a > 0 {
                a
            } else {
                -a
            }),
{
    lemma_mod_auto(m);
    broadcast use group_mul_properties_internal;

    let f = |u: int| (m * u + b) % m == b % m;
    lemma_mul_induction(f);
    assert(f(a));
}

/// Proof that modulo distributes over subtraction if the subtracted value is
/// less than or equal to the modulo of the number it's being subtracted from.
/// Specifically, because `0 <= s <= x % d`, we can conclude that
/// `x % d - s % d == (x - s) % d`.
pub broadcast proof fn lemma_mod_subtraction(x: nat, s: nat, d: nat)
    requires
        0 < d,
        0 <= s <= x % d,
    ensures
        #![trigger ((x - s) % d as int)]
        x % d - s % d == (x - s) % d as int,
{
    lemma_mod_auto(d as int);
}

/// Proof that modulo distributes over addition, provided you do an
/// extra modulo after adding the remainders. Specifically,
/// `((x % m) + (y % m)) % m == (x + y) % m`.
pub broadcast proof fn lemma_add_mod_noop(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        #![trigger (x + y) % m]
        ((x % m) + (y % m)) % m == (x + y) % m,
{
    lemma_mod_auto(m);
}

/// Proof that describes an expanded and succinct version of modulus
/// operator in relation to addition. Specifically,
/// `(x + (y % m)) % m == (x + y) % m`.
pub broadcast proof fn lemma_add_mod_noop_right(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        #![trigger (x + y) % m]
        (x + (y % m)) % m == (x + y) % m,
{
    lemma_mod_auto(m);
}

/// Proof that modulo distributes over subtraction provided you do an
/// extra modulo operation after subtracting the remainders.
/// Specifically, `((x % m) - (y % m)) % m == (x - y) % m`.
pub broadcast proof fn lemma_sub_mod_noop(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        #![trigger (x - y) % m]
        ((x % m) - (y % m)) % m == (x - y) % m,
{
    lemma_mod_auto(m);
}

/// Proof that describes an expanded and succinct version of modulus
/// operator in relation to subtraction. Specifically,
/// `(x - (y % m)) % m == (x - y) % m`.
pub broadcast proof fn lemma_sub_mod_noop_right(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        #![trigger ((x - y) % m)]
        (x - (y % m)) % m == (x - y) % m,
{
    lemma_mod_auto(m);
}

/// Proof of two properties of the sum of two remainders with the same dividend:
/// 1) `a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d)`.
/// 2) `(a % d + b % d) < d ==> a % d + b % d == (a + b) % d`.
pub broadcast proof fn lemma_mod_adds(a: int, b: int, d: int)
    requires
        0 < d,
    ensures
        #![trigger ((a + b) % d)]
        a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d),
        (a % d + b % d) < d ==> a % d + b % d == (a + b) % d,
{
    broadcast use group_mul_properties_internal;

    lemma_div_auto(d);
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
        assert(f(0) && (forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, 1))) && (
        forall|i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub1(i, 1)))) by {
            broadcast use group_mul_properties_internal;

            lemma_mod_auto(d);
        };
        lemma_mul_induction(f);
        assert(f(x));
    }
    broadcast use group_mul_properties_internal;

}

/// This proof isn't exported from this module. It's just used in
/// the proof of [`lemma_fundamental_div_mod_converse`].
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
/// the proof of [`lemma_fundamental_div_mod_converse`].
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
/// know that `r` is the remainder `x % d`.
pub broadcast proof fn lemma_fundamental_div_mod_converse_mod(x: int, d: int, q: int, r: int)
    requires
        d != 0,
        0 <= r < d,
        x == #[trigger] (q * d + r),
    ensures
        r == #[trigger] (x % d),
{
    lemma_fundamental_div_mod_converse_helper_1(q, d, r);
    assert(q == (q * d + r) / d);
    lemma_fundamental_div_mod_converse_helper_2(q, d, r);
}

/// Proof of the converse of the fundamental property of division and modulo.
/// Specifically, if we know `0 <= r < d` and `x == q * d + r`, then we
/// know that `q` is the quotient `x / d`.
pub broadcast proof fn lemma_fundamental_div_mod_converse_div(x: int, d: int, q: int, r: int)
    requires
        d != 0,
        0 <= r < d,
        x == #[trigger] (q * d + r),
    ensures
        q == #[trigger] (x / d),
{
    lemma_fundamental_div_mod_converse_helper_1(q, d, r);
    assert(q == (q * d + r) / d);
    lemma_fundamental_div_mod_converse_helper_2(q, d, r);
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
        r == x % d,
        q == x / d,
{
    lemma_fundamental_div_mod_converse_mod(x, d, q, r);
    lemma_fundamental_div_mod_converse_div(x, d, q, r);
}

pub broadcast group group_fundamental_div_mod_converse {
    lemma_fundamental_div_mod_converse_mod,
    lemma_fundamental_div_mod_converse_div,
}

// Check that the group_fundamental_div_mod_converse broadcast group group_provides the same properties as the _auto lemma it replaces
/// Proof of the converse of the fundamental property of division and
/// modulo. That is, whenever `0 <= r < d` and `x == q * d + r`, we
/// know that `q` is the quotient `x / d` and `r` is the remainder `x % d`.
proof fn lemma_fundamental_div_mod_converse_prove_auto()
    ensures  // forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) ==> q == (x / d) && r == #[trigger](x % d),

        forall|x: int, d: int, q: int, r: int|
            d != 0 && 0 <= r < d && x == #[trigger] (q * d + r) ==> q == #[trigger] (x / d),
        forall|x: int, d: int, q: int, r: int|
            d != 0 && 0 <= r < d && x == #[trigger] (q * d + r) ==> r == #[trigger] (x % d),
{
    broadcast use group_fundamental_div_mod_converse;

}

/// Proof that the remainder, when natural number `x` is divided by
/// positive integer `m`, is less than `m`.
pub broadcast proof fn lemma_mod_pos_bound(x: int, m: int)
    requires
        0 <= x,
        0 < m,
    ensures
        0 <= #[trigger] (x % m) < m,
{
    lemma_mod_auto(m);
}

/// Proof that when integer `x` is divided by positive integer `m`,
/// the remainder is nonegative and less than `m`.
pub broadcast proof fn lemma_mod_bound(x: int, m: int)
    requires
        0 < m,
    ensures
        0 <= #[trigger] (x % m) < m,
{
    ModINL::lemma_mod_range(x, m);
}

/// Proof that the remainder when `x * y` is divided by `m` is
/// equivalent to the remainder when `(x % m) * y` is divided by `m`
pub broadcast proof fn lemma_mul_mod_noop_left(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        (x % m) * y % m == #[trigger] (x * y % m),
{
    lemma_mod_auto(m);
    lemma_mul_induction_auto(y, |u: int| (x % m) * u % m == x * u % m);
}

/// Proof that the remainder when `x * y` is divided by `m` is
/// equivalent to the remainder when `x * (y % m)` is divided by `m`.
pub broadcast proof fn lemma_mul_mod_noop_right(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        x * (y % m) % m == #[trigger] ((x * y) % m),
{
    lemma_mod_auto(m);
    lemma_mul_induction_auto(x, |u: int| u * (y % m) % m == (u * y) % m);
}

/// Proof of various properties about modulo equivalence with respect
/// to multiplication, specifically various expressions that `(x * y)
/// % m` is equivalent to.
pub broadcast proof fn lemma_mul_mod_noop_general(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        ((x % m) * y) % m == (x * y) % m,
        (x * (y % m)) % m == (x * y) % m,
        ((x % m) * (y % m)) % m == #[trigger] ((x * y) % m),
{
    lemma_mul_mod_noop_left(x, y, m);
    lemma_mul_mod_noop_right(x, y, m);
    lemma_mul_mod_noop_right(x % m, y, m);
}

/// Proof that modulo distributes over multiplication, provided you do
/// an extra modulo operation after multiplying the remainders. Specifically,
/// `(x % m) * (y % m) % m == (x * y) % m`.
pub broadcast proof fn lemma_mul_mod_noop(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        (x % m) * (y % m) % m == #[trigger] ((x * y) % m),
{
    lemma_mul_mod_noop_general(x, y, m);
}

/// Proof that `x` and `y` are congruent modulo `m` if and only if `x
/// - y` is congruent to 0 modulo `m`. In other words, `x % m == y % m
/// <==> (x - y) % m == 0`.
///
/// Note: The Dafny standard library uses the triggers `x % m, y % m`
/// for the broadcasted forall quantifier. But this can lead to a trigger loop,
/// so we don't do that here.
pub broadcast proof fn lemma_mod_equivalence(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        #![trigger (x - y) % m]
        x % m == y % m <==> (x - y) % m == 0,
{
    lemma_mod_auto(m);
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
pub broadcast proof fn lemma_mod_mul_equivalent(x: int, y: int, z: int, m: int)
    requires
        m > 0,
        is_mod_equivalent(x, y, m),
    ensures
        #[trigger] is_mod_equivalent(x * z, y * z, m),
{
    lemma_mul_mod_noop_left(x, z, m);
    lemma_mul_mod_noop_left(y, z, m);
    lemma_mod_equivalence(x, y, m);
    lemma_mod_equivalence(x * z, y * z, m);
}

// TODO: temporarily needed until `broadcast use` can be used in calc!
proof fn lemma_mul_is_distributive_sub_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z,
{
    broadcast use lemma_mul_is_distributive_sub;

}

/// Proof that multiplying the divisor by a positive number can't
/// decrease the remainder. Specifically, because `k > 0`, we have
/// `x % d <= x % (d * k)`.
pub broadcast proof fn lemma_mod_ordering(x: int, k: int, d: int)
    requires
        1 < d,
        0 < k,
    ensures
        0 < d * k,
        x % d <= #[trigger] (x % (d * k)),
{
    lemma_mul_strictly_increases(d, k);
    calc! {
        (==)
        x % d + d * (x / d); {
            lemma_fundamental_div_mod(x, d);
        }
        x; {
            lemma_fundamental_div_mod(x, d * k);
        }
        x % (d * k) + (d * k) * (x / (d * k)); {
            lemma_mul_is_associative_auto();
        }
        x % (d * k) + d * (k * (x / (d * k)));
    }
    calc! {
        (==)
        x % d; {
            lemma_mod_properties_auto();
        }
        (x % d) % d; {
            lemma_mod_multiples_vanish(x / d - k * (x / (d * k)), x % d, d);
        }
        (x % d + d * (x / d - k * (x / (d * k)))) % d; {
            lemma_mul_is_distributive_sub_auto();
        }
        (x % d + d * (x / d) - d * (k * (x / (d * k)))) % d; {}
        (x % (d * k)) % d;
    }
    assert((x % (d * k)) % d <= x % (d * k)) by {
        broadcast use group_mod_properties;

        lemma_mod_decreases((x % (d * k)) as nat, d as nat);
    };
}

/// Proof that the remainder when `x` is divided by `a * b`, taken
/// modulo `a`, is equivalent to `x` modulo `a`. That is,
/// `(x % (a * b)) % a == x % a`.
pub broadcast proof fn lemma_mod_mod(x: int, a: int, b: int)
    requires
        0 < a,
        0 < b,
    ensures
        #![trigger (x % (a * b)) % a, x % a]
        0 < a * b,
        (x % (a * b)) % a == x % a,
{
    broadcast use lemma_mul_strictly_positive;

    calc! {
        (==)
        x; {
            lemma_fundamental_div_mod(x, a * b);
        }
        (a * b) * (x / (a * b)) + x % (a * b); {
            lemma_mul_is_associative_auto();
        }
        a * (b * (x / (a * b))) + x % (a * b); {
            lemma_fundamental_div_mod(x % (a * b), a);
        }
        a * (b * (x / (a * b))) + a * (x % (a * b) / a) + (x % (a * b)) % a; {
            lemma_mul_is_distributive_auto();
        }
        a * (b * (x / (a * b)) + x % (a * b) / a) + (x % (a * b)) % a;
    }
    broadcast use group_mod_properties, lemma_mul_is_commutative;

    lemma_fundamental_div_mod_converse(
        x,
        a,
        b * (x / (a * b)) + x % (a * b) / a,
        (x % (a * b)) % a,
    );
}

/// Proof that `(x % y) % (y * z) < y`.
pub broadcast proof fn lemma_part_bound2(x: int, y: int, z: int)
    requires
        0 <= x,
        0 < y,
        0 < z,
    ensures
        y * z > 0,
        #[trigger] (x % y) % #[trigger] (y * z) < y,
{
    broadcast use lemma_mul_strictly_positive;

    lemma_mod_properties_auto();
    assert(x % y < y);
    broadcast use lemma_mul_is_commutative, lemma_mul_increases;

    assert(y <= y * z);
    assert(0 <= x % y < y * z);
    lemma_mod_properties_auto();
    lemma_small_mod((x % y) as nat, (y * z) as nat);
    assert((x % y) % (y * z) == x % y);
}

/// Proof of the validity of an expanded form of the modulus operation.
/// Specifically, `x % (y * z) == y * ((x / y) % z) + x % y`.
pub broadcast proof fn lemma_mod_breakdown(x: int, y: int, z: int)
    requires
        0 <= x,
        0 < y,
        0 < z,
    ensures
        #![trigger x % (y * z)]
        y * z > 0,
        x % (y * z) == y * ((x / y) % z) + x % y,
{
    broadcast use lemma_mul_strictly_positive;

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
        x % (y * z); {
            lemma_fundamental_div_mod(x, y);
        }
        (y * (x / y) + x % y) % (y * z); {
            lemma_mod_properties_auto();
            assert(0 <= x % y);
            lemma_mul_nonnegative(y, x / y);
            assert((y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z);
            lemma_mod_adds(y * (x / y), x % y, y * z);
        }
        (y * (x / y)) % (y * z) + (x % y) % (y * z); {
            lemma_mod_properties_auto();
            lemma_mul_increases(z, y);
            lemma_mul_is_commutative_auto();
            assert(x % y < y && y <= y * z);
            lemma_small_mod((x % y) as nat, (y * z) as nat);
            assert((x % y) % (y * z) == x % y);
        }
        (y * (x / y)) % (y * z) + x % y; {
            lemma_truncate_middle(x / y, y, z);
        }
        y * ((x / y) % z) + x % y;
    }
}

} // verus!
