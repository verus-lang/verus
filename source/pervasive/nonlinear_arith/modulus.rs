//! This file contains proofs related to integer modulo operations.
//! These are part of the math standard library.
//!
//! It's based on the second part (since the first part is about
//! division) of the following file from the Dafny math standard
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
use crate::nonlinear_arith::math::{add as add1, sub as sub1};

verus! {
use crate::nonlinear_arith::mul::*;
use crate::nonlinear_arith::div::*;
use crate::nonlinear_arith::internals::div_internals::{lemma_div_auto};
use crate::nonlinear_arith::internals::div_internals_nonlinear::{lemma_small_div};
use crate::nonlinear_arith::internals::mod_internals::{lemma_div_add_denominator, lemma_mod_auto, mod_recursive};
use crate::nonlinear_arith::internals::mul_internals::{lemma_mul_induction_auto, lemma_mul_auto, lemma_mul_induction};

/// Proof that computing the modulus using `%` is equivalent to
/// computing it with [`mod_recursive`]. Specifically,
/// `x % m == mod_recursive(x, m)`.
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

/// Proof that computing the modulus using `%` is equivalent to
/// computing it with [`mod_recursive`]
pub proof fn lemma_mod_is_mod_recursive_auto()
    ensures forall |x: int, d: int| d > 0 ==> mod_recursive(x, d) == #[trigger](x % d)
{
    reveal(mod_recursive);
    assert forall |x: int, d: int| d > 0 implies mod_recursive(x, d) == #[trigger](x % d) by
    {
        lemma_mod_is_mod_recursive(x, d);
    };
}

/// Proof of basic properties of the modulus operation: any integer
/// divided by itself produces a remainder of 0; performing `(x % m) %
/// m` gives the same result as simply perfoming `x % m`.
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

/// Proof of properties of the modulus operation including those
/// described in `lemma_mod_basics_auto`. This lemma also states that
/// the remainder of any division will be less than the divisor's
/// value.
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

/// Proof that when natural number `x` is divided by natural number
/// `m`, the remainder will be less than or equal to `x`.
pub proof fn lemma_mod_decreases(x: nat, m: nat)
    requires 0 < m
    ensures x % m <= x
{
    lemma_mod_auto(m as int);
}

/// Proof that dividing any natural number `x` by any divisor produces
/// a quotient less than or equal to `x`.
pub proof fn lemma_mod_decreases_auto()
    ensures forall |x: nat, m: nat| 0 < m ==> #[trigger](x % m) <= x,
{
    assert forall |x: nat, m: nat| 0 < m implies #[trigger](x % m) <= x by
    {
        lemma_mod_decreases(x, m);
    }
}

/// Proof that if `x % m` is zero and `x` is positive, then `x >= m`.
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

/// Proof that if a remainder is zero and the dividend is positive,
/// then the dividend is greater than or equal to the divisor. In
/// other words, if `x % m == 0` and `x > 0`, then `x >= m`.
pub proof fn lemma_mod_is_zero_auto()
    ensures forall |x: nat, m: nat| x > 0 && m > 0 && #[trigger](x % m) == 0 ==> x >= m,
{
    assert forall |x: nat, m: nat| x > 0 && m > 0 && #[trigger](x % m) == 0 implies x >= m by
    {
        lemma_mod_is_zero(x, m);
    }
}

/// Proof that multiplying by a number then dividing by that same
/// number produces a remainder of 0. Specifically, `(x * m) % m == 0`.
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

/// Proof that multiplying by a number then dividing by that same
/// number produces a remainder of 0
pub proof fn lemma_mod_multiples_basic_auto()
    ensures forall |x: int, m: int| m > 0 ==> #[trigger]((x * m) % m) == 0,
{
    assert forall |x: int, m: int| m > 0 implies #[trigger]((x * m) % m) == 0 by
    {
        lemma_mod_multiples_basic(x, m);
    }
}

/// Proof that adding the divisor to the dividend doesn't change the
/// remainder. Specifically, `(m + b) % m == b % m`.
pub proof fn lemma_mod_add_multiples_vanish(b: int, m: int)
    requires 0 < m
    ensures (m + b) % m == b % m
{
    lemma_mod_auto(m);
}

/// Proof that adding the divisor to the dividend doesn't change the
/// remainder. In other words, for all `m` and `b`, `(m + b) % m == b % m`.
pub proof fn lemma_mod_add_multiples_vanish_auto()
    ensures forall |b: int, m: int| m > 0 ==> ((m + b) % m) == #[trigger](b % m),
{
    assert forall |b: int, m: int| m > 0 implies ((m + b) % m) == #[trigger](b % m) by
    {
        lemma_mod_add_multiples_vanish(b, m);
    }
}

/// Proof that subtracting the divisor from the dividend doesn't
/// change the remainder. Specifically, `(-m + b) % m == b % m`.
pub proof fn lemma_mod_sub_multiples_vanish(b: int, m: int)
    requires 0 < m
    ensures (-m + b) % m == b % m
{
    lemma_mod_auto(m);
}

/// Proof that subtracting the divisor from the dividend doesn't
/// change the remainder. In other words, for all `m` and `b`,
/// `(-m + b) % m == b % m`.
pub proof fn lemma_mod_sub_multiples_vanish_auto()
    ensures forall |b: int, m: int| m > 0 ==> ((-m + b) % m) == #[trigger](b % m),
{
    assert forall |b: int, m: int| m > 0 implies ((-m + b) % m) == #[trigger](b % m) by
    {
        lemma_mod_sub_multiples_vanish(b, m);
    }
}

/// Proof that adding any multiple of the divisor to the dividend will produce the
/// same remainder. In other words, `(m * a + b) % m == b % m`.
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

/// Proof that adding any multiple of the divisor to the dividend will produce the
/// same remainder. In other words, for all `m`, `a`, and `b`,
/// `(m * a + b) % m == b % m`.
pub proof fn lemma_mod_multiples_vanish_auto()
    ensures forall |a: int, b: int, m: int| m > 0 ==> #[trigger]((m * a + b) % m) == b % m,
{
    assert forall |a: int, b: int, m: int| m > 0 implies #[trigger]((m * a + b) % m) == b % m by
    {
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
        0 <= s <= x % d
    ensures 
        x % d - s % d == (x - s) % d as int
{
    lemma_mod_auto(d as int);
}

/// Proof that modulo distributes over subtraction if the subtracted
/// value is less than or equal to the modulo of the number it's being
/// subtracted from. In other words, for all `s`, `x`, and `d`
/// satisfying `0 <= s <= x % d`, we can conclude that `x % d - s % d
/// == (x - s) % d`.
pub proof fn lemma_mod_subtraction_auto()
    ensures forall |x: nat, s: nat, d: nat| #![trigger ((x - s) % d as int)] 0 < d && 0 <= s <= x % d ==> x % d - s % d == (x - s) % d as int,
{
    assert forall |x: nat, s: nat, d: nat| 0 < d && 0 <= s <= x % d implies x % d - s % d == #[trigger]((x - s) % d as int) as int by
    {
        lemma_mod_subtraction(x, s, d);
    }
}

/// Proof that modulo distributes over addition, provided you do an extra modulo after adding the remainders.
/// Specifically, `((x % m) + (y % m)) % m == (x + y) % m`.
pub proof fn lemma_add_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) + (y % m)) % m == (x + y) % m
{
    lemma_mod_auto(m);
}

/// Proof that modulo distributes over addition, provided you do an extra modulo after adding the remainders.
/// In other words, for all `x`, `y`, and `m`, `((x % m) + (y % m)) % m == (x + y) % m`.
pub proof fn lemma_add_mod_noop_auto()
    ensures forall |x: int, y: int, m: int| #![trigger (x + y) % m] 0 < m ==> ((x % m) + (y % m)) % m == (x + y) % m,
{
    assert forall |x: int, y: int, m: int| 0 < m implies ((x % m) + (y % m)) % m == #[trigger]((x + y) % m) by
    {
        lemma_add_mod_noop(x, y, m);
    }
}

/// Proof that describes an expanded and succinct version of modulus operator in relation to addition.
/// Specifically, `(x + (y % m)) % m == (x + y) % m`.
pub proof fn lemma_add_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures (x + (y % m)) % m == (x + y) % m
{
    lemma_mod_auto(m);
}

/// Proof that describes an expanded and succinct version of modulus operator in relation to addition.
/// That is, for all `x`, `y`, and `m`, `(x + (y % m)) % m == (x + y) % m`.
pub proof fn lemma_add_mod_noop_right_auto()
    ensures forall |x: int, y: int, m: int| #![trigger (x + y) % m] 0 < m ==> (x + (y % m)) % m == (x + y) % m,
{
    assert forall |x: int, y: int, m: int| 0 < m implies (x + (y % m)) % m == #[trigger]((x + y) % m) by
    {
        lemma_add_mod_noop_right(x, y, m);
    }
}

/// Proof that modulo distributes over subtraction provided you do an extra modulo operation after
/// subtracting the remainders. Specifically, `((x % m) - (y % m)) % m == (x - y) % m`.
pub proof fn lemma_sub_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) - (y % m)) % m == (x - y) % m
{
    lemma_mod_auto(m);
}

/// Proof that modulo distributes over subtraction provided you do an extra modulo operation after
/// subtracting the remainders. In other words, for all `x`, `y`, and `m`,
/// `((x % m) - (y % m)) % m == (x - y) % m`.
pub proof fn lemma_sub_mod_noop_auto()
    ensures forall |x: int, y: int, m: int| #![trigger (x - y) % m] 0 < m ==> ((x % m) - (y % m)) % m == (x - y) % m,
{
    assert forall |x: int, y: int, m: int| 0 < m implies ((x % m) - (y % m)) % m == #[trigger]((x - y) % m) by
    {
        lemma_sub_mod_noop(x, y, m);
    }
}

/// Proof that describes an expanded and succinct version of modulus operator in relation to subtraction.
/// Specifically, `(x - (y % m)) % m == (x - y) % m`.
pub proof fn lemma_sub_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures (x - (y % m)) % m == (x - y) % m
{
    lemma_mod_auto(m);
}

/// Proof that describes an expanded and succinct version of modulus operator in relation to subtraction.
/// That is, for all `x`, `y`, and `m`, `(x - (y % m)) % m == (x - y) % m`.
pub proof fn lemma_sub_mod_noop_right_auto()
    ensures forall |x: int, y: int, m: int| #![trigger ((x - y) % m)] 0 < m ==> (x - (y % m)) % m == (x - y) % m,
{
    assert forall |x: int, y: int, m: int| 0 < m implies (x - (y % m)) % m == #[trigger]((x - y) % m) by
    {
        lemma_sub_mod_noop_right(x, y, m);
    }
}

/// Proof of two properties of the sum of two remainders with the same dividend:
/// 1) `a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d)`.
/// 2) `(a % d + b % d) < d ==> a % d + b % d == (a + b) % d`.
pub proof fn lemma_mod_adds(a: int, b: int, d: int)
    requires 0 < d
    ensures 
        a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d),
        (a % d + b % d) < d ==> a % d + b % d == (a + b) % d
{
    lemma_mul_auto();
    lemma_div_auto(d);
}

/// Proof of two properties of the sum of two remainders with the same dividend,
/// i.e., that for all `a`, `b`, and `d`:
/// 1) `a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d)`.
/// 2) `(a % d + b % d) < d ==> a % d + b % d == (a + b) % d`.
pub proof fn lemma_mod_adds_auto()
    ensures forall |a: int, b: int, d: int| #![trigger ((a + b) % d)] 0 < d ==> a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d),
{
    assert forall |a: int, b: int, d: int| 0 < d implies a % d + b % d == #[trigger]((a + b) % d) + d * ((a % d + b % d) / d) by
    {
        lemma_mod_adds(a, b, d);
    }
}

/// Proof that the remainder when dividing integer `x` by positive
/// integer `d` is equivalent to the remainder of `x * (1 - d)` by
/// `d`.
#[verifier::spinoff_prover]
pub proof fn lemma_mod_neg_neg(x: int, d: int)
    requires 0 < d
    ensures x % d == (x * (1 - d)) % d
{
    assert ((x - x * d) % d == x % d) by {
        let f = |i: int| (x - i * d) % d == x % d;
        lemma_mul_auto();
        assert (  f(0)
                && (forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger]f(add1(i, 1)))
                && (forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger]f(sub1(i, 1)))
            )
        by {
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
        0 <= r < d
    ensures
        u == (u * d + r) / d
    decreases
        if u >= 0 { u } else { -u }
{
    if u < 0 {
        lemma_fundamental_div_mod_converse_helper_1(u + 1, d, r);
        lemma_div_add_denominator(d, u * d + r);
        lemma_mul_is_distributive_add_other_way(d, u + 1, -1);
        assert (u == (u * d + r) / d);
    }
    else if u == 0 {
        lemma_small_div();
        assert (u == 0 ==> u * d == 0) by (nonlinear_arith);
        assert (u == (u * d + r) / d);
    }
    else {
        lemma_fundamental_div_mod_converse_helper_1(u - 1, d, r);
        lemma_div_add_denominator(d, (u - 1) * d + r);
        lemma_mul_is_distributive_add_other_way(d, u - 1, 1);
        assert (u * d + r == (u - 1) * d + r + d);
        assert (u == (u * d + r) / d);
    }
}

/// This proof isn't exported from this module. It's just used in
/// the proof of `lemma_fundamental_div_mod_converse`.
proof fn lemma_fundamental_div_mod_converse_helper_2(u: int, d: int, r: int)
    requires
        d != 0,
        0 <= r < d
    ensures
        r == (u * d + r) % d
    decreases
        if u >= 0 { u } else { -u }
{
    if u < 0 {
        lemma_fundamental_div_mod_converse_helper_2(u + 1, d, r);
        lemma_mod_add_multiples_vanish(u * d + r, d);
        lemma_mul_is_distributive_add_other_way(d, u + 1, -1);
        assert (u * d == (u + 1) * d + (-1) * d);
        assert (u * d + r == (u + 1) * d + r - d);
        assert (r == (u * d + r) % d);
    }
    else if u == 0 {
        assert (u == 0 ==> u * d == 0) by (nonlinear_arith);
        if d > 0 {
            lemma_small_mod(r as nat, d as nat);
        }
        else {
            lemma_small_mod(r as nat, (-d) as nat);
        }
        assert (r == (u * d + r) % d);
    }
    else {
        lemma_fundamental_div_mod_converse_helper_2(u - 1, d, r);
        lemma_mod_add_multiples_vanish((u - 1) * d + r, d);
        lemma_mul_is_distributive_add_other_way(d, u - 1, 1);
        assert (u * d + r == (u - 1) * d + r + d);
        assert (r == (u * d + r) % d);
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
        r == x % d
{
    lemma_fundamental_div_mod_converse_helper_1(q, d, r);
    assert (q == (q * d + r) / d);
    lemma_fundamental_div_mod_converse_helper_2(q, d, r);
}

/// Proof of the converse of the fundamental property of division and
/// modulo. That is, whenever `0 <= r < d` and `x == q * d + r`, we
/// know that `q` is the quotient `x / d` and `r` is the remainder `x % d`.
pub proof fn lemma_fundamental_div_mod_converse_auto()
    ensures 
        // forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) ==> q == (x / d) && r == #[trigger](x % d),
        forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) ==> q == #[trigger](x / d),
        forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) ==> r == #[trigger](x % d),
{
    assert forall |x: int, d: int, q: int, r: int|
        d != 0 && 0 <= r < d && x == #[trigger](q * d + r) implies q == #[trigger](x / d) by {
        lemma_fundamental_div_mod_converse(x, d, q, r);
    };
    assert forall |x: int, d: int, q: int, r: int|
        d != 0 && 0 <= r < d && x == #[trigger](q * d + r) implies r == #[trigger](x % d) by {
        lemma_fundamental_div_mod_converse(x, d, q, r);
    };
}

/// Proof that the remainder, when natural number `x` is divided by
/// positive integer `m`, is less than `m`.
pub proof fn lemma_mod_pos_bound(x: int, m: int)
    requires 
        0 <= x,
        0 < m,
    ensures  0 <= x % m < m
    decreases x
{
    lemma_mod_auto(m);
}

/// Proof that the remainder, when any natural number `x` is divided by
/// any positive integer `m`, is less than `m`.
pub proof fn lemma_mod_pos_bound_auto()
    ensures forall |x: int, m: int| 0 <= x && 0 < m ==> 0 <= #[trigger](x % m) < m,
{
    assert forall |x: int, m: int| 0 <= x && 0 < m implies 0 <= #[trigger](x % m) < m by
    {
        lemma_mod_pos_bound(x, m);
    }
}

/// Proof that the remainder when `x * y` is divided by `m` is
/// equivalent to the remainder when `(x % m) * y` is divided by `m`
pub proof fn lemma_mul_mod_noop_left(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m) * y % m == x * y % m
{
    lemma_mod_auto(m);
    lemma_mul_induction_auto(y, |u: int| (x % m) * u % m == x * u % m);
}

/// Proof that for any `x`, `y`, and `m`, the remainder when `x * y`
/// is divided by `m` is equivalent to the remainder when `(x % m) *
/// y` is divided by `m`
pub proof fn lemma_mul_mod_noop_left_auto()
    ensures forall |x: int, y: int, m: int| 0 < m ==> (x % m) * y % m == #[trigger](x * y % m),
{
    assert forall |x: int, y: int, m: int| 0 < m implies (x % m) * y % m == #[trigger](x * y % m) by
    {
        lemma_mul_mod_noop_left(x, y, m);
    }
}

/// Proof that the remainder when `x * y` is divided by `m` is
/// equivalent to the remainder when `x * (y % m)` is divided by `m`.
pub proof fn lemma_mul_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures x * (y % m) % m == (x * y) % m
{
    lemma_mod_auto(m);
    lemma_mul_induction_auto(x, |u: int| u * (y % m) % m == (u * y) % m);
}

/// Proof that for all `x`, `y`, and `m`, the remainder when `x * y`
/// is divided by `m` is equivalent to the remainder when `x * (y % m)`
/// is divided by `m`.
pub proof fn lemma_mul_mod_noop_right_auto()
    ensures forall |x: int, y: int, m: int| 0 < m ==> x * (y % m) % m == #[trigger]((x * y) % m),
{
    assert forall |x: int, y: int, m: int| 0 < m implies x * (y % m) % m == #[trigger]((x * y) % m) by
    {
        lemma_mul_mod_noop_right(x, y, m);
    }
}

/// Proof of various properties about modulo equivalence with respect
/// to multiplication, specifically various expressions that `(x * y)
/// % m` is equivalent to.
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

/// Proof of various properties about modulo equivalence with respect to multiplication
pub proof fn lemma_mul_mod_noop_general_auto()
    ensures forall |x: int, y: int, m: int| 0 < m ==> (((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m == #[trigger]((x * y) % m)),
{
    assert forall |x: int, y: int, m: int| 0 < m implies (((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m == #[trigger]((x * y) % m)) by
    {
        lemma_mul_mod_noop_general(x, y, m);
    }
}

/// Proof that modulo distributes over multiplication, provided you do
/// an extra modulo operation after multiplying the remainders. Specifically,
/// `(x % m) * (y % m) % m == (x * y) % m`.
pub proof fn lemma_mul_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m) * (y % m) % m == (x * y) % m
{
    lemma_mul_mod_noop_general(x, y, m);
}

/// Proof that modulo distributes over multiplication, provided you do
/// an extra modulo operation after multiplying the remainders
pub proof fn lemma_mul_mod_noop_auto()
    ensures forall |x: int, y: int, m: int| 0 < m ==> ((x % m) * (y % m) % m == #[trigger]((x * y) % m)),
{
    assert forall |x: int, y: int, m: int| 0 < m implies ((x % m) * (y % m) % m == #[trigger]((x * y) % m)) by
    {
        lemma_mul_mod_noop(x, y, m);
    }
}

/// Proof that `x` and `y` are congruent modulo `m` if and only if `x
/// - y` is congruent to 0 modulo `m`. In other words, `x % m == y % m
/// <==> (x - y) % m == 0`.
pub proof fn lemma_mod_equivalence(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m == y % m <==> (x - y) % m == 0
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
    ensures forall |x: int, y: int, m: int| #![trigger (x - y) % m] 0 < m ==> (x % m == y % m <==> (x - y) % m == 0),
{
    assert forall |x: int, y: int, m: int| #![trigger (x - y) % m] 0 < m implies ((x % m) == (y % m) <==> (x - y) % m == 0) by
    {
        lemma_mod_equivalence(x, y, m);
    }
}

/// This function says that `x` is congruent to `y` modulo `m` if and
/// only if their difference `x - y` is congruent to 0 modulo `m`.
pub open spec fn is_mod_equivalent(x: int, y: int, m: int) -> bool
    recommends
        m > 0
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
    ensures forall |x: int, y: int, z: int, m: int|  m > 0 && ( x % m == y % m <==> (x - y) % m == 0) ==> #[trigger]is_mod_equivalent(x * z, y * z, m),
{
    assert forall |x: int, y: int, z: int, m: int| m > 0 && is_mod_equivalent(x, y, m) implies #[trigger]is_mod_equivalent(x * z, y * z, m) by
    {
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

/// Proof that multiplying the divisor by a positive number can't
/// decrease the remainder. That is, for any `x`, `d > 1`, and `k > 0`,
/// `x % d <= x % (d * k)`.
pub proof fn lemma_mod_ordering_auto()
    ensures forall |x: int, k: int, d: int| 1 < d && 0 < k ==> (x % d <= #[trigger](x % (d * k))),
{
    assert forall |x: int, k: int, d: int| 1 < d && 0 < k implies (x % d <= #[trigger](x % (d * k))) by
    {
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
    lemma_fundamental_div_mod_converse(x, a, b * (x / (a * b)) + x % (a * b) / a, (x % (a * b)) % a);
}

/// Proof that for any integer `x` and positive integers `a` and `b`,
/// the remainder when `x` is divided by `a * b`, taken modulo `a`,
/// is equivalent to `x` modulo `a`. In other words,
/// `(x % (a * b)) % a == x % a`.
pub proof fn lemma_mod_mod_auto()
    ensures
        forall |a: int, b: int| #![trigger a * b] 0 < a && 0 < b ==> 0 < a * b,
        forall |x: int, a: int, b: int| #![trigger (x % (a * b)) % a, x % a] 0 < a && 0 < b ==> (x % (a * b)) % a == x % a,
{
    assert forall |a: int, b: int| #![trigger a * b] 0 < a && 0 < b implies 0 < a * b by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall |x: int, a: int, b: int| #![trigger x % (a * b)]
        0 < a && 0 < b implies
        (x % (a * b)) % a == x % a by
    {
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

/// Proof of the validity of an expanded form of the modulus operation.
/// Specifically, `x % (y * z) == y * ((x / y) % z) + x % y`.
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
        forall |y: int, z: int| #![trigger y * z] 0 < y && 0 < z ==> y * z > 0,
        forall |x: int, y: int, z: int| #![trigger x % (y * z)]
            0 <= x && 0 < y && 0 < z ==> x % (y * z) == y * ((x / y) % z) + x % y,
{
    assert forall |y: int, z: int| #![trigger y * z] 0 < y && 0 < z implies y * z > 0 by
    {
        lemma_mul_strictly_positive_auto();
    }
    assert forall |x: int, y: int, z: int| #![trigger x % (y * z)]
        0 <= x && 0 < y && 0 < z implies
        x % (y * z) == y * ((x / y) % z) + x % y by
    {
        lemma_mod_breakdown(x, y, z);
    }
}

}
