//! This file contains proofs related to modulo. These are internal
//! functions used within the math standard library.
//!
//! It's based on the following file from the Dafny math standard library:
//! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/ModInternals.dfy`.
//! That file has the following copyright notice:
//! /*******************************************************************************
//! *  Original: Copyright (c) Microsoft Corporation
//! *  SPDX-License-Identifier: MIT
//! *
//! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
//! *  SPDX-License-Identifier: MIT
//! *******************************************************************************/
#[allow(unused_imports)]
use super::super::super::prelude::*;

verus! {

use super::super::super::arithmetic::internals::general_internals::*;
use super::super::super::arithmetic::mul::*;
#[cfg(verus_keep_ghost)]
use super::mul_internals::group_mul_properties_internal;
#[cfg(verus_keep_ghost)]
use super::super::super::arithmetic::internals::mul_internals_nonlinear;
#[cfg(verus_keep_ghost)]
use super::super::super::arithmetic::internals::mod_internals_nonlinear::{
    lemma_fundamental_div_mod,
    lemma_mod_range,
    lemma_small_mod,
};
#[cfg(verus_keep_ghost)]
use super::super::super::arithmetic::internals::div_internals_nonlinear;
#[cfg(verus_keep_ghost)]
use super::super::super::math::{add as add1, sub as sub1};

/// This function performs the modulus operation recursively.
#[verifier::opaque]
pub open spec fn mod_recursive(x: int, d: int) -> int
    recommends
        d > 0,
    decreases
            (if x < 0 {
                (d - x)
            } else {
                x
            }),
    when d > 0
{
    if x < 0 {
        mod_recursive(d + x, d)
    } else if x < d {
        x
    } else {
        mod_recursive(x - d, d)
    }
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in certain base cases, and proves correctness of
/// inductive steps both upward and downward from the base cases. This
/// lemma invokes induction to establish that the predicate holds for
/// all possible inputs.
///
/// `f`: The integer predicate
///
/// `n`: Upper bound on the base cases. Specifically, the caller
/// establishes `f(i)` for every value `i` satisfying `0 <= i < n`.
///
/// To prove inductive steps upward from the base cases, the caller
/// must establish that, for any `i >= 0`, `f(i) ==> f(add1(i, n))`.
/// `add1(i, n)` is just `i + n`, but written in a functional style
/// so that it can be used where functional triggers are required.
///
/// To prove inductive steps downward from the base cases, the caller
/// must establish that, for any `i < n`, `f(i) ==> f(sub1(i, n))`.
/// `sub1(i, n)` is just `i - n`, but written in a functional style
/// so that it can be used where functional triggers are required.
pub proof fn lemma_mod_induction_forall(n: int, f: spec_fn(int) -> bool)
    requires
        n > 0,
        forall|i: int| 0 <= i < n ==> #[trigger] f(i),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, n)),
        forall|i: int| i < n && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)),
    ensures
        forall|i| #[trigger] f(i),
{
    assert forall|i: int| #[trigger] f(i) by {
        lemma_induction_helper(n, f, i);
    };
}

/// This utility function helps prove a mathematical property of a
/// pair of integers by induction. The caller supplies a predicate
/// over a pair of integers, proves the predicate holds in certain
/// base cases, and proves correctness of inductive steps both upward
/// and downward from the base cases. This lemma invokes induction to
/// establish that the predicate holds for all possible inputs.
///
/// `f`: The integer predicate
///
/// `n`: Upper bound on the base cases. Specifically, the caller
/// establishes `f(i, j)` for every pair of values `i, j` satisfying
/// `0 <= i < n` and `0 <= j < n`.
///
/// To prove inductive steps from the base cases, the caller must
/// establish that:
///
/// 1) For any `i >= 0`, `f(i, j) ==> f(add1(i, n), j)`. `add1(i, n)`
/// is just `i + n`, but written in a functional style so that it can
/// be used where functional triggers are required.
///
/// 2) For any `j >= 0`, `f(i, j) ==> f(i, add1(j, n))`
///
/// 3) For any `i < n`, `f(i) ==> f(sub1(i, n))`. `sub1(i, n)` is just
/// `i - n`, but written in a functional style so that it can be used
/// where functional triggers are required.
///
/// 4) For any `j < n`, `f(j) ==> f(i, sub1(j, n))`.
pub proof fn lemma_mod_induction_forall2(n: int, f: spec_fn(int, int) -> bool)
    requires
        n > 0,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger] f(i, j),
        forall|i: int, j: int| i >= 0 && #[trigger] f(i, j) ==> #[trigger] f(add1(i, n), j),
        forall|i: int, j: int| j >= 0 && #[trigger] f(i, j) ==> #[trigger] f(i, add1(j, n)),
        forall|i: int, j: int| i < n && #[trigger] f(i, j) ==> #[trigger] f(sub1(i, n), j),
        forall|i: int, j: int| j < n && #[trigger] f(i, j) ==> #[trigger] f(i, sub1(j, n)),
    ensures
        forall|i: int, j: int| #[trigger] f(i, j),
{
    assert forall|x: int, y: int| #[trigger] f(x, y) by {
        assert forall|i: int| 0 <= i < n implies #[trigger] f(i, y) by {
            let fj = |j| f(i, j);
            lemma_mod_induction_forall(n, fj);
            assert(fj(y));
        };
        let fi = |i| f(i, y);
        lemma_mod_induction_forall(n, fi);
        assert(fi(x));
    };
}

/// Proof that when dividing, adding the denominator to the numerator
/// increases the result by 1. Specifically, for the given `n` and `x`,
/// `(x + n) / n == x / n + 1`.
#[verifier::spinoff_prover]
pub proof fn lemma_div_add_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        (x + n) / n == x / n + 1,
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x + n, n);
    let zp = (x + n) / n - x / n - 1;
    assert(0 == n * zp + ((x + n) % n) - (x % n)) by {
        broadcast use group_mul_properties_internal;

    };
    if (zp > 0) {
        lemma_mul_inequality(1, zp, n);
    }
    if (zp < 0) {
        lemma_mul_inequality(zp, -1, n);
    }
}

/// Proof that when dividing, subtracting the denominator from the numerator
/// decreases the result by 1. Specifically, for the given `n` and `x`,
/// `(x - n) / n == x / n - 1`.
pub proof fn lemma_div_sub_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        (x - n) / n == x / n - 1,
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x - n, n);
    let zm = (x - n) / n - x / n + 1;
    assert(0 == n * zm + ((x - n) % n) - (x % n)) by {
        broadcast use group_mul_properties_internal;

    }
    if (zm > 0) {
        lemma_mul_inequality(1, zm, n);
    }
    if (zm < 0) {
        lemma_mul_inequality(zm, -1, n);
    }
}

/// Proof that when dividing, adding the denominator to the numerator
/// doesn't change the remainder. Specifically, for the given `n` and
/// `x`, `(x + n) % n == x % n`.
#[verifier::spinoff_prover]
pub proof fn lemma_mod_add_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        (x + n) % n == x % n,
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x + n, n);
    let zp = (x + n) / n - x / n - 1;
    assert(n * zp == n * ((x + n) / n - x / n) - n) by {
        assert(n * (((x + n) / n - x / n) - 1) == n * ((x + n) / n - x / n) - n) by {
            broadcast use group_mul_is_commutative_and_distributive;

        };
    };
    assert(0 == n * zp + ((x + n) % n) - (x % n)) by {
        broadcast use group_mul_properties_internal;

    }
    if (zp > 0) {
        lemma_mul_inequality(1, zp, n);
    } else if (zp < 0) {
        lemma_mul_inequality(zp, -1, n);
    } else {
        broadcast use group_mul_properties_internal;

    }
}

/// Proof that when dividing, subtracting the denominator from the
/// numerator doesn't change the remainder. Specifically, for the
/// given `n` and `x`, `(x - n) % n == x % n`.
pub proof fn lemma_mod_sub_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        (x - n) % n == x % n,
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x - n, n);
    let zm = (x - n) / n - x / n + 1;
    broadcast use group_mul_is_distributive;  // OBSERVE

    assert(0 == n * zm + ((x - n) % n) - (x % n)) by {
        broadcast use group_mul_properties_internal;

    }
    if (zm > 0) {
        lemma_mul_inequality(1, zm, n);
    }
    if (zm < 0) {
        lemma_mul_inequality(zm, -1, n);
    }
}

/// Proof that for the given `n` and `x`, `x % n == x` if and only if
/// `0 <= x < n`.
pub proof fn lemma_mod_below_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        0 <= x < n <==> x % n == x,
{
    assert forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x by {
        if (0 <= x < n) {
            lemma_small_mod(x as nat, n as nat);
        }
        lemma_mod_range(x, n);
    }
}

/// Proof of basic properties of the division given the divisor `n`:
///
/// 1) Adding the denominator to the numerator increases the quotient
/// by 1 and doesn't change the remainder.
///
/// 2) Subtracting the denominator from the numerator decreases the
/// quotient by 1 and doesn't change the remainder.
///
/// 3) The numerator is the same as the result if and only if the
/// numerator is in the half-open range `[0, n)`.
pub proof fn lemma_mod_basics(n: int)
    requires
        n > 0,
    ensures
        forall|x: int| #[trigger] ((x + n) % n) == x % n,
        forall|x: int| #[trigger] ((x - n) % n) == x % n,
        forall|x: int| #[trigger] ((x + n) / n) == x / n + 1,
        forall|x: int| #[trigger] ((x - n) / n) == x / n - 1,
        forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x,
{
    assert forall|x: int| #[trigger] ((x + n) % n) == x % n by {
        lemma_mod_add_denominator(n, x);
    };
    assert forall|x: int| #[trigger] ((x - n) % n) == x % n by {
        lemma_mod_sub_denominator(n, x);
        assert((x - n) % n == x % n);
    };
    assert forall|x: int| #[trigger] ((x + n) / n) == x / n + 1 by {
        lemma_div_add_denominator(n, x);
    };
    assert forall|x: int| #[trigger] ((x - n) / n) == x / n - 1 by {
        lemma_div_sub_denominator(n, x);
    };
    assert forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x by {
        lemma_mod_below_denominator(n, x);
    };
}

/// Proof that if `x == q * r + n` and `0 <= r < n`, then `q == x / n`
/// and `r == x % n`. Essentially, this is the converse of the
/// fundamental theorem of division and modulo.
pub proof fn lemma_quotient_and_remainder(x: int, q: int, r: int, n: int)
    requires
        n > 0,
        0 <= r < n,
        x == q * n + r,
    ensures
        q == x / n,
        r == x % n,
    decreases
            (if q > 0 {
                q
            } else {
                -q
            }),
{
    lemma_mod_basics(n);
    if q > 0 {
        mul_internals_nonlinear::lemma_mul_is_distributive_add(n, q - 1, 1);
        broadcast use lemma_mul_is_commutative;

        assert(q * n + r == (q - 1) * n + n + r);
        lemma_quotient_and_remainder(x - n, q - 1, r, n);
    } else if q < 0 {
        lemma_mul_is_distributive_sub(n, q + 1, 1);
        broadcast use lemma_mul_is_commutative;

        assert(q * n + r == (q + 1) * n - n + r);
        lemma_quotient_and_remainder(x + n, q + 1, r, n);
    } else {
        div_internals_nonlinear::lemma_small_div();
        assert(r / n == 0);
    }
}

/// This function says that for any `x` and `y`, there are two
/// possibilities for the sum `x % n + y % n`: (1) It's in the range
/// `[0, n)` and it's equal to `(x + y) % n`. (2) It's in the range
/// `[n, n + n)` and it's equal to `(x + y) % n + n`.
pub open spec fn mod_auto_plus(n: int) -> bool
    recommends
        n > 0,
{
    forall|x: int, y: int|
        {
            let z = (x % n) + (y % n);
            ((0 <= z < n && #[trigger] ((x + y) % n) == z) || (n <= z < n + n && ((x + y) % n) == z
                - n))
        }
}

/// This function says that for any `x` and `y`, there are two
/// possibilities for the difference `x % n - y % n`: (1) It's in the
/// range `[0, n)` and it's equal to `(x - y) % n`. (2) It's in the
/// range `[-n, 0)` and it's equal to `(x + y) % n - n`.
pub open spec fn mod_auto_minus(n: int) -> bool
    recommends
        n > 0,
{
    forall|x: int, y: int|
        {
            let z = (x % n) - (y % n);
            ((0 <= z < n && #[trigger] ((x - y) % n) == z) || (-n <= z < 0 && ((x - y) % n) == z
                + n))
        }
}

/// This function states various useful properties about the modulo
/// operator when the divisor is `n`.
pub open spec fn mod_auto(n: int) -> bool
    recommends
        n > 0,
{
    &&& (n % n == 0 && (-n) % n == 0)
    &&& (forall|x: int| #[trigger] ((x % n) % n) == x % n)
    &&& (forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x)
    &&& mod_auto_plus(n)
    &&& mod_auto_minus(n)
}

/// Proof of `mod_auto(n)`, which states various useful properties
/// about the modulo operator when the divisor is the positive number
/// `n`
pub proof fn lemma_mod_auto(n: int)
    requires
        n > 0,
    ensures
        mod_auto(n),
{
    lemma_mod_basics(n);
    broadcast use group_mul_properties_internal;

    assert forall|x: int, y: int|
        {
            let z = (x % n) + (y % n);
            ((0 <= z < n && #[trigger] ((x + y) % n) == z) || (n <= z < n + n && ((x + y) % n) == z
                - n))
        } by {
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
        } else {
            lemma_quotient_and_remainder(x + y, xq + yq + 1, xr + yr - n, n);
        }
    }
    assert forall|x: int, y: int|
        {
            let z = (x % n) - (y % n);
            ((0 <= z < n && #[trigger] ((x - y) % n) == z) || (-n <= z < 0 && ((x - y) % n) == z
                + n))
        } by {
        let xq = x / n;
        let xr = x % n;
        lemma_fundamental_div_mod(x, n);
        assert(x == n * (x / n) + (x % n));
        let yq = y / n;
        let yr = y % n;
        lemma_fundamental_div_mod(y, n);
        assert(y == yq * n + yr);
        if xr - yr >= 0 {
            lemma_quotient_and_remainder(x - y, xq - yq, xr - yr, n);
        } else {  // xr - yr < 0
            lemma_quotient_and_remainder(x - y, xq - yq - 1, xr - yr + n, n);
        }
    }
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in certain base cases, and proves correctness of
/// inductive steps both upward and downward from the base cases. This
/// lemma invokes induction to establish that the predicate holds for
/// the given arbitrary input `x`.
///
/// `f`: The integer predicate
///
/// `n`: Upper bound on the base cases. Specifically, the caller
/// establishes `f(i)` for every value `i` satisfying `is_le(0, i) &&
/// i < n`.
///
/// `x`: The desired case established by this lemma. Its postcondition
/// thus includes `f(x)`.
///
/// To prove inductive steps upward from the base cases, the caller
/// must establish that, for any `i`, `is_le(0, i) && f(i) ==> f(i +
/// n)`. `is_le(0, i)` is just `0 <= i`, but written in a functional
/// style so that it can be used where functional triggers are
/// required.
///
/// To prove inductive steps downward from the base cases, the caller
/// must establish that, for any `i`, `is_le(i + 1, n) && f(i) ==> f(i
/// - n)`. `is_le(i + 1, n)` is just `i + 1 <= n`, but written in a
/// functional style so that it can be used where functional triggers
/// are required.
pub proof fn lemma_mod_induction_auto(n: int, x: int, f: spec_fn(int) -> bool)
    requires
        n > 0,
        mod_auto(n) ==> {
            &&& (forall|i: int| #[trigger] is_le(0, i) && i < n ==> f(i))
            &&& (forall|i: int| #[trigger] is_le(0, i) && f(i) ==> f(i + n))
            &&& (forall|i: int| #[trigger] is_le(i + 1, n) && f(i) ==> f(i - n))
        },
    ensures
        mod_auto(n),
        f(x),
{
    lemma_mod_auto(n);
    assert(forall|i: int| is_le(0, i) && #[trigger] f(i) ==> #[trigger] f(add1(i, n)));
    assert(forall|i: int| is_le(i + 1, n) && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)));
    assert forall|i: int| 0 <= i < n implies #[trigger] f(i) by {
        assert(forall|i: int| is_le(0, i) && i < n ==> f(i));
        assert(is_le(0, i) && i < n);
    };
    lemma_mod_induction_forall(n, f);
    assert(f(x));
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in certain base cases, and proves correctness of
/// inductive steps both upward and downward from the base cases. This
/// lemma invokes induction to establish that the predicate holds for
/// all integer values.
///
/// `f`: The integer predicate
///
/// `n`: Upper bound on the base cases. Specifically, the caller
/// establishes `f(i)` for every value `i` satisfying `is_le(0, i) &&
/// i < n`.
///
/// To prove inductive steps upward from the base cases, the caller
/// must establish that, for any `i`, `is_le(0, i) && f(i) ==> f(i +
/// n)`. `is_le(0, i)` is just `0 <= i`, but written in a functional
/// style so that it can be used where functional triggers are
/// required.
///
/// To prove inductive steps downward from the base cases, the caller
/// must establish that, for any `i`, `is_le(i + 1, n) && f(i) ==> f(i
/// - n)`. `is_le(i + 1, n)` is just `i + 1 <= n`, but written in a
/// functional style so that it can be used where functional triggers
/// are required.
pub proof fn lemma_mod_induction_auto_forall(n: int, f: spec_fn(int) -> bool)
    requires
        n > 0,
        mod_auto(n) ==> {
            &&& (forall|i: int| #[trigger] is_le(0, i) && i < n ==> f(i))
            &&& (forall|i: int| #[trigger] is_le(0, i) && f(i) ==> f(i + n))
            &&& (forall|i: int| #[trigger] is_le(i + 1, n) && f(i) ==> f(i - n))
        },
    ensures
        mod_auto(n),
        forall|i| #[trigger] f(i),
{
    assert(mod_auto(n)) by {
        lemma_mod_induction_auto(n, 0, f);
    }
    assert forall|i| #[trigger] f(i) by {
        lemma_mod_induction_auto(n, i, f);
    }
}

} // verus!
