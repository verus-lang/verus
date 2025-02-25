//! This file contains proofs related to division. These are internal
//! functions used within the math standard library.
//!
//! It's based on the following file from the Dafny math standard library:
//! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/DivInternals.dfy`.
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

#[cfg(verus_keep_ghost)]
use super::super::super::arithmetic::internals::general_internals::is_le;
#[cfg(verus_keep_ghost)]
use super::super::super::arithmetic::internals::mod_internals::{
    lemma_mod_induction_forall,
    lemma_mod_induction_forall2,
    mod_auto,
    lemma_mod_auto,
    lemma_mod_basics,
};
use super::super::super::arithmetic::internals::mod_internals_nonlinear;
#[cfg(verus_keep_ghost)]
#[cfg(verus_keep_ghost)]
use super::super::super::arithmetic::internals::div_internals_nonlinear;
#[cfg(verus_keep_ghost)]
use super::super::super::math::{add as add1, sub as sub1};

/// This function recursively computes the quotient resulting from
/// dividing two numbers `x` and `d`, in the case where `d > 0`
#[verifier::opaque]
pub open spec fn div_pos(x: int, d: int) -> int
    recommends
        d > 0,
    decreases
            (if x < 0 {
                d - x
            } else {
                x
            }),
    when d > 0
{
    if x < 0 {
        -1 + div_pos(x + d, d)
    } else if x < d {
        0
    } else {
        1 + div_pos(x - d, d)
    }
}

/// This function recursively computes the quotient resulting from
/// dividing two numbers `x` and `d`. It's only meaningful when `d !=
/// 0`, of course.
#[verifier::opaque]
pub open spec fn div_recursive(x: int, d: int) -> int
    recommends
        d != 0,
{
    // reveal(div_pos);
    if d > 0 {
        div_pos(x, d)
    } else {
        -1 * div_pos(x, -1 * d)
    }
}

/// Proof of basic properties of integer division when the divisor is
/// the given positive integer `n`
pub proof fn lemma_div_basics(n: int)
    requires
        n > 0,
    ensures
        (n / n) == 1 && -((-n) / n) == 1,
        forall|x: int| 0 <= x < n <==> #[trigger] (x / n) == 0,
        forall|x: int| #[trigger] ((x + n) / n) == x / n + 1,
        forall|x: int| #[trigger] ((x - n) / n) == x / n - 1,
{
    lemma_mod_auto(n);
    lemma_mod_basics(n);
    div_internals_nonlinear::lemma_small_div();
    div_internals_nonlinear::lemma_div_by_self(n);
    assert forall|x: int| 0 <= x < n <== #[trigger] (x / n) == 0 by {
        mod_internals_nonlinear::lemma_fundamental_div_mod(x, n);
    }
}

/// This function says that for any `x` and `y`, there are two
/// possibilities for the sum `x % n + y % n`: (1) It's in the range
/// `[0, n)` and `(x + y) / n == x / n + y / n`. (2) It's in the range
/// `[n, n + n)` and `(x + y) / n = x / n + y / n + 1`.
pub open spec fn div_auto_plus(n: int) -> bool {
    forall|x: int, y: int|
        #![trigger ((x + y) / n)]
        {
            let z = (x % n) + (y % n);
            ((0 <= z < n && ((x + y) / n) == x / n + y / n) || (n <= z < n + n && ((x + y) / n) == x
                / n + y / n + 1))
        }
}

/// This function says that for any `x` and `y`, there are two
/// possibilities for the difference `x % n - y % n`: (1) It's in the
/// range `[0, n)` and `(x - y) / n == x / n - y / n`. (2) It's in the
/// range `[-n, 0)` and `(x - y) / n = x / n - y / n - 1`.
pub open spec fn div_auto_minus(n: int) -> bool {
    forall|x: int, y: int|
        #![trigger ((x - y) / n)]
        {
            let z = (x % n) - (y % n);
            ((0 <= z < n && ((x - y) / n) == x / n - y / n) || (-n <= z < 0 && ((x - y) / n) == x
                / n - y / n - 1))
        }
}

/// This function states various properties of integer division when
/// the denominator is `n`, including the identity property, a fact
/// about when quotients are zero, and facts about adding and
/// subtracting integers over this common denominator
pub open spec fn div_auto(n: int) -> bool
    recommends
        n > 0,
{
    &&& mod_auto(n)
    &&& (n / n == -((-n) / n) == 1)
    &&& forall|x: int| 0 <= x < n <==> #[trigger] (x / n) == 0
    &&& div_auto_plus(n)
    &&& div_auto_minus(n)
}

/// Proof of `div_auto_plus(n)`, not exported publicly because it's
/// just used as part of [`lemma_div_auto`] to prove `div_auto(n)`
proof fn lemma_div_auto_plus(n: int)
    requires
        n > 0,
    ensures
        div_auto_plus(n),
{
    lemma_mod_auto(n);
    lemma_div_basics(n);
    assert forall|x: int, y: int|
        {
            let z = (x % n) + (y % n);
            ((0 <= z < n && #[trigger] ((x + y) / n) == x / n + y / n) || (n <= z < n + n && ((x
                + y) / n) == x / n + y / n + 1))
        } by {
        let f = |xx: int, yy: int|
            {
                let z = (xx % n) + (yy % n);
                ((0 <= z < n && ((xx + yy) / n) == xx / n + yy / n) || (n <= z < 2 * n && ((xx + yy)
                    / n) == xx / n + yy / n + 1))
            };
        assert forall|i: int, j: int|
            {
                // changing this from j + n to mod's addition speeds up the verification
                // otherwise you need higher rlimit
                // might be a good case for profilers
                &&& (j >= 0 && #[trigger] f(i, j) ==> f(i, add1(j, n)))
                &&& (i < n && f(i, j) ==> f(i - n, j))
                &&& (j < n && f(i, j) ==> f(i, j - n))
                &&& (i >= 0 && f(i, j) ==> f(i + n, j))
            } by {
            assert(((i + n) + j) / n == ((i + j) + n) / n);
            assert((i + (j + n)) / n == ((i + j) + n) / n);
            assert(((i - n) + j) / n == ((i + j) - n) / n);
            assert((i + (j - n)) / n == ((i + j) - n) / n);
        }
        assert forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger] f(i, j) by {
            assert(((i + n) + j) / n == ((i + j) + n) / n);
            assert((i + (j + n)) / n == ((i + j) + n) / n);
            assert(((i - n) + j) / n == ((i + j) - n) / n);
            assert((i + (j - n)) / n == ((i + j) - n) / n);
        }
        lemma_mod_induction_forall2(n, f);
        assert(f(x, y));
    }
}

/// Proof of `div_auto_mius(n)`, not exported publicly because it's
/// just used as part of [`lemma_div_auto`] to prove `div_auto(n)`
#[verifier::spinoff_prover]
proof fn lemma_div_auto_minus(n: int)
    requires
        n > 0,
    ensures
        div_auto_minus(n),
{
    lemma_mod_auto(n);
    lemma_div_basics(n);
    assert forall|x: int, y: int|
        {
            let z = (x % n) - (y % n);
            ((0 <= z < n && #[trigger] ((x - y) / n) == x / n - y / n) || (-n <= z < 0 && ((x - y)
                / n) == x / n - y / n - 1))
        } by {
        let f = |xx: int, yy: int|
            {
                let z = (xx % n) - (yy % n);
                ((0 <= z < n && ((xx - yy) / n) == xx / n - yy / n) || (-n <= z < 0 && (xx - yy) / n
                    == xx / n - yy / n - 1))
            };
        assert forall|i: int, j: int|
            {
                &&& (j >= 0 && #[trigger] f(i, j) ==> f(i, add1(j, n)))
                &&& (i < n && f(i, j) ==> f(sub1(i, n), j))
                &&& (j < n && f(i, j) ==> f(i, sub1(j, n)))
                &&& (i >= 0 && f(i, j) ==> f(add1(i, n), j))
            } by {
            assert(((i + n) - j) / n == ((i - j) + n) / n);
            assert((i - (j - n)) / n == ((i - j) + n) / n);
            assert(((i - n) - j) / n == ((i - j) - n) / n);
            assert((i - (j + n)) / n == ((i - j) - n) / n);
        }
        assert forall|i: int, j: int| 0 <= i < n && 0 <= j < n implies #[trigger] f(i, j) by {
            assert(((i + n) - j) / n == ((i - j) + n) / n);
            assert((i - (j - n)) / n == ((i - j) + n) / n);
            assert(((i - n) - j) / n == ((i - j) - n) / n);
            assert((i - (j + n)) / n == ((i - j) - n) / n);
        }
        lemma_mod_induction_forall2(n, f);
        assert(f(x, y));
    }
}

/// Proof of `div_auto(n)`, which expresses many useful properties of
/// division when the denominator is the given positive integer `n`.
pub proof fn lemma_div_auto(n: int)
    requires
        n > 0,
    ensures
        div_auto(n),
{
    lemma_mod_auto(n);
    lemma_div_basics(n);
    assert forall|x: int| 0 <= x < n <==> #[trigger] (x / n) == 0 by {
        lemma_div_basics(n);
    }
    assert((0 + n) / n == 1);
    assert((0 - n) / n == -1);
    lemma_div_auto_plus(n);
    lemma_div_auto_minus(n);
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
pub proof fn lemma_div_induction_auto(n: int, x: int, f: spec_fn(int) -> bool)
    requires
        n > 0,
        div_auto(n) ==> {
            &&& (forall|i: int| #[trigger] is_le(0, i) && i < n ==> f(i))
            &&& (forall|i: int| #[trigger] is_le(0, i) && f(i) ==> f(i + n))
            &&& (forall|i: int| #[trigger] is_le(i + 1, n) && f(i) ==> f(i - n))
        },
    ensures
        div_auto(n),
        f(x),
{
    lemma_div_auto(n);
    assert(forall|i: int| is_le(0, i) && i < n ==> f(i));
    assert(forall|i: int| is_le(0, i) && #[trigger] f(i) ==> #[trigger] f(add1(i, n)));
    assert(forall|i: int| is_le(i + 1, n) && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)));
    assert forall|i: int| 0 <= i < n implies #[trigger] f(i) by {
        assert(f(i)) by {
            assert(forall|i: int| is_le(0, i) && i < n ==> f(i));
            assert(is_le(0, i) && i < n);
        };
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
pub proof fn lemma_div_induction_auto_forall(n: int, f: spec_fn(int) -> bool)
    requires
        n > 0,
        div_auto(n) ==> {
            &&& (forall|i: int| #[trigger] is_le(0, i) && i < n ==> f(i))
            &&& (forall|i: int| #[trigger] is_le(0, i) && f(i) ==> f(i + n))
            &&& (forall|i: int| #[trigger] is_le(i + 1, n) && f(i) ==> f(i - n))
        },
    ensures
        div_auto(n),
        forall|i| #[trigger] f(i),
{
    assert(div_auto(n)) by {
        lemma_div_induction_auto(n, 0, f);
    }
    assert forall|i| #[trigger] f(i) by {
        lemma_div_induction_auto(n, i, f);
    }
}

} // verus!
