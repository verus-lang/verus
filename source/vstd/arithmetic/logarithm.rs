//! This file contains proofs related to integer logarithms. These are
//! part of the math standard library.
//!
//! It's based on the following file from the Dafny math standard
//! library:
//! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Logarithm.dfy`.
//! That file has the following copyright notice:
//! /*******************************************************************************
//! * Original: Copyright (c) Microsoft Corporation *
//! SPDX-License-Identifier: MIT * * Modifications and Extensions:
//! Copyright by the contributors to the Dafny Project *
//! SPDX-License-Identifier: MIT
//! *******************************************************************************/
#[allow(unused_imports)]
use super::super::prelude::*;

verus! {

use super::super::calc_macro::*;
#[cfg(verus_keep_ghost)]
use super::div_mod::{
    lemma_div_pos_is_pos,
    lemma_div_decreases,
    lemma_div_is_ordered,
    lemma_div_multiples_vanish,
};
#[cfg(verus_keep_ghost)]
use super::super::math::{div as div1};
#[cfg(verus_keep_ghost)]
use super::super::arithmetic::mul::{lemma_mul_increases, lemma_mul_is_commutative};
#[cfg(verus_keep_ghost)]
use super::super::arithmetic::power::{pow, lemma_pow_positive};

/// This function recursively defines the integer logarithm. It's only
/// meaningful when the base of the logarithm `base` is greater than 1,
/// and when the value whose logarithm is taken, `pow`, is non-negative.
#[verifier::opaque]
pub open spec fn log(base: int, pow: int) -> int
    recommends
        base > 1,
        pow >= 0,
    decreases pow,
{
    // In Dafny, we can invoke lemmas in functions to establish
    // termination. Here in Verus, instead, we add the second
    // conditions `pow / base >= pow` and `pow / base < 0` to show
    // termination.
    if pow < base || pow / base >= pow || pow / base < 0 {
        0
    } else {
        1 + log(base, pow / base)
    }
}

/// Proof that since `pow` is less than `base`, its logarithm in that base is 0
pub proof fn lemma_log0(base: int, pow: int)
    requires
        base > 1,
        0 <= pow < base,
    ensures
        log(base, pow) == 0,
{
    reveal(log);
}

/// Proof that since `pow` is greater than or equal to `base`, its
/// logarithm in that base is 1 more than the logarithm of `pow /
/// base`
pub broadcast proof fn lemma_log_s(base: int, pow: int)
    requires
        base > 1,
        pow >= base,
    ensures
        #![trigger log(base, div1(pow, base))]
        pow / base >= 0,
        log(base, pow) == 1 + log(base, pow / base),
{
    broadcast use lemma_div_pos_is_pos, lemma_div_decreases;

    reveal(log);
}

/// Proof that the integer logarithm is always nonnegative. Specifically,
/// `log(base, pow) >= 0`.
pub proof fn lemma_log_nonnegative(base: int, pow: int)
    requires
        base > 1,
        0 <= pow,
    ensures
        log(base, pow) >= 0,
    decreases pow,
{
    reveal(log);
    if !(pow < base || pow / base >= pow || pow / base < 0) {
        lemma_log_nonnegative(base, pow / base);
    }
}

/// Proof that since `pow1` is less than or equal to `pow2`, the
/// integer logarithm of `pow1` in base `base` is less than or equal
/// to that of `pow2`.
pub proof fn lemma_log_is_ordered(base: int, pow1: int, pow2: int)
    requires
        base > 1,
        0 <= pow1 <= pow2,
    ensures
        log(base, pow1) <= log(base, pow2),
    decreases pow1,
{
    reveal(log);
    if pow2 < base {
        assert(log(base, pow1) == 0 == log(base, pow2));
    } else if pow1 < base {
        assert(log(base, pow1) == 0);
        lemma_log_nonnegative(base, pow2);
    } else {
        broadcast use lemma_div_pos_is_pos, lemma_div_is_ordered, lemma_div_decreases;

        lemma_log_is_ordered(base, pow1 / base, pow2 / base);
    }
}

/// Proof that the integer logarithm of `pow(base, n)` in base `base` is `n`
pub proof fn lemma_log_pow(base: int, n: nat)
    requires
        base > 1,
    ensures
        log(base, pow(base, n)) == n,
    decreases n,
{
    if n == 0 {
        reveal(pow);
        reveal(log);
    } else {
        let n_minus_1: nat = (n - 1) as nat;
        lemma_pow_positive(base, n);
        calc! {
            (==)
            log(base, pow(base, n)); (==) {
                reveal(pow);
            }
            log(base, base * pow(base, n_minus_1)); (==) {
                lemma_pow_positive(base, n_minus_1);
                lemma_mul_increases(pow(base, n_minus_1), base);
                lemma_mul_is_commutative(pow(base, n_minus_1), base);
                lemma_log_s(base, base * pow(base, n_minus_1));
            }
            1 + log(base, (base * pow(base, n_minus_1)) / base); (==) {
                lemma_div_multiples_vanish(pow(base, n_minus_1), base);
            }
            1 + log(base, pow(base, n_minus_1)); (==) {
                lemma_log_pow(base, n_minus_1);
            }
            1 + (n - 1);
        }
    }
}

} // verus!
