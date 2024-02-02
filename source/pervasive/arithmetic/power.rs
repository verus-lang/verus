//! This file contains proofs related to exponentiation. These are
//! part of the math standard library.
//!
//! It's based on the following file from the Dafny math standard library:
//! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Power.dfy`.
//! That file has the following copyright notice:
//! /*******************************************************************************
//! *  Original: Copyright (c) Microsoft Corporation
//! *  SPDX-License-Identifier: MIT
//! *  
//! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
//! *  SPDX-License-Identifier: MIT 
//! *******************************************************************************/

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::calc_macro::*;

verus! {

use crate::arithmetic::div_mod::*;
use crate::arithmetic::internals::general_internals::{is_le};
use crate::arithmetic::mul::{lemma_mul_inequality, lemma_mul_nonnegative_auto, lemma_mul_strictly_increases, lemma_mul_left_inequality, lemma_mul_basics_auto, lemma_mul_increases_auto, lemma_mul_strictly_increases_auto, lemma_mul_is_commutative_auto, lemma_mul_is_distributive_auto, lemma_mul_is_associative_auto, lemma_mul_nonnegative};
use crate::arithmetic::internals::mul_internals::{lemma_mul_auto, lemma_mul_induction_auto};
use crate::arithmetic::math::{sub as sub1};

/// This function performs exponentiation recursively, to compute `b`
/// to the power of a natural number `e`
pub open spec fn pow(b: int, e: nat) -> int
    decreases e
{
    if e == 0 {
        1
    } else {
        b * pow(b, (e - 1) as nat)
    }
}

/// Proof that the given integer `b` to the power of 0 is 1
pub proof fn lemma_pow0(b: int)
    ensures pow(b, 0) == 1
{
    reveal(pow);
}

/// Proof that any integer to the power of 0 is 1
pub proof fn lemma_pow0_auto()
    ensures forall |b: int| #[trigger]pow(b, 0 as nat) == 1
{
    reveal(pow);
}

/// Proof that the given integer `b` to the power of 1 is `b`
pub proof fn lemma_pow1(b: int)
    ensures pow(b, 1) == b
{
    calc! { (==)
        pow(b, 1);
        { reveal(pow); }
        b * pow(b, 0);
        { lemma_pow0(b); }
        b * 1;
        { lemma_mul_basics_auto(); }
        b;
    }
}

/// Proof that any integer to the power of 1 is itself
pub proof fn lemma_pow1_auto()
    ensures 
        forall |b: int| #[trigger]pow(b, 1) == b,
{
    reveal(pow);
    assert forall |b: int| #[trigger]pow(b, 1) == b by
    {
        lemma_pow1(b);
    };
}

/// Proof that 0 to the power of the given positive integer `e` is 0
pub proof fn lemma0_pow(e: nat)
    requires e > 0
    ensures pow(0, e) == 0
    decreases e
{
    reveal(pow);
    lemma_mul_basics_auto();
    if e != 1 {
        lemma0_pow((e - 1) as nat);
    }
}

/// Proof that 0 to the power of any positive integer is 0
pub proof fn lemma0_pow_auto()
    ensures forall |e: nat| e > 0 ==> #[trigger]pow(0, e) == 0
{
    reveal(pow);
    assert forall |e: nat| e > 0 implies #[trigger]pow(0, e) == 0 by
    {
        lemma0_pow(e);
    }
}

/// Proof that 1 to the power of the given natural number `e` is 1
pub proof fn lemma1_pow(e: nat)
    ensures pow(1, e) == 1
    decreases e
{
    reveal(pow);
    lemma_mul_basics_auto();
    if e != 0 {
        lemma1_pow((e - 1) as nat);
    }
}

/// Proof that 1 to the power of any natural number is 1
pub proof fn lemma1_pow_auto()
    ensures forall |e: nat| e > 0 ==> #[trigger]pow(1, e) == 1
{
    reveal(pow);
    assert forall |e: nat| e > 0 implies
        #[trigger]pow(1, e) == 1 by
    {
        lemma1_pow(e);
    }
}

/// Proof that taking the given number `x` to the power of 2 produces `x * x`
pub proof fn lemma_square_is_pow2(x: int)
ensures pow(x, 2) == x * x
{
    // the original dafny is just a reveal clause
    // maybe I can do it with reveal_with_fuel? but I don't know how
    // the following doesn't work
    // assert(pow(x, 2) == x * x) by { 
        // reveal_with_fuel(pow, 2);
    //  };
    reveal(pow);
    assert(x as int * pow(x as int, 1) == x * (x as int * pow(x as int, 0)));
}

/// Proof that taking any positive integer to the power of 2 is
/// equivalent to multiplying that integer by itself
pub proof fn lemma_square_is_pow2_auto()
    ensures forall |x: int| x > 0 ==> #[trigger]pow(x, 2) == x * x,
{
    reveal(pow);
    assert forall |x: int| x > 0 implies
        #[trigger]pow(x, 2) == x * x by
    {
        lemma_square_is_pow2(x);
    }
}

/// Proof that taking the given positive integer `b` to the power of
/// the given natural number `n` produces a positive result
pub proof fn lemma_pow_positive(b: int, e: nat)
    requires b > 0
    ensures 0 < pow(b, e)
{
    // dafny does not need to reveal
    reveal(pow);
    lemma_mul_increases_auto();
    lemma_pow0_auto();
    
    lemma_mul_induction_auto(e as int, |u: int| 0 <= u ==> 0 < pow(b, u as nat));
}

/// Proof that taking any positive integer to any natural number power
/// produces a positive result
pub proof fn lemma_pow_positive_auto()
    ensures 
        forall |b: int, e: nat| b > 0 ==> 0 < #[trigger] pow(b, e)
{
    reveal(pow);
    assert forall |b: int, e: nat| b > 0 implies 0 < #[trigger] pow(b, e) by
    {
        lemma_pow_positive(b, e);
    }
}

/// Proof that taking an integer `b` to the power of the sum of two
/// natural numbers `e1` and `e2` is equivalent to multiplying `b` to
/// the power of `e1` by `b` to the power of `e2`
pub proof fn lemma_pow_adds(b: int, e1: nat, e2: nat)
    ensures pow(b, e1 + e2) == pow(b, e1) * pow(b, e2),
    decreases e1
{
    if e1 == 0 {
    calc! { (==)
        pow(b, e1) * pow(b, e2);
        { lemma_pow0(b); }
        1 * pow(b, e2);
        { lemma_mul_basics_auto(); }
        pow(b, 0 + e2);
    }
    }
    else {
    calc! { (==)
        pow(b, e1) * pow(b, e2);
        { reveal(pow); }
        (b * pow(b, (e1 - 1) as nat)) * pow(b, e2);
        { lemma_mul_is_associative_auto(); }
        b * (pow(b, (e1 - 1) as nat) * pow(b, e2));
        { lemma_pow_adds(b, (e1 - 1) as nat, e2); }
        b * pow(b, (e1 - 1 + e2) as nat);
        { reveal(pow); }
        pow(b, e1 + e2);
    }
    }
}

/// Proof that taking an integer to the power of the sum of two
/// natural numbers is equivalent to taking it to the power of each of
/// those numbers and multiplying the results
pub proof fn lemma_pow_adds_auto()
    ensures forall |x: int, y: nat, z: nat| #[trigger] pow(x, y + z) == pow(x, y) * pow(x, z),
{
    assert forall |x: int, y: nat, z: nat| #[trigger] pow(x, y + z) == pow(x, y) * pow(x, z) by
    {
    lemma_pow_adds(x, y, z);
    }
}

/// Proof that if `e1 >= e2`, then `b` to the power of `e1` is equal
/// to the product of `b` to the power of `e1 - e2` and `b` to the
/// power of `e2`
pub proof fn lemma_pow_sub_add_cancel(b: int, e1: nat, e2: nat)
    requires e1 >= e2
    ensures pow(b, (e1 - e2) as nat) * pow(b, e2) == pow(b, e1)
    decreases e1
{
    lemma_pow_adds(b, (e1 - e2) as nat, e2);
}

/// Proof that, for any `x`, `y`, and `z` such that `y >= z`, we know
/// `x` to the power of `y` is equal to the product of `x` to the
/// power of `y - z` and `x` to the power of `z`
pub proof fn lemma_pow_sub_add_cancel_auto()
    ensures forall |x: int, y: nat, z: nat| y >= z ==> #[trigger]pow(x, (y - z) as nat) * pow(x, z) == pow(x, y),

{
    assert forall |x: int, y: nat, z: nat| y >= z implies #[trigger]pow(x, (y - z) as nat) * pow(x, z) == pow(x, y) by 
    {
        lemma_pow_sub_add_cancel(x, y, z);
    }
}

/// Proof that, as long as `e1 <= e2`, taking a positive integer `b`
/// to the power of `e2 - e1` is equivalent to dividing `b` to the
/// power of `e2` by `b` to the power of `e1`.
pub proof fn lemma_pow_subtracts(b: int, e1: nat, e2: nat)
    requires 
        b > 0,
        e1 <= e2
    ensures 
        pow(b, e1) > 0,
        pow(b , (e2 - e1) as nat) == pow(b , e2) / pow(b , e1) > 0
{
    lemma_pow_positive_auto();
    calc! {
        (==)
        pow(b, e2) / pow(b , e1);
        { lemma_pow_sub_add_cancel(b , e2, e1); }
        pow(b , (e2 - e1) as nat) * pow(b , e1) / pow(b , e1);
        { lemma_div_by_multiple(pow(b , (e2 - e1) as nat), pow(b , e1)); }
        pow(b , (e2 - e1) as nat);
    }
}

/// Proof that, for all `b`, `e1`, and `e2`, as long as `b` is
/// positive and `e1 <= e2`, taking `b` to the power of `e2 - e1` is
/// equivalent to dividing `b` to the power of `e2` by `b` to the
/// power of `e1`.
pub proof fn lemma_pow_subtracts_auto()
ensures 
    forall |b: int, e1: nat| b > 0 ==> pow(b, e1) > 0,
    forall |b: int, e1: nat, e2: nat| b > 0 && e1 <= e2 ==> #[trigger]pow(b, (e2 - e1) as nat) == pow(b, e2) / pow(b, e1) > 0,
{
    reveal(pow);
    lemma_pow_positive_auto();
    assert forall |b: int, e1: nat, e2: nat| b > 0 && e1 <= e2 implies #[trigger]pow(b, (e2 - e1) as nat) == pow(b, e2) / pow(b, e1) > 0 by
    {
        lemma_pow_subtracts(b, e1, e2);
    }
}

/// Proof that `a` to the power of `b * c` is equal to the result of
/// taking `a` to the power of `b`, then taking that to the power of
/// `c`.
pub proof fn lemma_pow_multiplies(a: int, b: nat, c: nat)
    ensures 
        0 <= b * c,
        pow(pow(a, b), c) == pow(a, b * c)
    decreases c
{
    lemma_mul_nonnegative(b as int, c as int);
    if c == 0 {
        lemma_mul_basics_auto();
        calc! {
            (==)
            pow(a, (b * c) as nat);
            { lemma_pow0(a); }
            1;
            { lemma_pow0(pow(a, b)); }
            pow(pow(a, b), c);
        }
    }
    else {
        calc! { (==)
            b * c - b;
            { lemma_mul_basics_auto(); }
            b * c - b * 1;
            { lemma_mul_is_distributive_auto(); }
            b * (c - 1);
        }
        lemma_mul_nonnegative(b as int, c - 1);
        assert(0 <= b * c - b);

        calc! { (==)
            pow(a, b * c);
            { }
            pow(a, (b + b * c - b) as nat);
            { lemma_pow_adds(a, b, (b * c - b) as nat); }
            pow(a, b) * pow(a, (b * c - b) as nat);
            { }
            pow(a, b) * pow(a, (b * (c - 1)) as nat);
            { lemma_pow_multiplies(a, b, (c - 1) as nat); }
            pow(a, b) * pow(pow(a, b), (c - 1) as nat);
            { reveal(pow); }
            pow(pow(a, b), c);
        }
    }
}

/// Proof that, for any `a`, `b`, and `c`, `a` to the power of `b * c`
/// is equal to the result of taking `a` to the power of `b`, then
/// taking that to the power of `c`.
pub proof fn lemma_pow_multiplies_auto()
    ensures forall |b: nat, c: nat| 0 <= #[trigger](b * c),
            forall |a: int, b: nat, c: nat| #[trigger]pow(pow(a, b), c) == pow(a, b * c),
{
    assert forall |a: int, b: nat, c: nat| #[trigger]pow(pow(a, b), c) == pow(a, b * c) by
    {
        lemma_pow_multiplies(a, b, c);
    };
}

/// Proof that `a * b` to the power of `e` is equal to the product of
/// `a` to the power of `e` and `b` to the power of `e`
pub proof fn lemma_pow_distributes(a: int, b: int, e: nat)
    ensures 
        pow(a * b, e) == pow(a, e) * pow(b, e)
    decreases e
{
    reveal(pow);
    lemma_mul_basics_auto();
    if e >= 1 {
        calc! { (==)
            pow(a * b, e); { reveal(pow); }
            (a * b) * pow(a * b, (e - 1) as nat);
            { lemma_pow_distributes(a, b, (e - 1) as nat); }
            (a * b) * (pow(a, (e - 1) as nat) * pow(b, (e - 1) as nat));
            { lemma_mul_is_associative_auto(); 
            lemma_mul_is_commutative_auto(); 
            assert ((a * b * pow(a, (e - 1) as nat)) * pow(b, (e - 1) as nat) 
                == (a * pow(a, (e - 1) as nat) * b) * pow(b, (e - 1) as nat)); 
            }
            (a * pow(a, (e - 1) as nat)) * (b * pow(b, (e - 1) as nat)); { reveal(pow);}
            pow(a, e) * pow(b, e);
        }
    }
}

/// Proof that, for any `x`, `y`, and `z`, `x * y` to the power of `z`
/// is equal to the product of `x` to the power of `z` and `y` to the
/// power of `z`
pub proof fn lemma_pow_distributes_auto()
    ensures forall |x: int, y: nat, z: nat| #[trigger]pow(x * y, z) == pow(x, z) * pow(y as int, z),
{
    // reveal pow();
    assert forall |x: int, y: nat, z: nat| #[trigger]pow(x * y, z) == pow(x, z) * pow(y as int, z) by
    {
    lemma_pow_distributes(x, y as int, z);
    }
}

/// Proof of various useful properties of `pow` (exponentiation)
pub proof fn lemma_pow_auto()
    ensures 
        forall |x: int| pow(x, 0) == 1,
        forall |x: int| #[trigger] pow(x, 1) == x,
        forall |x: int, y: int| y == 0 ==> #[trigger] pow(x, y as nat) == 1,
        forall |x: int, y: int| y == 1 ==> #[trigger]pow(x, y as nat) == x,
        forall |x: int, y: int| 0 < x && 0 < y ==> x <= #[trigger](x * y as nat),
        forall |x: int, y: int| 0 < x && 1 < y ==> x < #[trigger](x * y as nat),
        forall |x: int, y: nat, z: nat| #[trigger] pow(x, y + z) == pow(x, y) * pow(x, z),
        forall |x: int, y: nat, z: nat| y >= z ==> #[trigger]pow(x, (y - z) as nat) * pow(x, z) == pow(x, y),
        forall |x: int, y: nat, z: nat| #[trigger]pow(x * y, z) == pow(x, z) * pow(y as int, z),
{
    reveal(pow);

    lemma_pow0_auto();
    lemma_pow1_auto();

    lemma_pow_distributes_auto();
    lemma_pow_adds_auto();
    lemma_pow_sub_add_cancel_auto();

    lemma_mul_auto();
    lemma_mul_increases_auto();
    lemma_mul_strictly_increases_auto();
}

/// Proof that a number greater than 1 raised to a power strictly
/// increases as the power strictly increases. Specifically, given
/// that `b > 1` and `e1 < e2`, we can conclude that `pow(b, e1) <
/// pow(b, e2)`.
pub proof fn lemma_pow_strictly_increases(b: nat, e1: nat, e2: nat)
    requires 
        1 < b,
        e1 < e2,
    ensures 
        pow(b as int, e1) < pow(b as int, e2)
{
    let f = |e: int| 0 < e ==> pow(b as int, e1) < pow(b as int, (e1 + e) as nat);
    assert forall |i: int| (#[trigger]is_le(0, i) && f(i)) implies f(i + 1) by
    {
    calc! {(<=)    
        pow(b as int, (e1 + i) as nat);
        (<=) { 
            lemma_pow_positive(b as int, (e1 + i) as nat);
            lemma_mul_left_inequality(pow(b as int, (e1 + i) as nat), 1, b as int); 
        }
        pow(b as int, (e1 + i) as nat) * b;
        (<=) { lemma_pow1(b as int); }
        pow(b as int, (e1 + i) as nat) * pow(b as int, 1);
        (<=)   { lemma_pow_adds(b as int, (e1 + i) as nat, 1nat); }
        pow(b as int, (e1 + i + 1) as nat);
    }
    assert(0 < i ==> pow(b as int, e1) < pow(b as int, (e1 + i) as nat));
    if (i == 0) {
        assert(pow(b as int, e1) < pow(b as int, (e1 + 1) as nat)) by {
            reveal(pow);
            assert(pow(b as int, e1) < b * pow(b as int, e1)) by {
                    // cannot be replaced to lemma_pow_auto()
                    assert(pow(b as int, e1) > 0) by { 
                        lemma_pow_positive_auto() 
                    };
                    lemma_mul_strictly_increases(b as int, pow(b as int, e1));
            };
        };
    }
    assert(f(i + 1));
    }
    lemma_mul_induction_auto(e2 - e1, f);
} 

/// Proof that any number greater than 1 raised to a power strictly
/// increases as the power strictly increases
pub proof fn lemma_pow_strictly_increases_auto()
    ensures forall |b: int, e1: nat, e2: nat| 1 < b && e1 < e2 ==> #[trigger]pow(b, e1) < #[trigger]pow(b, e2),
{
    reveal(pow);
    assert forall |b: int, e1: nat, e2: nat| 1 < b && e1 < e2 implies #[trigger]pow(b, e1) < #[trigger]pow(b, e2) by
    {
        lemma_pow_strictly_increases(b as nat, e1, e2);
    }
}

/// Proof that a positive number raised to a power increases as the
/// power increases. Specifically, since `e1 <= e2`, we know `pow(b,
/// e1) <= pow(b, e2)`.
pub proof fn lemma_pow_increases(b: nat, e1: nat, e2: nat)
    requires 
        b > 0,
        e1 <= e2,
    ensures 
        pow(b as int, e1) <= pow(b as int, e2)
{
    if e1 != e2 {
        if b > 1 {
            lemma_pow_strictly_increases(b, e1, e2);
        }
        else {
            lemma1_pow(e1);
            lemma1_pow(e2);
        }
    }
}

/// Proof that a positive number raised to a power increases as the
/// power increases
pub proof fn lemma_pow_increases_auto()
    ensures forall |b: int, e1: nat, e2: nat| b > 0 && e1 <= e2 ==> #[trigger]pow(b, e1) <= #[trigger]pow(b, e2),
{
    reveal(pow);
    assert forall |b: int, e1: nat, e2: nat| b > 0 && e1 <= e2 implies #[trigger]pow(b, e1) <= #[trigger]pow(b, e2) by
    {
        lemma_pow_increases(b as nat, e1, e2);
    }
}

/// Proof that if an exponentiation result strictly increases when the
/// exponent changes, then the change is an increase. Specifically, if
/// we know `pow(b, e1) < pow(b, e2)`, then we can conclude `e1 < e2`.
pub proof fn lemma_pow_strictly_increases_converse(b: nat, e1: nat, e2: nat)
    requires 
        b > 0,
        pow(b as int, e1) < pow(b as int, e2)
    ensures 
        e1 < e2
{
    if e1 >= e2 
    {
        lemma_pow_increases(b, e2, e1);
        assert(false);
    }
}

/// Proof that if an exponentiation result strictly increases when the
/// exponent changes, then the change is an increase. That is,
/// whenever we know `b > 0` and `pow(b, e1) < pow(b, e2)`, we can
/// conclude `e1 < e2`.
pub proof fn lemma_pow_strictly_increases_converse_auto()
    ensures
        forall |b: nat, e1: nat, e2: nat| b > 0 && pow(b as int, e1) < pow(b as int, e2) ==> e1 < e2,
{
    reveal(pow);
    assert forall |b: nat, e1: nat, e2: nat| b > 0 && pow(b as int, e1) < pow(b as int, e2) implies e1 < e2 by
    {
        lemma_pow_strictly_increases_converse(b, e1, e2);
    }
}

/// Proof that if the exponentiation of a number greater than 1
/// doesn't decrease when the exponent changes, then the change isn't
/// a decrease. Specifically, given that `b > 1` and `pow(b, e1) <=
/// pow(b, e2)`, we can conclude that `e1 <= e2`.
pub proof fn lemma_pow_increases_converse(b: nat, e1: nat, e2: nat)
    requires 
        1 < b,
        pow(b as int, e1) <= pow(b as int, e2)
    ensures 
        e1 <= e2
{
    if e1 > e2 {
        lemma_pow_strictly_increases(b, e2, e1);
        assert(false);
    }
}

/// Proof that whenever the exponentiation of a number greater than 1
/// doesn't decrease when the exponent changes, then the change isn't
/// a decrease
pub proof fn lemma_pow_increases_converse_auto()
    ensures forall |b: nat, e1: nat, e2: nat| 1 < b && pow(b as int, e1) <= pow(b as int, e2) ==> e1 <= e2,
{
    assert forall |b: nat, e1: nat, e2: nat| 1 < b && pow(b as int, e1) <= pow(b as int, e2) implies e1 <= e2 by
    {
        lemma_pow_increases_converse(b, e1, e2);
    }
}

/// Proof that `(b^(xy))^z = (b^x)^(yz)`, given that `x * y` and `y *
/// z` are nonnegative and `b` is positive
pub proof fn lemma_pull_out_pows(b: nat, x: nat, y: nat, z: nat)
    requires 
        b > 0,
    ensures 
        0 <= x * y,
        0 <= y * z,
        pow(pow(b as int, x * y), z) == pow(pow(b as int, x), y * z)
{
    lemma_mul_nonnegative(x as int, y as int);
    lemma_mul_nonnegative(y as int, z as int);
    lemma_pow_positive(b as int, x);
    calc! { (==)
        pow(pow(b as int, x * y), z);
        { lemma_pow_multiplies(b as int, x, y); }
        pow(pow(pow(b as int, x), y), z);
        { lemma_pow_multiplies(pow(b as int, x), y, z); }
        pow(pow(b as int, x), y * z);
    }
}

/// Proof that for any `b`, `x`, `y`, and `z` such that `x * y >= 0`
/// and `y * z >= 0` and `b > 0`, we know `(b^(xy))^z = (b^x)^(yz)`
pub proof fn lemma_pull_out_pows_auto()
    ensures 
        forall |y: nat, z: nat| 0 <= #[trigger](z * y) && 0 <= y * z,        
        forall |b: nat, x: nat, y: nat, z: nat| b > 0 ==> #[trigger]pow(pow(b as int, x * y), z) == pow(pow(b as int, x), y * z)
{
    // reveal(pow);
    lemma_mul_nonnegative_auto();
    assert forall |b: nat, x: nat, y: nat, z: nat| b > 0 implies #[trigger]pow(pow(b as int, x * y), z) == pow(pow(b as int, x), y * z) by
    {
    lemma_pull_out_pows(b, x, y, z);
    }
}

/// Proof that if `e2 <= e1` and `x < pow(b, e1)`, then dividing `x`
/// by `pow(b, e2)` produces a result less than `pow(b, e1 - e2)`
pub proof fn lemma_pow_division_inequality(x: nat, b: nat, e1: nat, e2: nat)
    requires 
        b > 0,
        e2 <= e1,
        x < pow(b as int, e1),
    ensures 
        pow(b as int, e2) > 0,
        // also somewhat annoying that division operator needs explicit type casting
        // because the divisor and dividend need to have the same type
        x as int / pow(b as int, e2) < pow(b as int, (e1 - e2) as nat),
{
    lemma_pow_positive_auto();
    assert(x  as int / pow(b as int, e2) >= pow(b as int, (e1 - e2) as nat) ==> false) by {
        if x  as int / pow(b as int, e2) >= pow(b as int, (e1 - e2) as nat) {
            lemma_mul_inequality(pow(b as int, (e1 - e2) as nat) , x as int / pow(b as int, e2), pow(b as int, e2));
            lemma_fundamental_div_mod(x as int, pow(b as int, e2));
            lemma_mul_is_commutative_auto();
            lemma_pow_adds(b as int, (e1 - e2) as nat, e2);
            lemma_mod_properties_auto();

        }
    };
}

/// Proof that for all `x`, `b`, `e1`, and `e2` such that `e2 <= e1`
/// and `x < pow(b, e1)`, we know that dividing `x` by `pow(b, e2)`
/// produces a result less than `pow(b, e1 - e2)`
pub proof fn lemma_pow_division_inequality_auto()
    ensures
        forall |b: int, e2: nat| b > 0 && e2 <= e2 ==> pow(b, e2) > 0,
        forall |x: nat, b: int, e1: nat, e2: nat| b > 0 && e2 <= e1 && x < pow(b, e1) ==> #[trigger](x as int / pow(b, e2)) < #[trigger]pow(b, (sub1(e1 as int, e2 as int)) as nat),
{
    reveal(pow);
    lemma_pow_positive_auto();

    assert forall |x: nat, b: int, e1: nat, e2: nat| b > 0 && e2 <= e1 && x < pow(b, e1) implies #[trigger](x as int / pow(b, e2)) < #[trigger]pow(b, (sub1(e1 as int, e2 as int)) as nat) by
    {
        lemma_pow_division_inequality(x, b as nat, e1, e2);
    };
}

/// Proof that `pow(b, e)` modulo `b` is 0
pub proof fn lemma_pow_mod(b: nat, e: nat)
    requires 
        b > 0,
        e > 0
    ensures 
        pow(b as int, e) % b as int == 0,
{
    reveal(pow);

    assert(pow(b as int, e) % b as int == (b * pow(b as int, (e - 1) as nat)) % b as int);
    assert((b * pow(b as int, (e - 1) as nat)) % b as int == (pow(b as int, (e - 1) as nat) * b) % b as int) by {
        lemma_mul_is_commutative_auto();
    };
    assert((pow(b as int, (e - 1) as nat) * b) % b as int == 0) by {
        lemma_pow_positive_auto();
        lemma_mod_multiples_basic(pow(b as int, (e - 1) as nat) , b as int);
    };

    // TODO
    // TO BE DiSCUSSED, suprisingly, the calculational proof saying the same thing does not work
    // calc! {
    // (==)
    // pow(b as int, e) % b as int; {}
    // (b * pow(b as int, (e - 1) as nat)) % b as int;
    // { lemma_mul_is_associative_auto(); }
    // (pow(b as int, (e - 1) as nat) * b) % b as int;
    // {
    //     lemma_pow_positive_auto();
    //     lemma_mod_multiples_basic(pow(b as int, (e - 1) as nat) , b as int);
    // }
    // 0;
    // }
}

/// Proof that for any `b` and `e`, we know `pow(b, e)` modulo `b` is 0
pub proof fn lemma_pow_mod_auto()
    ensures forall |b: nat, e: nat| b > 0 && e > 0 ==> #[trigger]pow(b as int, e) % b as int == 0,
{
    assert forall |b: nat, e: nat| b > 0 && e > 0 implies #[trigger]pow(b as int, e) % b as int == 0 by
    {
        lemma_pow_mod(b, e);
    }
}

/// Proof that exponentiation then modulo produces the same result as
/// doing the modulo first, then doing the exponentiation, then doing
/// the modulo again. Specifically, `((b % m)^e) % m == b^e % m`.
pub proof fn lemma_pow_mod_noop(b: int, e: nat, m: int)
    requires m > 0
    ensures pow(b % m, e) % m == pow(b, e) % m
    decreases e
{
    reveal(pow);
    lemma_mod_properties_auto();
    if e > 0 {
    calc! { (==)
        pow(b % m, e) % m; {}
        ((b % m) * pow(b % m, (e - 1) as nat)) % m;
        { lemma_mul_mod_noop_general(b, pow(b % m, (e - 1) as nat), m); }
        ((b % m) * (pow(b % m, (e - 1) as nat) % m) % m) % m;
        { lemma_pow_mod_noop(b, (e - 1) as nat, m); }
        ((b % m) * (pow(b, (e - 1) as nat) % m) % m) % m;
        { lemma_mul_mod_noop_general(b, pow(b, (e - 1) as nat), m); }
        (b * (pow(b, (e - 1) as nat)) % m) % m; {}
        (b * (pow(b, (e - 1) as nat))) % m; {}
        pow(b, e) % m;
    }
    }
}

/// Proof that exponentiation then modulo produces the same result as
/// doing the modulo first, then doing the exponentiation, then doing
/// the modulo again
pub proof fn lemma_pow_mod_noop_auto()
    ensures forall |b: int, e: nat, m: int| m > 0 ==> #[trigger]pow(b % m, e) % m == pow(b, e) % m,
{
    assert forall |b: int, e: nat, m: int| m > 0 implies #[trigger]pow(b % m, e) % m == pow(b, e) % m by
    {
        lemma_pow_mod_noop(b, e, m);
    }
}

}
