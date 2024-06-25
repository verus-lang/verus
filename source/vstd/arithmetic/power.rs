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
use super::super::calc_macro::*;
#[allow(unused_imports)]
use super::super::prelude::*;

verus! {

use super::super::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use super::super::arithmetic::internals::general_internals::{is_le};
#[cfg(verus_keep_ghost)]
use super::super::arithmetic::mul::{
    lemma_mul_inequality,
    lemma_mul_nonnegative,
    lemma_mul_strictly_increases,
    lemma_mul_left_inequality,
    group_mul_basics,
    lemma_mul_increases,
    lemma_mul_is_commutative,
    group_mul_is_distributive,
    lemma_mul_is_associative,
};
#[cfg(verus_keep_ghost)]
use super::internals::mul_internals::{group_mul_properties_internal, lemma_mul_induction_auto};
#[cfg(verus_keep_ghost)]
use super::super::math::{sub as sub1};

/// This function performs exponentiation recursively, to compute `b`
/// to the power of a natural number `e`
pub open spec fn pow(b: int, e: nat) -> int
    decreases e,
{
    if e == 0 {
        1
    } else {
        b * pow(b, (e - 1) as nat)
    }
}

/// Proof that the given integer `b` to the power of 0 is 1
pub broadcast proof fn lemma_pow0(b: int)
    ensures
        #[trigger] pow(b, 0) == 1,
{
    reveal(pow);
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

/// Proof that the given integer `b` to the power of 1 is `b`
pub broadcast proof fn lemma_pow1(b: int)
    ensures
        #[trigger] pow(b, 1) == b,
{
    calc! {
        (==)
        pow(b, 1); {
            reveal(pow);
        }
        b * pow(b, 0); {
            lemma_pow0(b);
        }
        b * 1; {
            lemma_mul_basics_auto();
        }
        b;
    }
}

/// Proof that 0 to the power of the given positive integer `e` is 0
pub broadcast proof fn lemma0_pow(e: nat)
    requires
        e > 0,
    ensures
        #[trigger] pow(0, e) == 0,
    decreases e,
{
    reveal(pow);
    lemma_mul_basics_auto();
    if e != 1 {
        lemma0_pow((e - 1) as nat);
    }
}

/// Proof that 1 to the power of the given natural number `e` is 1
pub broadcast proof fn lemma1_pow(e: nat)
    ensures
        #[trigger] pow(1, e) == 1,
    decreases e,
{
    reveal(pow);
    lemma_mul_basics_auto();
    if e != 0 {
        lemma1_pow((e - 1) as nat);
    }
}

/// Proof that taking the given number `x` to the power of 2 produces `x * x`
pub broadcast proof fn lemma_square_is_pow2(x: int)
    ensures
        #[trigger] pow(x, 2) == x * x,
{
    reveal_with_fuel(pow, 3);
}

/// Proof that taking the given positive integer `b` to the power of
/// the given natural number `n` produces a positive result
pub broadcast proof fn lemma_pow_positive(b: int, e: nat)
    requires
        b > 0,
    ensures
        0 < #[trigger] pow(b, e),
{
    // dafny does not need to reveal
    reveal(pow);
    broadcast use lemma_mul_increases;
    broadcast use lemma_pow0;

    lemma_mul_induction_auto(e as int, |u: int| 0 <= u ==> 0 < pow(b, u as nat));
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

/// Proof that taking an integer `b` to the power of the sum of two
/// natural numbers `e1` and `e2` is equivalent to multiplying `b` to
/// the power of `e1` by `b` to the power of `e2`
pub broadcast proof fn lemma_pow_adds(b: int, e1: nat, e2: nat)
    ensures
        #[trigger] pow(b, e1 + e2) == pow(b, e1) * pow(b, e2),
    decreases e1,
{
    if e1 == 0 {
        calc! {
            (==)
            pow(b, e1) * pow(b, e2); {
                lemma_pow0(b);
            }
            1 * pow(b, e2); {
                lemma_mul_basics_auto();
            }
            pow(b, 0 + e2);
        }
    } else {
        calc! {
            (==)
            pow(b, e1) * pow(b, e2); {
                reveal(pow);
            }
            (b * pow(b, (e1 - 1) as nat)) * pow(b, e2); {
                lemma_mul_is_associative_auto();
            }
            b * (pow(b, (e1 - 1) as nat) * pow(b, e2)); {
                lemma_pow_adds(b, (e1 - 1) as nat, e2);
            }
            b * pow(b, (e1 - 1 + e2) as nat); {
                reveal(pow);
            }
            pow(b, e1 + e2);
        }
    }
}

/// Proof that if `e1 >= e2`, then `b` to the power of `e1` is equal
/// to the product of `b` to the power of `e1 - e2` and `b` to the
/// power of `e2`
pub broadcast proof fn lemma_pow_sub_add_cancel(b: int, e1: nat, e2: nat)
    requires
        e1 >= e2,
    ensures
        #[trigger] pow(b, (e1 - e2) as nat) * pow(b, e2) == pow(b, e1),
    decreases e1,
{
    lemma_pow_adds(b, (e1 - e2) as nat, e2);
}

/// Proof that, as long as `e1 <= e2`, taking a positive integer `b`
/// to the power of `e2 - e1` is equivalent to dividing `b` to the
/// power of `e2` by `b` to the power of `e1`.
pub broadcast proof fn lemma_pow_subtracts(b: int, e1: nat, e2: nat)
    requires
        b > 0,
        e1 <= e2,
    ensures
        pow(b, e1) > 0,
        #[trigger] pow(b, (e2 - e1) as nat) == pow(b, e2) / pow(b, e1) > 0,
{
    broadcast use lemma_pow_positive;

    calc! {
        (==)
        pow(b, e2) / pow(b, e1); {
            lemma_pow_sub_add_cancel(b, e2, e1);
        }
        pow(b, (e2 - e1) as nat) * pow(b, e1) / pow(b, e1); {
            lemma_div_by_multiple(pow(b, (e2 - e1) as nat), pow(b, e1));
        }
        pow(b, (e2 - e1) as nat);
    }
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

/// Proof that `a` to the power of `b * c` is equal to the result of
/// taking `a` to the power of `b`, then taking that to the power of
/// `c`
pub broadcast proof fn lemma_pow_multiplies(a: int, b: nat, c: nat)
    ensures
        0 <= b * c,
        #[trigger] pow(pow(a, b), c) == pow(a, b * c),
    decreases c,
{
    lemma_mul_nonnegative(b as int, c as int);
    if c == 0 {
        lemma_mul_basics_auto();
        calc! {
            (==)
            pow(a, (b * c) as nat); {
                lemma_pow0(a);
            }
            1; {
                lemma_pow0(pow(a, b));
            }
            pow(pow(a, b), c);
        }
    } else {
        calc! {
            (==)
            b * c - b; {
                lemma_mul_basics_auto();
            }
            b * c - b * 1; { lemma_mul_is_distributive_auto() }
            b * (c - 1);
        }
        lemma_mul_nonnegative(b as int, c - 1);
        assert(0 <= b * c - b);
        calc! {
            (==)
            pow(a, b * c); {}
            pow(a, (b + b * c - b) as nat); {
                lemma_pow_adds(a, b, (b * c - b) as nat);
            }
            pow(a, b) * pow(a, (b * c - b) as nat); {}
            pow(a, b) * pow(a, (b * (c - 1)) as nat); {
                lemma_pow_multiplies(a, b, (c - 1) as nat);
            }
            pow(a, b) * pow(pow(a, b), (c - 1) as nat); {
                reveal(pow);
            }
            pow(pow(a, b), c);
        }
    }
}

// TODO: temporarily needed until `broadcast use` can be used in calc!
proof fn lemma_mul_is_commutative_auto()
    ensures
        forall|x: int, y: int| #[trigger] (x * y) == y * x,
{
    broadcast use lemma_mul_is_commutative;

}

/// Proof that `a * b` to the power of `e` is equal to the product of
/// `a` to the power of `e` and `b` to the power of `e`
pub broadcast proof fn lemma_pow_distributes(a: int, b: int, e: nat)
    ensures
        #[trigger] pow(a * b, e) == pow(a, e) * pow(b, e),
    decreases e,
{
    reveal(pow);
    lemma_mul_basics_auto();
    if e >= 1 {
        calc! {
            (==)
            pow(a * b, e); {
                reveal(pow);
            }
            (a * b) * pow(a * b, (e - 1) as nat); {
                lemma_pow_distributes(a, b, (e - 1) as nat);
            }
            (a * b) * (pow(a, (e - 1) as nat) * pow(b, (e - 1) as nat)); {
                lemma_mul_is_associative_auto();
                lemma_mul_is_commutative_auto();
                assert((a * b * pow(a, (e - 1) as nat)) * pow(b, (e - 1) as nat) == (a * pow(
                    a,
                    (e - 1) as nat,
                ) * b) * pow(b, (e - 1) as nat));
            }
            (a * pow(a, (e - 1) as nat)) * (b * pow(b, (e - 1) as nat)); {
                reveal(pow);
            }
            pow(a, e) * pow(b, e);
        }
    }
}

pub broadcast group group_pow_properties {
    lemma_pow0,
    lemma_pow1,
    lemma_pow_distributes,
    lemma_pow_adds,
    lemma_pow_sub_add_cancel,
    group_mul_properties_internal,
    lemma_mul_increases,
    lemma_mul_strictly_increases,
}

/// Proof of various useful properties of [`pow`] (exponentiation)
proof fn lemma_pow_properties_prove_pow_auto()
    ensures
        forall|x: int| pow(x, 0) == 1,
        forall|x: int| #[trigger] pow(x, 1) == x,
        forall|x: int, y: int| y == 0 ==> #[trigger] pow(x, y as nat) == 1,
        forall|x: int, y: int| y == 1 ==> #[trigger] pow(x, y as nat) == x,
        forall|x: int, y: int| 0 < x && 0 < y ==> x <= #[trigger] (x * y as nat),
        forall|x: int, y: int| 0 < x && 1 < y ==> x < #[trigger] (x * y as nat),
        forall|x: int, y: nat, z: nat| #[trigger] pow(x, y + z) == pow(x, y) * pow(x, z),
        forall|x: int, y: nat, z: nat|
            y >= z ==> #[trigger] pow(x, (y - z) as nat) * pow(x, z) == pow(x, y),
        forall|x: int, y: nat, z: nat| #[trigger] pow(x * y, z) == pow(x, z) * pow(y as int, z),
{
    reveal(pow);
    broadcast use group_pow_properties;

}

/// Proof that a number greater than 1 raised to a power strictly
/// increases as the power strictly increases. Specifically, given
/// that `b > 1` and `e1 < e2`, we can conclude that `pow(b, e1) <
/// pow(b, e2)`.
pub broadcast proof fn lemma_pow_strictly_increases(b: nat, e1: nat, e2: nat)
    requires
        1 < b,
        e1 < e2,
    ensures
        #[trigger] pow(b as int, e1) < #[trigger] pow(b as int, e2),
{
    let f = |e: int| 0 < e ==> pow(b as int, e1) < pow(b as int, (e1 + e) as nat);
    assert forall|i: int| (#[trigger] is_le(0, i) && f(i)) implies f(i + 1) by {
        calc! {
            (<=)
            pow(b as int, (e1 + i) as nat); (<=) {
                lemma_pow_positive(b as int, (e1 + i) as nat);
                lemma_mul_left_inequality(pow(b as int, (e1 + i) as nat), 1, b as int);
            }
            pow(b as int, (e1 + i) as nat) * b; (<=) {
                lemma_pow1(b as int);
            }
            pow(b as int, (e1 + i) as nat) * pow(b as int, 1); (<=) {
                lemma_pow_adds(b as int, (e1 + i) as nat, 1nat);
            }
            pow(b as int, (e1 + i + 1) as nat);
        }
        assert(0 < i ==> pow(b as int, e1) < pow(b as int, (e1 + i) as nat));
        if (i == 0) {
            assert(pow(b as int, e1) < pow(b as int, (e1 + 1) as nat)) by {
                reveal(pow);
                assert(pow(b as int, e1) < b * pow(b as int, e1)) by {
                    // cannot be replaced to lemma_pow_auto()
                    assert(pow(b as int, e1) > 0) by {
                        broadcast use lemma_pow_positive;

                    }
                    lemma_mul_strictly_increases(b as int, pow(b as int, e1));
                };
            };
        }
        assert(f(i + 1));
    }
    lemma_mul_induction_auto(e2 - e1, f);
}

/// Proof that a positive number raised to a power increases as the
/// power increases. Specifically, since `e1 <= e2`, we know `pow(b,
/// e1) <= pow(b, e2)`.
pub broadcast proof fn lemma_pow_increases(b: nat, e1: nat, e2: nat)
    requires
        b > 0,
        e1 <= e2,
    ensures
        #[trigger] pow(b as int, e1) <= #[trigger] pow(b as int, e2),
{
    if e1 != e2 {
        if b > 1 {
            lemma_pow_strictly_increases(b, e1, e2);
        } else {
            lemma1_pow(e1);
            lemma1_pow(e2);
        }
    }
}

/// Proof that if an exponentiation result strictly increases when the
/// exponent changes, then the change is an increase. Specifically, if
/// we know `pow(b, e1) < pow(b, e2)`, then we can conclude `e1 < e2`.
pub broadcast proof fn lemma_pow_strictly_increases_converse(b: nat, e1: nat, e2: nat)
    requires
        b > 0,
        #[trigger] pow(b as int, e1) < #[trigger] pow(b as int, e2),
    ensures
        e1 < e2,
{
    if e1 >= e2 {
        lemma_pow_increases(b, e2, e1);
        assert(false);
    }
}

/// Proof that if the exponentiation of a number greater than 1
/// doesn't decrease when the exponent changes, then the change isn't
/// a decrease. Specifically, given that `b > 1` and `pow(b, e1) <=
/// pow(b, e2)`, we can conclude that `e1 <= e2`.
pub broadcast proof fn lemma_pow_increases_converse(b: nat, e1: nat, e2: nat)
    requires
        1 < b,
        #[trigger] pow(b as int, e1) <= #[trigger] pow(b as int, e2),
    ensures
        e1 <= e2,
{
    if e1 > e2 {
        lemma_pow_strictly_increases(b, e2, e1);
        assert(false);
    }
}

/// Proof that `(b^(xy))^z = (b^x)^(yz)`, given that `x * y` and `y *
/// z` are nonnegative and `b` is positive
pub broadcast proof fn lemma_pull_out_pows(b: nat, x: nat, y: nat, z: nat)
    requires
        b > 0,
    ensures
        0 <= x * y,
        0 <= y * z,
        #[trigger] pow(pow(b as int, x * y), z) == pow(pow(b as int, x), y * z),
{
    lemma_mul_nonnegative(x as int, y as int);
    lemma_mul_nonnegative(y as int, z as int);
    lemma_pow_positive(b as int, x);
    calc! {
        (==)
        pow(pow(b as int, x * y), z); {
            lemma_pow_multiplies(b as int, x, y);
        }
        pow(pow(pow(b as int, x), y), z); {
            lemma_pow_multiplies(pow(b as int, x), y, z);
        }
        pow(pow(b as int, x), y * z);
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
        #[trigger] (x as int / pow(b as int, e2)) < #[trigger] pow(b as int, (e1 - e2) as nat),
{
    broadcast use lemma_pow_positive;

    assert(x as int / pow(b as int, e2) >= pow(b as int, (e1 - e2) as nat) ==> false) by {
        if x as int / pow(b as int, e2) >= pow(b as int, (e1 - e2) as nat) {
            lemma_mul_inequality(
                pow(b as int, (e1 - e2) as nat),
                x as int / pow(b as int, e2),
                pow(b as int, e2),
            );
            lemma_fundamental_div_mod(x as int, pow(b as int, e2));
            broadcast use lemma_mul_is_commutative, group_mod_properties;

            lemma_pow_adds(b as int, (e1 - e2) as nat, e2);
        }
    };
}

/// Proof that `pow(b, e)` modulo `b` is 0
pub broadcast proof fn lemma_pow_mod(b: nat, e: nat)
    requires
        b > 0,
        e > 0,
    ensures
        #[trigger] pow(b as int, e) % b as int == 0,
{
    reveal(pow);
    assert(pow(b as int, e) % b as int == (b * pow(b as int, (e - 1) as nat)) % b as int);
    assert((b * pow(b as int, (e - 1) as nat)) % b as int == (pow(b as int, (e - 1) as nat) * b)
        % b as int) by {
        broadcast use lemma_mul_is_commutative;

    };
    assert((pow(b as int, (e - 1) as nat) * b) % b as int == 0) by {
        broadcast use lemma_pow_positive;

        lemma_mod_multiples_basic(pow(b as int, (e - 1) as nat), b as int);
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

/// Proof that exponentiation then modulo produces the same result as
/// doing the modulo first, then doing the exponentiation, then doing
/// the modulo again. Specifically, `((b % m)^e) % m == b^e % m`.
pub broadcast proof fn lemma_pow_mod_noop(b: int, e: nat, m: int)
    requires
        m > 0,
    ensures
        #[trigger] pow(b % m, e) % m == pow(b, e) % m,
    decreases e,
{
    reveal(pow);
    broadcast use group_mod_properties;

    if e > 0 {
        calc! {
            (==)
            pow(b % m, e) % m; {}
            ((b % m) * pow(b % m, (e - 1) as nat)) % m; {
                lemma_mul_mod_noop_general(b, pow(b % m, (e - 1) as nat), m);
            }
            ((b % m) * (pow(b % m, (e - 1) as nat) % m) % m) % m; {
                lemma_pow_mod_noop(b, (e - 1) as nat, m);
            }
            ((b % m) * (pow(b, (e - 1) as nat) % m) % m) % m; {
                lemma_mul_mod_noop_general(b, pow(b, (e - 1) as nat), m);
            }
            (b * (pow(b, (e - 1) as nat)) % m) % m; {}
            (b * (pow(b, (e - 1) as nat))) % m; {}
            pow(b, e) % m;
        }
    }
}

} // verus!
