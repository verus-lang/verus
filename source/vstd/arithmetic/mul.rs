//! This file contains proofs related to integer multiplication (`*`).
//! These are part of the math standard library.
//!
//! It's based on the following file from the Dafny math standard
//! library:
//! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Mul.dfy`.
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

use super::super::arithmetic::internals::mul_internals_nonlinear as MulINL;
use super::super::arithmetic::internals::mul_internals::*;

/// Proof that multiplication using `*` is equivalent to
/// multiplication using a recursive definition. Specifically,
/// `x * y` is equivalent in that way.
pub broadcast proof fn lemma_mul_is_mul_recursive(x: int, y: int)
    ensures
        #[trigger] (x * y) == mul_recursive(x, y),
{
    if (x >= 0) {
        lemma_mul_is_mul_pos(x, y);
        assert(x * y == mul_pos(x, y));
        assert((x * y) == mul_recursive(x, y));
    } else {
        lemma_mul_is_mul_pos(-x, y);
        assert(x * y == -1 * (-x * y)) by { lemma_mul_is_associative(-1, -x, y) };  // OBSERVE
        assert((x * y) == mul_recursive(x, y));
    }
}

/// Proof that multiplying two positive integers with `*` results in
/// the same product as would be achieved by recursive addition.
/// Specifically, `x * y == mul_pos(x, y)`.
pub proof fn lemma_mul_is_mul_pos(x: int, y: int)
    requires
        x >= 0,
    ensures
        x * y == mul_pos(x, y),
{
    reveal(mul_pos);
    lemma_mul_induction_auto(x, |u: int| u >= 0 ==> u * y == mul_pos(u, y));
}

pub proof fn lemma_mul_basics(x: int)
    ensures
        0 * x == 0,
        x * 0 == 0,
        x * 1 == x,
        1 * x == x,
{
}

/// Proof of basic properties of multiplication by `x`, specifically
/// what happens when multiplying by 0 or 1
pub broadcast proof fn lemma_mul_basics_1(x: int)
    ensures
        #[trigger] (0 * x) == 0,
{
}

/// Proof of basic properties of multiplication by `x`, specifically
/// what happens when multiplying by 0 or 1
pub broadcast proof fn lemma_mul_basics_2(x: int)
    ensures
        #[trigger] (x * 0) == 0,
{
}

/// Proof of basic properties of multiplication by `x`, specifically
/// what happens when multiplying by 0 or 1
pub broadcast proof fn lemma_mul_basics_3(x: int)
    ensures
        #[trigger] (x * 1) == x,
{
}

/// Proof of basic properties of multiplication by `x`, specifically
/// what happens when multiplying by 0 or 1
pub broadcast proof fn lemma_mul_basics_4(x: int)
    ensures
        #[trigger] (1 * x) == x,
{
}

pub broadcast group group_mul_basics {
    lemma_mul_basics_1,
    lemma_mul_basics_2,
    lemma_mul_basics_3,
    lemma_mul_basics_4,
}

/// Proof that `x * y` is nonzero if and only if both `x` and `y` are nonzero
pub broadcast proof fn lemma_mul_nonzero(x: int, y: int)
    ensures
        #[trigger] (x * y) != 0 <==> x != 0 && y != 0,
{
    MulINL::lemma_mul_nonzero(x, y);
}

/// Proof that any integer multiplied by 0 results in a product of 0
pub broadcast proof fn lemma_mul_by_zero_is_zero(x: int)
    ensures
        #![trigger x * 0]
        #![trigger 0 * x]
        x * 0 == 0 && 0 * x == 0,
{
    assert forall|x: int| #![trigger x * 0] #![trigger 0 * x] x * 0 == 0 && 0 * x == 0 by {
        lemma_mul_basics(x);
    }
}

/// Proof that multiplication is associative, specifically that
/// `x * (y * z) == (x * y) * z`.
pub broadcast proof fn lemma_mul_is_associative(x: int, y: int, z: int)
    ensures
        #![trigger x * (y * z)]
        #![trigger (x * y) * z]
        x * (y * z) == (x * y) * z,
{
    MulINL::lemma_mul_is_associative(x, y, z);
}

/// Proof that multiplication is commutative, specifically that
/// `x * y == y * x`.
pub broadcast proof fn lemma_mul_is_commutative(x: int, y: int)
    ensures
        #[trigger] (x * y) == y * x,
{
}

/// Proof that, since the product of the two integers `x` and `y` is
/// nonnegative, that product is greater than or equal to each of `x`
/// and `y`
pub broadcast proof fn lemma_mul_ordering(x: int, y: int)
    requires
        x != 0,
        y != 0,
        0 <= x * y,
    ensures
        #[trigger] (x * y) >= x && x * y >= y,
{
    MulINL::lemma_mul_ordering(x, y);
}

/*
    We don't port LemmaMulEquality or LemmaMulEqualityAuto from the
    Dafny standard library for arithmetic, since they're never useful.
    They say that `x == y ==> x * z == y * z`, which is trivial. It
    follows immediately from the basic SMT axiom that functions and
    operators (including multiplication) have equal values when
    applied to equal arguments.
*/

/// Proof that, since `x <= y` and `z >= 0`, `x * z <= y * z`
pub broadcast proof fn lemma_mul_inequality(x: int, y: int, z: int)
    requires
        x <= y,
        z >= 0,
    ensures
        #[trigger] (x * z) <= #[trigger] (y * z),
{
    lemma_mul_induction_auto(z, |u: int| u >= 0 ==> x * u <= y * u);
}

/// Proof that since `x < y` and `z > 0`, `x * z < y * z`.
pub broadcast proof fn lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires
        x < y,
        z > 0,
    ensures
        #[trigger] (x * z) < #[trigger] (y * z),
{
    MulINL::lemma_mul_strict_inequality(x, y, z);
}

/// Proof that since `x` is bounded above by `xbound` and `y` is
/// bounded above by `ybound`, the product of `x` and `y` is bounded
/// above by the product of the bounds
pub broadcast proof fn lemma_mul_upper_bound(x: int, xbound: int, y: int, ybound: int)
    requires
        x <= xbound,
        y <= ybound,
        0 <= x,
        0 <= y,
    ensures
        #[trigger] (x * y) <= #[trigger] (xbound * ybound),
{
    lemma_mul_inequality(x, xbound, y);
    lemma_mul_inequality(y, ybound, xbound);
}

/// Proof that when `x` has an exclusive upper bound `xbound` and `y`
/// has an exclusive upper bound `ybound`, that the product of `x` and
/// `y` is bounded above by the product of the predecessors of their
/// upper bounds. In other words, `x * y <= (xbound - 1) * (ybound - 1)`.
pub broadcast proof fn lemma_mul_strict_upper_bound(x: int, xbound: int, y: int, ybound: int)
    requires
        x < xbound,
        y < ybound,
        0 < x,
        0 < y,
    ensures
        #[trigger] (x * y) <= #[trigger] ((xbound - 1) * (ybound - 1)),
{
    lemma_mul_inequality(x, xbound - 1, y);
    lemma_mul_inequality(y, ybound - 1, xbound - 1);
}

/// Proof that multiplying the positive integer `x` by respectively
/// `y` and `z` maintains the order of `y` and `z`. Specifically, `y
/// <= z ==> x * y <= x * z` and `y < z ==> x * y < x * z`.
pub broadcast proof fn lemma_mul_left_inequality(x: int, y: int, z: int)
    requires
        0 < x,
    ensures
        y <= z ==> #[trigger] (x * y) <= #[trigger] (x * z),
        y < z ==> x * y < x * z,
{
    lemma_mul_induction_auto(x, |u: int| u > 0 ==> y <= z ==> u * y <= u * z);
    lemma_mul_induction_auto(x, |u: int| u > 0 ==> y < z ==> u * y < u * z);
}

/// Proof that if `x` and `y` have equal results when multiplied by
/// nonzero `m`, then they're equal
pub broadcast proof fn lemma_mul_equality_converse(m: int, x: int, y: int)
    requires
        m != 0,
        #[trigger] (m * x) == #[trigger] (m * y),
    ensures
        x == y,
{
    lemma_mul_induction_auto(m, |u| x > y && 0 < u ==> x * u > y * u);
    lemma_mul_induction_auto(m, |u: int| x < y && 0 < u ==> x * u < y * u);
    lemma_mul_induction_auto(m, |u: int| x > y && 0 > u ==> x * u < y * u);
    lemma_mul_induction_auto(m, |u: int| x < y && 0 > u ==> x * u > y * u);
}

/// Proof that since `x * z <= y * z` and `z > 0`, that `x <= y`
pub broadcast proof fn lemma_mul_inequality_converse(x: int, y: int, z: int)
    requires
        #[trigger] (x * z) <= #[trigger] (y * z),
        z > 0,
    ensures
        x <= y,
{
    lemma_mul_induction_auto(z, |u: int| x * u <= y * u && u > 0 ==> x <= y);
}

/// Proof that since `x * z < y * z` and `z >= 0`, we know `x < y`
pub broadcast proof fn lemma_mul_strict_inequality_converse(x: int, y: int, z: int)
    requires
        #[trigger] (x * z) < #[trigger] (y * z),
        z >= 0,
    ensures
        x < y,
{
    lemma_mul_induction_auto(z, |u: int| x * u < y * u && u >= 0 ==> x < y);
}

/// Proof that multiplication distributes over addition, specifically that
/// `x * (y + z) == x * y + x * z`
pub broadcast proof fn lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures
        #[trigger] (x * (y + z)) == x * y + x * z,
{
    MulINL::lemma_mul_is_distributive_add(x, y, z);
}

/// Proof that multiplication distributes over addition, specifically that
/// `(y + z) * x == y * x + z * x`
pub broadcast proof fn lemma_mul_is_distributive_add_other_way(x: int, y: int, z: int)
    ensures
        #[trigger] ((y + z) * x) == y * x + z * x,
{
    broadcast use group_mul_properties_internal;

}

/// Proof that multiplication distributes over subtraction, specifically that
/// `x * (y - z) == x * y - x * z`
pub broadcast proof fn lemma_mul_is_distributive_sub(x: int, y: int, z: int)
    ensures
        #[trigger] (x * (y - z)) == x * y - x * z,
{
    broadcast use group_mul_properties_internal;

}

/// Proof that multiplication distributes over subtraction when the
/// subtraction happens in the multiplicand (i.e., in the left-hand
/// argument to `*`). Specifically, `(y - z) * x == y * x - z * x`.
pub broadcast proof fn lemma_mul_is_distributive_sub_other_way(x: int, y: int, z: int)
    ensures
        #[trigger] ((y - z) * x) == y * x - z * x,
{
    lemma_mul_is_distributive_sub(x, y, z);
    lemma_mul_is_commutative(x, y - z);
    lemma_mul_is_commutative(x, y);
    lemma_mul_is_commutative(x, z);
}

pub broadcast group group_mul_is_distributive {
    lemma_mul_is_distributive_add,
    lemma_mul_is_distributive_add_other_way,
    lemma_mul_is_distributive_sub,
    lemma_mul_is_distributive_sub_other_way,
}

pub broadcast group group_mul_is_commutative_and_distributive {
    lemma_mul_is_commutative,
    group_mul_is_distributive,
}

/// Proof that multiplication is commutative, distributes over
/// addition, and distributes over subtraction, in the specific cases
/// where one of the arguments to the multiplication is `x` and the
/// other arguments are `y` and `z`
proof fn lemma_mul_is_distributive(x: int, y: int, z: int)
    ensures
        x * (y + z) == x * y + x * z,
        x * (y - z) == x * y - x * z,
        (y + z) * x == y * x + z * x,
        (y - z) * x == y * x - z * x,
        x * (y + z) == (y + z) * x,
        x * (y - z) == (y - z) * x,
        x * y == y * x,
        x * z == z * x,
{
    broadcast use group_mul_is_commutative_and_distributive;

}

/// Proof that multiplication distributes over addition and
/// subtraction, whether the addition or subtraction happens in the
/// first or the second argument to the multiplication
// pub broadcast proof fn lemma_mul_is_distributive_plus(x: int, y: int, z: int)
//     ensures
//         forall|x: int, y: int, z: int| #[trigger] (x * (y + z)) == x * y + x * z,
//         forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z,
//         forall|x: int, y: int, z: int| #[trigger] ((y + z) * x) == y * x + z * x,
//         forall|x: int, y: int, z: int| #[trigger] ((y - z) * x) == y * x - z * x,
// {
//     lemma_mul_is_distributive_add_auto();
//     lemma_mul_is_distributive_sub_auto();
//     broadcast use lemma_mul_is_commutative;
// }
/// Proof that if `x` and `y` are both positive, then their product is
/// also positive
pub broadcast proof fn lemma_mul_strictly_positive(x: int, y: int)
    ensures
        (0 < x && 0 < y) ==> (0 < #[trigger] (x * y)),
{
    MulINL::lemma_mul_strictly_positive(x, y);
}

/// Proof that since `x > 1` and `y > 0`, `y < x * y`
pub broadcast proof fn lemma_mul_strictly_increases(x: int, y: int)
    requires
        1 < x,
        0 < y,
    ensures
        y < #[trigger] (x * y),
{
    lemma_mul_induction_auto(x, |u: int| 1 < u ==> y < u * y);
}

/// Proof that since `x` and `y` are both positive, their product is
/// greater than or equal to `y`
pub broadcast proof fn lemma_mul_increases(x: int, y: int)
    requires
        0 < x,
        0 < y,
    ensures
        y <= #[trigger] (x * y),
{
    lemma_mul_induction_auto(x, |u: int| 0 < u ==> y <= u * y);
}

/// Proof that since `x` and `y` are non-negative, their product is
/// non-negative
pub broadcast proof fn lemma_mul_nonnegative(x: int, y: int)
    requires
        0 <= x,
        0 <= y,
    ensures
        0 <= #[trigger] (x * y),
{
    lemma_mul_induction_auto(x, |u: int| 0 <= u ==> 0 <= u * y);
}

/// Proof that negating `x` or `y` before multiplying them together
/// produces the negation of the product of `x` and `y`
pub broadcast proof fn lemma_mul_unary_negation(x: int, y: int)
    ensures
        #![trigger (-x) * y]
        #![trigger x * (-y)]
        (-x) * y == -(x * y) == x * (-y),
{
    lemma_mul_induction_auto(x, |u: int| (-u) * y == -(u * y) == u * (-y));
}

/// Proof that multiplying `-x` and `-y` produces the same product as
/// multiplying `x` and `y`
pub broadcast proof fn lemma_mul_cancels_negatives(x: int, y: int)
    ensures
        #[trigger] (x * y) == (-x) * (-y),
{
    lemma_mul_induction_auto(x, |u: int| (-u) * y == -(u * y) == u * (-y));
}

pub broadcast group group_mul_properties {
    group_mul_basics,
    lemma_mul_strict_inequality,
    lemma_mul_inequality,
    group_mul_is_commutative_and_distributive,
    lemma_mul_is_associative,
    lemma_mul_ordering,
    lemma_mul_nonzero,
    lemma_mul_nonnegative,
    lemma_mul_strictly_increases,
    lemma_mul_increases,
}

// Check that the group_mul_properties broadcast group group_provides the same properties as the _auto lemma it replaces
proof fn lemma_mul_properties_prove_mul_properties_auto()
    ensures
        forall|x: int, y: int| #[trigger] (x * y) == y * x,
        forall|x: int| #![trigger x * 1] #![trigger 1 * x] x * 1 == 1 * x == x,
        forall|x: int, y: int, z: int| x < y && z > 0 ==> #[trigger] (x * z) < #[trigger] (y * z),
        forall|x: int, y: int, z: int|
            x <= y && z >= 0 ==> #[trigger] (x * z) <= #[trigger] (y * z),
        forall|x: int, y: int, z: int| #[trigger] (x * (y + z)) == x * y + x * z,
        forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z,
        forall|x: int, y: int, z: int| #[trigger] ((y + z) * x) == y * x + z * x,
        forall|x: int, y: int, z: int| #[trigger] ((y - z) * x) == y * x - z * x,
        forall|x: int, y: int, z: int|
            #![trigger x * (y * z)]
            #![trigger (x * y) * z]
            x * (y * z) == (x * y) * z,
        forall|x: int, y: int| #[trigger] (x * y) != 0 <==> x != 0 && y != 0,
        forall|x: int, y: int| 0 <= x && 0 <= y ==> 0 <= #[trigger] (x * y),
        forall|x: int, y: int|
            0 < x && 0 < y && 0 <= x * y ==> x <= #[trigger] (x * y) && y <= (x * y),
        forall|x: int, y: int| (1 < x && 0 < y) ==> (y < #[trigger] (x * y)),
        forall|x: int, y: int| (0 < x && 0 < y) ==> (y <= #[trigger] (x * y)),
        forall|x: int, y: int| (0 < x && 0 < y) ==> (0 < #[trigger] (x * y)),
{
    broadcast use group_mul_properties;

}

} // verus!
