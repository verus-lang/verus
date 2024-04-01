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
use builtin::*;
use builtin_macros::*;

verus! {

use crate::arithmetic::internals::mul_internals_nonlinear as MulINL;
use crate::arithmetic::internals::mul_internals::*;

/// Proof that multiplication using `*` is equivalent to
/// multiplication using a recursive definition. Specifically,
/// `x * y` is equivalent in that way.
pub proof fn lemma_mul_is_mul_recursive(x: int, y: int)
    ensures
        (x * y) == mul_recursive(x, y),
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

/// Proof that multiplication using `*` is equivalent to
/// multiplication using a recursive definition
pub proof fn lemma_mul_is_mul_recursive_auto()
    ensures
        forall|x: int, y: int| x * y == mul_recursive(x, y),
{
    assert forall|x: int, y: int| x * y == mul_recursive(x, y) by { lemma_mul_is_mul_recursive(x, y)
    };
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

/// Proof of basic properties of multiplication by `x`, specifically
/// what happens when multiplying by 0 or 1
pub proof fn lemma_mul_basics(x: int)
    ensures
        0 * x == 0,
        x * 0 == 0,
        x * 1 == x,
        1 * x == x,
{
}

/// Proof of basic properties of multiplication, specifically what
/// happens when multiplying by 0 or 1
pub proof fn lemma_mul_basics_auto()
    ensures
        forall|x: int| #[trigger] (0 * x) == 0,
        forall|x: int| #[trigger] (x * 0) == 0,
        forall|x: int| #[trigger] (1 * x) == x,
        forall|x: int| #[trigger] (x * 1) == x,
{
}

/// Proof that `x * y` is nonzero if and only if both `x` and `y` are nonzero
pub proof fn lemma_mul_nonzero(x: int, y: int)
    ensures
        x * y != 0 <==> x != 0 && y != 0,
{
    MulINL::lemma_mul_nonzero(x, y);
}

/// Proof that a product is nonzero if and only if both factors are nonzero
pub proof fn lemma_mul_nonzero_auto()
    ensures
        forall|x: int, y: int| #[trigger] (x * y) != 0 <==> x != 0 && y != 0,
{
    assert forall|x: int, y: int| #[trigger] (x * y) != 0 <==> x != 0 && y != 0 by {
        lemma_mul_nonzero(x, y);
    }
}

/// Proof that any integer multiplied by 0 results in a product of 0
pub proof fn lemma_mul_by_zero_is_zero_auto()
    ensures
        forall|x: int| #![trigger x * 0] #![trigger 0 * x] x * 0 == 0 && 0 * x == 0,
{
    assert forall|x: int| #![trigger x * 0] #![trigger 0 * x] x * 0 == 0 && 0 * x == 0 by {
        lemma_mul_basics(x);
    }
}

/// Proof that multiplication is associative, specifically that
/// `x * (y * z) == (x * y) * z`.
pub proof fn lemma_mul_is_associative(x: int, y: int, z: int)
    ensures
        x * (y * z) == (x * y) * z,
{
    MulINL::lemma_mul_is_associative(x, y, z);
}

/// Proof that multiplication is associative
pub proof fn lemma_mul_is_associative_auto()
    ensures
        forall|x: int, y: int, z: int|
            #![trigger x * (y * z)]
            #![trigger (x * y) * z]
            (x * (y * z)) == ((x * y) * z),
{
    assert forall|x: int, y: int, z: int|
        #![trigger x * (y * z)]
        #![trigger (x * y) * z]
        (x * (y * z)) == ((x * y) * z) by {
        lemma_mul_is_associative(x, y, z);
    }
}

/// Proof that multiplication is commutative, specifically that
/// `x * y == y * x`.
pub proof fn lemma_mul_is_commutative(x: int, y: int)
    ensures
        x * y == y * x,
{
}

/// Proof that multiplication is commutative
pub proof fn lemma_mul_is_commutative_auto()
    ensures
        forall|x: int, y: int| #[trigger] (x * y) == (y * x),
{
}

/// Proof that, since the product of the two integers `x` and `y` is
/// nonnegative, that product is greater than or equal to each of `x`
/// and `y`
pub proof fn lemma_mul_ordering(x: int, y: int)
    requires
        x != 0,
        y != 0,
        0 <= x * y,
    ensures
        x * y >= x && x * y >= y,
{
    MulINL::lemma_mul_ordering(x, y);
}

/// Proof that if the product of two integers is nonnegative, then
/// that product is greater than or equal to each of the two integers
proof fn lemma_mul_ordering_auto()
    ensures
        forall|x: int, y: int|
            (0 != x && 0 != y && #[trigger] (x * y) >= 0) ==> x * y >= x && (x * y) >= y,
{
    assert forall|x: int, y: int| 0 != x && 0 != y && x * y >= 0 implies #[trigger] (x * y) >= x
        && #[trigger] (x * y) >= y by {
        lemma_mul_ordering(x, y);
    };
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
pub proof fn lemma_mul_inequality(x: int, y: int, z: int)
    requires
        x <= y,
        z >= 0,
    ensures
        x * z <= y * z,
{
    lemma_mul_induction_auto(z, |u: int| u >= 0 ==> x * u <= y * u);
}

/// Proof that any two integers, when each multiplied by a positive
/// number, will maintain their numerical order
pub proof fn lemma_mul_inequality_auto()
    ensures
        forall|x: int, y: int, z: int|
            x <= y && z >= 0 ==> #[trigger] (x * z) <= #[trigger] (y * z),
{
    assert forall|x: int, y: int, z: int| x <= y && z >= 0 implies #[trigger] (x * z)
        <= #[trigger] (y * z) by {
        lemma_mul_inequality(x, y, z);
    }
}

/// Proof that since `x < y` and `z > 0`, `x * z < y * z`.
pub proof fn lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires
        x < y,
        z > 0,
    ensures
        x * z < y * z,
{
    MulINL::lemma_mul_strict_inequality(x, y, z);
}

/// Proof that any two distinct integers, when each multiplied by a
/// positive integer, preserves their numerical order
pub proof fn lemma_mul_strict_inequality_auto()
    ensures
        forall|x: int, y: int, z: int| x < y && z > 0 ==> #[trigger] (x * z) < #[trigger] (y * z),
{
    assert forall|x: int, y: int, z: int| x < y && z > 0 implies #[trigger] (x * z) < #[trigger] (y
        * z) by {
        if x < y && z > 0 {
            lemma_mul_strict_inequality(x, y, z);
        }
    }
}

/// Proof that since `x` is bounded above by `xbound` and `y` is
/// bounded above by `ybound`, the product of `x` and `y` is bounded
/// above by the product of the bounds
pub proof fn lemma_mul_upper_bound(x: int, xbound: int, y: int, ybound: int)
    requires
        x <= xbound,
        y <= ybound,
        0 <= x,
        0 <= y,
    ensures
        x * y <= xbound * ybound,
{
    lemma_mul_inequality(x, xbound, y);
    lemma_mul_inequality(y, ybound, xbound);
}

/// Proof that when two integers have upper bounds, their product is
/// bounded above by the product of their upper bounds
pub proof fn lemma_mul_upper_bound_auto()
    ensures
        forall|x: int, xbound: int, y: int, ybound: int|
            x <= xbound && y <= ybound && 0 <= x && 0 <= y ==> #[trigger] (x * y) <= #[trigger] (
            xbound * ybound),
{
    assert forall|x: int, xbound: int, y: int, ybound: int|
        x <= xbound && y <= ybound && 0 <= x && 0 <= y implies #[trigger] (x * y) <= #[trigger] (
    xbound * ybound) by {
        lemma_mul_upper_bound(x, xbound, y, ybound);
    }
}

/// Proof that when `x` has an exclusive upper bound `xbound` and `y`
/// has an exclusive upper bound `ybound`, that the product of `x` and
/// `y` is bounded above by the product of the predecessors of their
/// upper bounds. In other words, `x * y <= (xbound - 1) * (ybound - 1)`.
pub proof fn lemma_mul_strict_upper_bound(x: int, xbound: int, y: int, ybound: int)
    requires
        x < xbound,
        y < ybound,
        0 < x,
        0 < y,
    ensures
        x * y <= (xbound - 1) * (ybound - 1),
{
    lemma_mul_inequality(x, xbound - 1, y);
    lemma_mul_inequality(y, ybound - 1, xbound - 1);
}

/// Proof that when two integers have exclusive upper bounds, their
/// product has, as an upper bound, the product of the predecessors of
/// their upper bounds
pub proof fn lemma_mul_strict_upper_bound_auto()
    ensures
        forall|x: int, xbound: int, y: int, ybound: int|
            x < xbound && y < ybound && 0 < x && 0 < y ==> #[trigger] (x * y) <= #[trigger] ((xbound
                - 1) * (ybound - 1)),
{
    assert forall|x: int, xbound: int, y: int, ybound: int|
        x < xbound && y < ybound && 0 < x && 0 < y implies #[trigger] (x * y) <= #[trigger] ((xbound
        - 1) * (ybound - 1)) by {
        lemma_mul_strict_upper_bound(x, xbound, y, ybound);
    }
}

/// Proof that multiplying the positive integer `x` by respectively
/// `y` and `z` maintains the order of `y` and `z`. Specifically, `y
/// <= z ==> x * y <= x * z` and `y < z ==> x * y < x * z`.
pub proof fn lemma_mul_left_inequality(x: int, y: int, z: int)
    requires
        0 < x,
    ensures
        y <= z ==> x * y <= x * z,
        y < z ==> x * y < x * z,
{
    lemma_mul_induction_auto(x, |u: int| u > 0 ==> y <= z ==> u * y <= u * z);
    lemma_mul_induction_auto(x, |u: int| u > 0 ==> y < z ==> u * y < u * z);
}

/// Proof that, for all `y`, `z`, and positive `x`, multiplying `x` by
/// respectively `y` and `z` maintains the order of `y` and `z`.
/// Specifically, `y <= z ==> x * y <= x * z` and `y < z ==> x * y < x * z`.
pub proof fn lemma_mul_left_inequality_auto()
    ensures
        forall|x: int, y: int, z: int|
            x > 0 ==> (y <= z ==> #[trigger] (x * y) <= #[trigger] (x * z)) && (y < z ==> (x * y)
                < (x * z)),
{
    assert forall|x: int, y: int, z: int| (y <= z || y < z) && 0 < x implies (y <= z
        ==> #[trigger] (x * y) <= #[trigger] (x * z)) && (y < z ==> (x * y) < (x * z)) by {
        lemma_mul_left_inequality(x, y, z);
    }
}

/// Proof that if `x` and `y` have equal results when multiplied by
/// nonzero `m`, then they're equal
pub proof fn lemma_mul_equality_converse(m: int, x: int, y: int)
    requires
        m != 0,
        m * x == m * y,
    ensures
        x == y,
{
    lemma_mul_induction_auto(m, |u| x > y && 0 < u ==> x * u > y * u);
    lemma_mul_induction_auto(m, |u: int| x < y && 0 < u ==> x * u < y * u);
    lemma_mul_induction_auto(m, |u: int| x > y && 0 > u ==> x * u < y * u);
    lemma_mul_induction_auto(m, |u: int| x < y && 0 > u ==> x * u > y * u);
}

/// Proof that if any two integers are each multiplied by a common
/// nonzero integer and the products are equal, the two original
/// integers are equal
pub proof fn lemma_mul_equality_converse_auto()
    ensures
        forall|m: int, x: int, y: int|
            (m != 0 && #[trigger] (m * x) == #[trigger] (m * y)) ==> x == y,
{
    assert forall|m: int, x: int, y: int|
        m != 0 && #[trigger] (m * x) == #[trigger] (m * y) implies x == y by {
        lemma_mul_equality_converse(m, x, y);
    }
}

/// Proof that since `x * z <= y * z` and `z > 0`, that `x <= y`
pub proof fn lemma_mul_inequality_converse(x: int, y: int, z: int)
    requires
        x * z <= y * z,
        z > 0,
    ensures
        x <= y,
{
    lemma_mul_induction_auto(z, |u: int| x * u <= y * u && u > 0 ==> x <= y);
}

/// Proof that whenever two integers have a less-than-or-equal
/// relationship to each other when multiplied by a positive integer,
/// they have that relationship themselves.
pub proof fn lemma_mul_inequality_converse_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * z) <= #[trigger] (y * z) && z > 0 ==> x <= y,
{
    assert forall|x: int, y: int, z: int| #[trigger]
        (x * z) <= #[trigger] (y * z) && z > 0 implies x <= y by {
        lemma_mul_inequality_converse(x, y, z);
    }
}

/// Proof that since `x * z < y * z` and `z >= 0`, we know `x < y`
pub proof fn lemma_mul_strict_inequality_converse(x: int, y: int, z: int)
    requires
        x * z < y * z,
        z >= 0,
    ensures
        x < y,
{
    lemma_mul_induction_auto(z, |u: int| x * u < y * u && u >= 0 ==> x < y);
}

/// Proof that whenever two integers have a less-than relationship to
/// each other when multiplied by a nonnegative integer, they have
/// that relationship themselves
pub proof fn lemma_mul_strict_inequality_converse_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * z) < #[trigger] (y * z) && z >= 0 ==> x < y,
{
    assert forall|x: int, y: int, z: int| #[trigger]
        (x * z) < #[trigger] (y * z) && z >= 0 implies x < y by {
        lemma_mul_strict_inequality_converse(x, y, z);
    }
}

/// Proof that multiplication distributes over addition, specifically that
/// `x * (y + z) == x * y + x * z`
pub proof fn lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures
        x * (y + z) == x * y + x * z,
{
    MulINL::lemma_mul_is_distributive_add(x, y, z);
}

/// Proof that multiplication distributes over addition
pub proof fn lemma_mul_is_distributive_add_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * (y + z)) == x * y + x * z,
{
    assert forall|x: int, y: int, z: int| #[trigger] (x * (y + z)) == x * y + x * z by {
        lemma_mul_is_distributive_add(x, y, z);
    }
}

/// Proof that multiplication distributes over addition, specifically that
/// `(y + z) * x == y * x + z * x`
pub proof fn lemma_mul_is_distributive_add_other_way(x: int, y: int, z: int)
    ensures
        (y + z) * x == y * x + z * x,
{
    lemma_mul_auto();
}

/// Proof that multiplication distributes over addition when the
/// addition happens in the multiplicand (i.e., in the left-hand
/// argument to `*`)
proof fn lemma_mul_is_distributive_add_other_way_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] ((y + z) * x) == y * x + z * x,
{
    assert forall|x: int, y: int, z: int| #[trigger] ((y + z) * x) == y * x + z * x by {
        lemma_mul_is_distributive_add_other_way(x, y, z);
    }
}

/// Proof that multiplication distributes over subtraction, specifically that
/// `x * (y - z) == x * y - x * z`
pub proof fn lemma_mul_is_distributive_sub(x: int, y: int, z: int)
    ensures
        x * (y - z) == x * y - x * z,
{
    lemma_mul_auto();
}

/// Proof that multiplication distributes over subtraction
pub proof fn lemma_mul_is_distributive_sub_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z,
{
    assert forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z by {
        lemma_mul_is_distributive_sub(x, y, z);
    }
}

/// Proof that multiplication distributes over subtraction when the
/// subtraction happens in the multiplicand (i.e., in the left-hand
/// argument to `*`). Specifically, `(y - z) * x == y * x - z * x`.
pub proof fn lemma_mul_is_distributive_sub_other_way(x: int, y: int, z: int)
    ensures
        (y - z) * x == y * x - z * x,
{
    lemma_mul_is_distributive_sub(x, y, z);
    lemma_mul_is_commutative(x, y - z);
    lemma_mul_is_commutative(x, y);
    lemma_mul_is_commutative(x, z);
}

/// Proof that multiplication distributes over subtraction when the
/// subtraction happens in the multiplicand (i.e., in the left-hand
/// argument to `*`)
pub proof fn lemma_mul_is_distributive_sub_other_way_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] ((y - z) * x) == y * x - z * x,
{
    assert forall|x: int, y: int, z: int| #[trigger] ((y - z) * x) == y * x - z * x by {
        lemma_mul_is_distributive_sub_other_way(x, y, z)
    }
}

/// Proof that multiplication is commutative, distributes over
/// addition, and distributes over subtraction, in the specific cases
/// where one of the arguments to the multiplication is `x` and the
/// other arguments are `y` and `z`
pub proof fn lemma_mul_is_distributive(x: int, y: int, z: int)
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
    lemma_mul_auto();
}

/// Proof that multiplication distributes over addition and
/// subtraction, whether the addition or subtraction happens in the
/// first or the second argument to the multiplication
pub proof fn lemma_mul_is_distributive_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * (y + z)) == x * y + x * z,
        forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z,
        forall|x: int, y: int, z: int| #[trigger] ((y + z) * x) == y * x + z * x,
        forall|x: int, y: int, z: int| #[trigger] ((y - z) * x) == y * x - z * x,
{
    lemma_mul_is_distributive_add_auto();
    lemma_mul_is_distributive_sub_auto();
    lemma_mul_is_commutative_auto();
}

/// Proof that if `x` and `y` are both positive, then their product is
/// also positive
pub proof fn lemma_mul_strictly_positive(x: int, y: int)
    ensures
        (0 < x && 0 < y) ==> (0 < x * y),
{
    MulINL::lemma_mul_strictly_positive(x, y);
}

/// Proof that multiplying any two positive integers will result in a
/// positive integer
pub proof fn lemma_mul_strictly_positive_auto()
    ensures
        forall|x: int, y: int| (0 < x && 0 < y) ==> (0 < #[trigger] (x * y)),
{
    assert forall|x: int, y: int| 0 < x && 0 < y implies 0 < #[trigger] (x * y) by {
        lemma_mul_strictly_positive(x, y);
    }
}

/// Proof that since `x > 1` and `y > 0`, `y < x * y`
pub proof fn lemma_mul_strictly_increases(x: int, y: int)
    requires
        1 < x,
        0 < y,
    ensures
        y < x * y,
{
    lemma_mul_induction_auto(x, |u: int| 1 < u ==> y < u * y);
}

/// Proof that multiplying any positive integer by any integer greater
/// than 1 will result in a product that is greater than the original
/// integer
pub proof fn lemma_mul_strictly_increases_auto()
    ensures
        forall|x: int, y: int| 1 < x && 0 < y ==> y < #[trigger] (x * y),
{
    assert forall|x: int, y: int| 1 < x && 0 < y implies y < #[trigger] (x * y) by {
        lemma_mul_strictly_increases(x, y);
    }
}

/// Proof that since `x` and `y` are both positive, their product is
/// greater than or equal to `y`
pub proof fn lemma_mul_increases(x: int, y: int)
    requires
        0 < x,
        0 < y,
    ensures
        y <= x * y,
{
    lemma_mul_induction_auto(x, |u: int| 0 < u ==> y <= u * y);
}

/// Proof that multiplying any two positive integers will result in a
/// product that is greater than or equal to each original integer
pub proof fn lemma_mul_increases_auto()
    ensures
        forall|x: int, y: int| (0 < x && 0 < y) ==> (y <= #[trigger] (x * y)),
{
    assert forall|x: int, y: int| (0 < x && 0 < y) implies (y <= #[trigger] (x * y)) by {
        lemma_mul_increases(x, y);
    }
}

/// Proof that since `x` and `y` are non-negative, their product is
/// non-negative
pub proof fn lemma_mul_nonnegative(x: int, y: int)
    requires
        0 <= x,
        0 <= y,
    ensures
        0 <= x * y,
{
    lemma_mul_induction_auto(x, |u: int| 0 <= u ==> 0 <= u * y);
}

/// Proof that multiplying any two non-negative integers produces a
/// non-negative integer
pub proof fn lemma_mul_nonnegative_auto()
    ensures
        forall|x: int, y: int| 0 <= x && 0 <= y ==> 0 <= #[trigger] (x * y),
{
    assert forall|x: int, y: int| 0 <= x && 0 <= y implies 0 <= #[trigger] (x * y) by {
        lemma_mul_nonnegative(x, y);
    }
}

/// Proof that negating `x` or `y` before multiplying them together
/// produces the negation of the product of `x` and `y`
pub proof fn lemma_mul_unary_negation(x: int, y: int)
    ensures
        (-x) * y == -(x * y) == x * (-y),
{
    lemma_mul_induction_auto(x, |u: int| (-u) * y == -(u * y) == u * (-y));
}

/// Proof that negating one of two integers before multiplying them
/// together produces the negation of their product
pub proof fn lemma_mul_unary_negation_auto()
    ensures
        forall|x: int, y: int|
            #![trigger (-x) * y]
            #![trigger x * (-y)]
            ((-x) * y) == (-(x * y)) == x * (-y),
{
    assert forall|x: int, y: int|
        #![trigger (-x) * y]
        #![trigger x * (-y)]
        ((-x) * y) == (-(x * y)) == x * (-y) by {
        lemma_mul_unary_negation(x, y);
    }
}

/// Proof that multiplying `-x` and `-y` produces the same product as
/// multiplying `x` and `y`
pub proof fn lemma_mul_cancels_negatives(x: int, y: int)
    ensures
        x * y == (-x) * (-y),
{
    lemma_mul_induction_auto(x, |u: int| (-u) * y == -(u * y) == u * (-y));
}

/// Proof that for any two integers `x` and `y`, multiplying `-x` and
/// `-y` produces the same product as multiplying `x` and `y`
pub proof fn lemma_mul_cancels_negatives_auto()
    ensures
        forall|x: int, y: int| #[trigger] (x * y) == (-x) * (-y),
{
    assert forall|x: int, y: int| #[trigger] (x * y) == (-x) * (-y) by {
        lemma_mul_cancels_negatives(x, y);
    }
}

/// Proof establishing many useful properties of negation
pub proof fn lemma_mul_properties()
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
    lemma_mul_strict_inequality_auto();
    lemma_mul_inequality_auto();
    lemma_mul_is_distributive_auto();
    lemma_mul_is_associative_auto();
    lemma_mul_ordering_auto();
    lemma_mul_nonzero_auto();
    lemma_mul_nonnegative_auto();
    lemma_mul_strictly_increases_auto();
    lemma_mul_increases_auto();
}

} // verus!
