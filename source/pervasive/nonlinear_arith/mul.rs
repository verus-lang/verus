//! Lemma for multiplication

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::calc_macro::*;

verus! {

use crate::nonlinear_arith::internals::mul_internals_nonlinear as MulINL;

use crate::nonlinear_arith::internals::mul_internals::*;

#[allow(unused_imports)]
use crate::nonlinear_arith::internals::general_internals::is_le;

/// The built-in syntax of multiplication results in the same product as multiplication
/// through recursive addition
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_is_mul_recursive(x: int, y: int)
    ensures (x * y) == mul_recursive(x, y)
{
    if (x >= 0) { 
        lemma_mul_is_mul_pos(x, y);
        assert (x * y == mul_pos(x, y));
        assert((x * y) == mul_recursive(x, y));
    }
    else { 
        lemma_mul_is_mul_pos(-x, y);
        assert (x * y == -1 * (-x * y)) by { lemma_mul_is_associative(-1, -x, y) }; // OBSERVE
        assert((x * y) == mul_recursive(x, y));
    }
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mul_is_mul_recursive_auto()
    ensures forall |x: int, y: int| x * y == mul_recursive(x, y)
{
    assert forall |x: int, y: int| x * y == mul_recursive(x, y) by { 
        lemma_mul_is_mul_recursive(x, y) };
}

/// the built-in syntax of multiplying two positive integers results in the same product as 
/// MulPos, which is achieved by recursive addition
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_is_mul_pos(x: int, y: int)
    requires x >= 0
    ensures x * y == mul_pos(x, y)
{
    reveal(mul_pos);
    lemma_mul_induction_auto(x, |u: int| u >= 0 ==> u * y == mul_pos(u, y));
}

/// ensures that the basic properties of multiplication, including the identity and zero properties
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_basics(x: int)
    ensures 
        0 * x == 0,
        x * 0 == 0,
        x * 1 == x,
        1 * x == x,
{}

// #[verifier::spinoff_prover]
pub proof fn lemma_mul_basics_auto()
    ensures 
        forall |x: int| #[trigger](0 * x) == 0,
        forall |x: int| #[trigger](x * 0) == 0,
        forall |x: int| #[trigger](1 * x) == x,
        forall |x: int| #[trigger](x * 1)  == x,
{}

/// multiplying two nonzero integers will never result in 0 as the poduct
/// (i.e. property of int is an integral domain)
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_nonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
{
    MulINL::lemma_mul_nonzero(x, y);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mul_nonzero_auto()
    ensures forall |x: int, y: int| #[trigger] (x * y) != 0 <==> x != 0 && y != 0
{
    assert forall |x: int, y: int|
        #[trigger](x * y) != 0 <==> x != 0 && y != 0 by
    {
    lemma_mul_nonzero(x, y);
    }
}

/// any integer multiplied by 0 results in a product of 0
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_by_zero_is_zero_auto()
    ensures forall |x: int| (#[trigger](x * 0) == 0 && #[trigger](0 * x) == 0)
{
    assert forall |x: int| 
    #[trigger](x * 0) == 0 && #[trigger](0 * x) == 0 by
    {
    lemma_mul_basics(x);
    }
}

/// multiplication is associative
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_is_associative(x: int, y: int, z: int)
    ensures x * (y * z) == (x * y) * z
{
    MulINL::lemma_mul_is_associative(x, y, z);
}

/// multiplication is always associative for all integers
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_is_associative_auto()
    ensures forall |x: int, y: int, z: int| 
        #[trigger](x * (y * z)) == #[trigger]((x * y) * z)
{
    assert forall |x: int, y: int, z: int| 
        #[trigger](x * (y * z)) == #[trigger]((x * y) * z) by 
    {
        lemma_mul_is_associative(x, y, z);
    }
}

/// multiplication is commutative
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_is_commutative(x: int, y: int)
    ensures x * y == y * x
{}

/// multiplication is always commutative for all integers
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_is_commutative_auto()
    ensures forall |x: int, y: int| #[trigger](x * y) == (y * x)
{}

/// the product of two integers is greater than the value of each individual integer
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_ordering(x: int, y: int)
    requires 
        x != 0,
        y != 0,
        0 <= x * y,
    ensures 
        x * y >= x && x * y >= y
{
    MulINL::lemma_mul_ordering(x, y);
}

/// the product of two positive integers is always greater than the individual value of either 
/// multiplied integer
// #[verifier::spinoff_prover]
proof fn lemma_mul_ordering_auto()
    ensures forall |x: int, y: int| (0 != x && 0 != y && #[trigger] (x * y) >= 0) 
        ==> x * y >= x && #[trigger] (x * y) >= y,
{
    assert forall |x: int, y: int| 0 != x && 0 != y && x * y >= 0 
        implies #[trigger](x * y) >= x && #[trigger](x * y) >= y
    by 
    {
        lemma_mul_ordering(x, y);
    };
}

/// If two integers `x` and `y` are equal, then their products with
/// any integer `z` are also equal.
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_equality(x: int, y: int, z: int)
    requires x == y
    ensures x * z == y * z
{}

// #[verifier::spinoff_prover]
pub proof fn lemma_mul_equality_auto()
    ensures forall |x: int, y: int, z: int| x == y ==> #[trigger](x * z) == #[trigger](y * z)
{
    assert forall |x: int, y: int, z: int| 
        x == y implies #[trigger](x * z) == #[trigger](y * z)
    by
    { lemma_mul_equality(x, y, z); } 
}

/// two integers that are multiplied by a positive number will maintain their numerical order
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_inequality(x: int, y: int, z: int)
    requires 
        x <= y,
        z >= 0
    ensures  x * z <= y * z
{
    lemma_mul_induction_auto(z, |u: int| u >= 0 ==> x * u <= y * u);
}

/// any two integers that are multiplied by a positive number will maintain their numerical order
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_inequality_auto()
    ensures forall |x: int, y: int, z: int| x <= y && z >= 0 ==> #[trigger](x * z) <= #[trigger](y * z)
{
    assert forall |x: int, y: int, z: int| x <= y && z >= 0 
        implies #[trigger](x * z) <= #[trigger](y * z) by
    {
        lemma_mul_inequality(x, y, z);
    }
}

/// multiplying by a positive integer preserves inequality
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires 
        x < y,
        z > 0
    ensures 
        x * z < y * z
{
    MulINL::lemma_mul_strict_inequality(x, y, z);
}

/// multiplying by a positive integer preserves inequality for all integers
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_strict_inequality_auto()
    ensures  forall |x: int, y: int, z: int| x < y && z > 0 ==> #[trigger](x * z) < #[trigger](y * z)
{
    assert forall |x: int, y: int, z: int | x < y && z > 0 
        implies #[trigger](x * z) < #[trigger](y * z)
    by
    {
        if x < y && z > 0 { lemma_mul_strict_inequality(x, y, z); }
    }
}

/// the product of two bounded integers is less than or equal to the product of their upper bounds
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_upper_bound(x: int, xbound: int, y: int, ybound: int)
    requires 
        x <= xbound,
        y <= ybound,
        0 <= x,
        0 <= y
    ensures 
        x * y <= xbound * ybound
{
    lemma_mul_inequality(x, xbound, y);
    lemma_mul_inequality(y, ybound, xbound);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mul_upper_bound_auto()
    ensures forall |x: int, xbound: int, y: int, ybound: int|
    x <= xbound && y <= ybound && 0 <= x && 0 <= y ==> #[trigger](x * y) <= #[trigger](xbound * ybound),
{
    assert forall |x: int, xbound: int, y: int, ybound: int| 
        x <= xbound && y <= ybound && 0 <= x && 0 <= y implies
        #[trigger](x * y) <= #[trigger](xbound * ybound)
    by
    {
        lemma_mul_upper_bound(x, xbound, y, ybound);
    }
}

/// the product of two strictly upper bounded integers is less than the product of their upper bounds */
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_strict_upper_bound(x: int, xbound: int, y: int, ybound: int)
    requires 
        x < xbound,
        y < ybound,
        0 < x,
        0 < y
    ensures 
    x * y <= (xbound - 1) * (ybound - 1)
{
    lemma_mul_inequality(x, xbound - 1, y);
    lemma_mul_inequality(y, ybound - 1, xbound - 1);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mul_strict_upper_bound_auto()
    ensures forall |x: int, xbound: int, y: int, ybound: int| x < xbound && y < ybound && 0 < x && 0 < y ==> #[trigger](x * y) <= #[trigger]((xbound - 1) * (ybound - 1))
{
    assert forall |x: int, xbound: int, y: int, ybound: int | x < xbound && y < ybound && 0 < x && 0 < y 
        implies #[trigger](x * y) <= #[trigger]((xbound - 1) * (ybound - 1))
    by
    {
        lemma_mul_strict_upper_bound(x, xbound, y, ybound);
    }
}

/// any two integers that are multiplied by a positive number will maintain their numerical order
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_left_inequality(x: int, y: int, z: int)
    requires 0 < x
    ensures 
        y <= z ==> x * y <= x * z,
        y < z ==> x * y < x * z
{
    lemma_mul_induction_auto(x, |u: int| u > 0 ==> y <= z ==> u * y <= u * z);
    lemma_mul_induction_auto(x, |u: int| u > 0 ==> y < z ==> u * y < u * z);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mul_left_inequality_auto()
    ensures forall |x: int, y: int, z: int| x > 0 ==> (y <= z ==> #[trigger](x * y) <= #[trigger](x * z)) && (y < z ==> #[trigger](x * y) < #[trigger](x * z))
{
    assert forall |x: int, y: int, z: int | (y <= z || y < z) && 0 < x 
        implies (y <= z ==> #[trigger](x * y) <= #[trigger](x * z)) && (y < z ==> #[trigger](x * y) < #[trigger](x * z)) by
    {
        lemma_mul_left_inequality(x, y, z);
    }
}

/// if two seperate integers are each multiplied by a common integer and the products are equal, the 
/// two original integers are equal
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_equality_converse(m: int, x: int, y: int)
    requires 
        m != 0,
        m * x == m * y
    ensures 
        x == y
{
        lemma_mul_induction_auto(m, |u| x > y && 0 < u ==> x * u > y * u);
        lemma_mul_induction_auto(m, |u: int| x < y && 0 < u ==> x * u < y * u);
        lemma_mul_induction_auto(m, |u: int| x > y && 0 > u ==> x * u < y * u);
        lemma_mul_induction_auto(m, |u: int| x < y && 0 > u ==> x * u > y * u);
}

/// if any two seperate integers are each multiplied by a common integer and the products are equal, the 
/// two original integers are equal
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_equality_converse_auto()
    ensures forall |m: int, x: int, y: int| (m != 0 && #[trigger](m * x) == #[trigger](m * y)) ==> x == y,
{
    assert forall |m: int, x: int, y: int | m != 0 && #[trigger](m * x) == #[trigger](m * y) 
        implies x == y by
    {
        lemma_mul_equality_converse(m, x, y);
    }
}

/// when two integers, x and y, are each multiplied by a positive integer, z, if x <= z then the x*z <= y*z
pub proof fn lemma_mul_inequality_converse(x: int, y: int, z: int)
    requires 
        x * z <= y * z,
        z > 0
    ensures  x <= y
{
    lemma_mul_induction_auto(z, |u: int| x * u <= y * u && u > 0 ==> x <= y);
}

/// when two integers, x and y, are each multiplied by a positive integer, z, if x <= z then the x*z <= y*z 
/// for all valid values of x, y, and z
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_inequality_converse_auto()
    ensures forall |x: int, y: int, z: int| #[trigger](x * z) <= #[trigger](y * z) && z > 0 ==> x <= y,
{
    assert forall |x: int, y: int, z: int | #[trigger](x * z) <= #[trigger](y * z) && z > 0 implies x <= y
    by
    {
        lemma_mul_inequality_converse(x, y, z);
    }
}

/// when two integers, x and y, are each multiplied by a positive integer, z, if x < z then the x*z < y*z
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_strict_inequality_converse(x: int, y: int, z: int)
    requires 
        x * z < y * z,
        z >= 0
    ensures
        x < y
{
    lemma_mul_induction_auto(z, |u: int| x * u < y * u && u >= 0 ==> x < y);
}

/// when two integers, x and y, are each multiplied by a positive integer, z, if x < z then the x*z < y*z 
/// for all valid values of x, y, and z
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_strict_inequality_converse_auto()
    ensures  forall |x: int, y: int, z: int| #[trigger](x * z) < #[trigger](y * z) && z >= 0 ==> x < y,
{
    assert forall |x: int, y: int, z: int | #[trigger](x * z) < #[trigger](y * z) && z >= 0
        implies x < y by
    {
       lemma_mul_strict_inequality_converse(x, y, z);
    }
}

/// multiplication is distributive
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
{
    MulINL::lemma_mul_is_distributive_add(x, y, z);
}

/// for all integers, multiplication is distributive with addition in the form x * (y + z)
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_is_distributive_add_auto()
    ensures forall |x: int, y: int, z: int| #[trigger](x * (y + z)) == x * y + x * z,
{
    assert forall |x: int, y: int, z: int|
        #[trigger](x * (y + z)) == x * y + x * z by
    {
        lemma_mul_is_distributive_add(x, y, z);
    }
}

/// for all integers, multiplication is distributive with addition in the form (y + z) * x
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_is_distributive_add_other_way(x: int, y: int, z: int)
    ensures (y + z) * x == y * x + z * x
{
    lemma_mul_auto();
}

// #[verifier::spinoff_prover]
proof fn lemma_mul_is_distributive_add_other_way_auto()
    ensures forall |x: int, y: int, z: int| #[trigger]((y + z) * x) == y * x + z * x,
{
    assert forall |x: int, y: int, z: int| 
        #[trigger]((y + z) * x) == y * x + z * x by
    {
        lemma_mul_is_distributive_add_other_way(x, y, z);
    }
}

/// multiplication is distributive with subtraction
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_is_distributive_sub(x: int, y: int, z: int)
    ensures x * (y - z) == x * y - x * z
{
    lemma_mul_auto();
}

/// for all integers, multiplication is distributive with subtraction
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_is_distributive_sub_auto()
    ensures forall |x: int, y: int, z: int| #[trigger](x * (y - z)) == x * y - x * z,
{
    assert forall |x: int, y: int, z: int| 
        #[trigger](x * (y - z)) == x * y - x * z by
    {
        lemma_mul_is_distributive_sub(x, y, z);
    }
}

/// proves the overall distributive nature of multiplication
// #[verifier::spinoff_prover]
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

/// for all integers, multiplication is distributive
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_is_distributive_auto()
    ensures
        forall |x: int, y: int, z: int| #[trigger](x * (y + z)) == x * y + x * z,
        forall |x: int, y: int, z: int| #[trigger](x * (y - z)) == x * y - x * z,
        forall |x: int, y: int, z: int| #[trigger]((y + z) * x) == y * x + z * x,
        forall |x: int, y: int, z: int| #[trigger]((y - z) * x) == y * x - z * x,
{
    lemma_mul_is_distributive_add_auto();
    lemma_mul_is_distributive_sub_auto();
    lemma_mul_is_commutative_auto();
}

/// multiplying two positive integers will result in a positive integer
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_strictly_positive(x: int, y: int)
    ensures (0 < x && 0 < y) ==> (0 < x * y)
{
    MulINL::lemma_mul_strictly_positive(x, y);
}

/// multiplying any two positive integers will result in a positive integer
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_strictly_positive_auto()
    ensures forall |x: int, y: int| (0 < x && 0 < y) ==> (0 < #[trigger](x * y)),
{
    assert forall |x: int, y: int| 0 < x && 0 < y implies 0 < #[trigger](x * y) by
    {
        lemma_mul_strictly_positive(x, y);
    }
}

/// multiplying a positive integer by an integer greater than 1 will result in a product that 
/// is greater than the original integer
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_strictly_increases(x: int, y: int)
    requires 
        1 < x,
        0 < y,
    ensures 
        y < x * y
{
    lemma_mul_induction_auto(x, |u: int| 1 < u ==> y < u * y);
}

/// multiplying any positive integer by any integer greater than 1 will result in a product that 
/// is greater than the original integer
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_strictly_increases_auto()
    ensures forall |x: int, y: int| 1 < x && 0 < y  ==> y < #[trigger](x * y)
{
    assert forall |x: int, y: int| 1 < x && 0 < y implies y < #[trigger](x * y) by
    {
       lemma_mul_strictly_increases(x, y);
    }
}

/// multiplying an integer by a positive integer will result in a product that is greater than or
/// equal to the original integer
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_increases(x: int, y: int)
    requires 
        0 < x,
        0 < y
    ensures 
        y <= x * y
{
    lemma_mul_induction_auto(x, |u: int| 0 < u ==> y <= u * y);
}

/// multiplying any integer by any positive integer will result in a product that is greater than or
/// equal to the original integer
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_increases_auto()
    ensures forall |x: int, y: int| (0 < x && 0 < y) ==> (y <= #[trigger](x * y))
{
    assert forall |x: int, y: int| (0 < x && 0 < y) 
        implies (y <= #[trigger](x * y)) by 
    {
        lemma_mul_increases(x, y);
    }
}

/// multiplying two positive numbers will result in a positive product
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_nonnegative(x: int, y: int)
    requires 
        0 <= x,
        0 <= y
    ensures  0 <= x * y
{
    lemma_mul_induction_auto(x, |u: int| 0 <= u ==> 0 <= u * y);
}

/// multiplying any two positive numbers will result in a positive product
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_nonnegative_auto()
    ensures forall |x: int, y: int| 0 <= x && 0 <= y ==> 0 <= #[trigger](x * y)
{
    assert forall |x: int, y: int| 0 <= x && 0 <= y implies 0 <= #[trigger](x * y) by
    {
        lemma_mul_nonnegative(x, y);
    }
}

/// shows the equivalent forms of using the unary negation operator
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_unary_negation(x: int, y: int)
    ensures 
        (-x) * y == -(x * y) == x * (-y)
{
    lemma_mul_induction_auto(x, |u: int| (-u) * y == - (u * y) == u * (-y));
}

/// shows the equivalent forms of using the unary negation operator for any integers
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_unary_negation_auto()
    ensures forall |x: int, y: int| #[trigger]((-x) * y) ==  #[trigger](-(x * y)) == x * (-y),
{
    assert forall |x: int, y: int| #[trigger]((-x) * y) ==  #[trigger](-(x * y)) == x * (-y) by
    {
        lemma_mul_unary_negation(x, y);
    }
}

/// multiplying two negative integers, -x and -y, is equivalent to multiplying x and y
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_cancels_negatives(x: int, y: int)
    ensures x * y == (-x) * (-y)
{
    lemma_mul_induction_auto(x, |u: int| (-u) * y == - (u * y) == u * (-y));
}

/// multiplying two negative integers, -x and -y, is equivalent to multiplying x and y
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_cancels_negatives_auto()
    ensures forall |x: int, y: int| #[trigger](x * y) == (-x) * (-y)
{
    assert forall |x: int, y: int| #[trigger](x * y) == (-x) * (-y) by
    {
        lemma_mul_cancels_negatives(x, y);
    }
}

/// includes all properties of multiplication
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_properties()
    ensures 
    forall |x: int, y: int| #[trigger](x * y) == y * x,
    forall |x: int| #[trigger](x * 1) == x && #[trigger](1 * x) == x,
    forall |x: int, y: int, z: int| x < y && z > 0 ==>  #[trigger](x * z) < #[trigger](y * z),
    forall |x: int, y: int, z: int| x <= y && z >= 0 ==> #[trigger](x * z) <= #[trigger](y * z),
    forall |x: int, y: int, z: int| #[trigger](x * (y + z)) == x * y + x * z,
    forall |x: int, y: int, z: int| #[trigger](x * (y - z)) == x * y - x * z,
    forall |x: int, y: int, z: int| #[trigger]((y + z) * x) == y * x + z * x,
    forall |x: int, y: int, z: int| #[trigger]((y - z) * x) == y * x - z * x,
    forall |x: int, y: int, z: int| #[trigger](x * (y * z)) == #[trigger]((x * y) * z),
    forall |x: int, y: int| #[trigger](x * y) != 0 <==> x != 0 && y != 0,
    forall |x: int, y: int| 0 <= x && 0 <= y ==> 0 <= #[trigger](x * y),
    forall |x: int, y: int| 0 < x && 0 < y && 0 <= x * y ==> x <= #[trigger](x * y) && y <= #[trigger](x * y),
    forall |x: int, y: int| (1 < x && 0 < y) ==> (y < #[trigger](x * y)),
    forall |x: int, y: int| (0 < x && 0 < y) ==> (y <= #[trigger](x * y)),
    forall |x: int, y: int| (0 < x && 0 < y) ==> (0 < #[trigger](x * y)),
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


}