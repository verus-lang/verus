//! Lemmas for division.

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::calc_macro::*;

verus! {

#[allow(unused_imports)]
use crate::nonlinear_arith::internals::div_internals::{div_recursive, lemma_div_induction_auto, div_auto, div_pos, lemma_div_auto};
use crate::nonlinear_arith::internals::div_internals_nonlinear as DivINL;
use crate::nonlinear_arith::internals::mod_internals_nonlinear as ModINL;
use crate::nonlinear_arith::internals::mul_internals::{lemma_mul_auto, lemma_mul_induction};
use crate::nonlinear_arith::mul::*;
use crate::nonlinear_arith::internals::general_internals::{is_le};
use crate::nonlinear_arith::modulus::*;
use crate::nonlinear_arith::math::{add as add1, sub as sub1};


/// Division using `/` is equivalent to division through [`div_recursive`]
// #[verifier::spinoff_prover]
pub proof fn lemma_div_is_div_recursive(x: int, d: int)
    requires 0 < d
    ensures div_recursive(x, d) == x / d
{
    reveal(div_recursive);
    reveal(div_pos);
    lemma_div_induction_auto(d, x, |u: int| div_recursive(u, d) == u / d);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_is_div_recursive_auto()
    ensures forall |x: int, d: int| d > 0 ==> div_recursive(x, d) == #[trigger](x / d)
{
    reveal(div_recursive);
    assert forall |x: int, d: int| d > 0 implies div_recursive(x, d) == #[trigger](x / d) by
    {
        lemma_div_is_div_recursive(x, d);
    }
}

/// The quotient of an integer divided by itself is 1
// #[verifier::spinoff_prover] 
pub proof fn lemma_div_by_self(d: int)
    requires d != 0
    ensures d / d == 1
{
    DivINL::lemma_div_by_self(d);
}

/// Zero divided by an integer besides 0 is 0
// #[verifier::spinoff_prover]
pub proof fn lemma_div_of0(d: int)
    requires d != 0
    ensures 0 as int  / d == 0
{
    DivINL::lemma_div_of0(d);
}

/// Ensures the basic properties of division: 0 divided by any integer is 0; any integer 
/// divided by 1 is itself; any integer divided by itself is 1. 
/// A convenience function to introduce basic properties about division
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
pub proof fn lemma_div_basics_auto()
    ensures
        forall |x: int| x != 0 ==> #[trigger](0int / x) == 0,
        forall |x: int| #[trigger](x / 1) == x,
        forall |x: int, y: int| x >= 0 && y > 0 ==> #[trigger](x / y) >= 0,
        forall |x: int, y: int| x >= 0 && y > 0 ==> #[trigger](x / y) <= x,
{
    assert forall |x: int| (x != 0 ==> #[trigger](0int / x) / x == 0) && (#[trigger](x / 1) == x) by
    {
        lemma_div_basics(x);
    };
    
    assert forall |x: int, y: int| x >= 0 && y > 0 implies 0 <= #[trigger](x / y) <= x by
    {
        lemma_div_pos_is_pos(x, y);
        lemma_div_is_ordered_by_denominator(x, 1, y);
    };
}

/// If a dividend is a whole number and the divisor is a natural number and their
/// quotient is 0, this implies that the dividend is smaller than the divisor
// #[verifier::spinoff_prover]
pub proof fn lemma_small_div_converse_auto()
    ensures forall |x: int, d:int| 0 <= x && 0 < d && #[trigger](x / d) == 0 ==> x < d,
{
    assert forall |x: int, d: int| 0 <= x && 0 < d &&  #[trigger](x / d) == 0 implies x < d by
    {
        lemma_div_induction_auto(d, x, |u: int| 0 <= u && 0 < d && u / d == 0 ==> u < d); 
    }
}

/// Division of a positive integer by a positive integer less than or equal to it is nonzero
// #[verifier::spinoff_prover]
pub proof fn lemma_div_non_zero(x: int, d: int)
    requires x >= d > 0
    ensures x / d > 0
{
    lemma_div_pos_is_pos_auto();
    if x / d == 0 {
        lemma_small_div_converse_auto();
    }
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_non_zero_auto()
    ensures forall |x: int, d: int| x >= d > 0 ==> #[trigger] (x / d) > 0
{
    assert forall |x: int, d: int| x >= d > 0 implies #[trigger] (x / d) > 0 by
    {
        lemma_div_non_zero(x, d);
    }
}

spec fn div (x:int, y: int) -> int
    recommends y != 0
{
    x / y
}

/// Given two fractions with the same numerator, the order of numbers is determined by 
/// the denominators. However, if the numerator is 0, the fractions are equal regardless of 
/// the denominators' values
// #[verifier::spinoff_prover]
pub proof fn lemma_div_is_ordered_by_denominator(x: int, y: int, z: int)
    requires 
        0 <= x,
        1 <= y <= z
    ensures 
        x / y >= x / z
    decreases x
{
    reveal(div_recursive);
    reveal(div_pos);
    lemma_div_is_div_recursive_auto();

    assert(forall |u: int, d: int| d > 0 ==> #[trigger]div_recursive(u, d) == #[trigger](div(u, d)));

    if (x < z)
    {
        lemma_div_is_ordered(0, x, y);
    }
    else
    {
        lemma_div_is_ordered(x - z, x - y, y);
        lemma_div_is_ordered_by_denominator(x - z, y, z);
    }
  
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_is_ordered_by_denominator_auto()
    ensures forall |x: int, y: int, z: int| 0 <= x && 1 <= y <= z ==> #[trigger](x / y) >= #[trigger](x / z)
{
    assert forall |x: int, y: int, z: int| 0 <= x && 1 <= y <= z implies #[trigger](x / y) >= #[trigger](x / z) by
    {
        lemma_div_is_ordered_by_denominator(x, y, z);
    }
}

/// Given two fractions with the same numerator, the order of numbers is strictly determined by 
/// the denominators.
// #[verifier::spinoff_prover]
pub proof fn lemma_div_is_strictly_smaller(x: int, d: int)
    requires 
        0 < x, 
        1 < d
    ensures 
        x / d  < x
    decreases x
{
    lemma_div_induction_auto(d, x, |u: int| 0 < u ==> u / d < u);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_is_strictly_smaller_auto()
    ensures forall |x: int, d: int|  0 < x && 1 < d ==> #[trigger](x / d) < x,
{
    assert forall |x: int, d: int|  0 < x && 1 < d implies #[trigger](x / d) < x by
    {
        lemma_div_is_strictly_smaller(x, d);
    }
}

/// Rounding is different when multiplying the sum of two integers by a fraction d/d vs. 
/// first multiplying each integer by d/d and then adding the quotients
// #[verifier::spinoff_prover]
pub proof fn lemma_dividing_sums(a: int, b: int, d: int, r: int)
    requires 
        0 < d,
        r == a % d + b % d - (a + b) % d,
    ensures 
        d * ((a + b) / d) - r == d * (a / d) + d * (b / d)
{
    ModINL::lemma_fundamental_div_mod(a + b, d);
    ModINL::lemma_fundamental_div_mod(a, d);
    ModINL::lemma_fundamental_div_mod(b, d);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_dividing_sums_auto()
    ensures forall |a: int, b: int, d: int, r: int| 
    #![trigger (d * ((a + b) / d) - r), (d * (a / d) + d * (b / d))] 
    0 < d && r == a % d + b % d - (a + b) % d ==> 
        d * ((a + b) / d) - r == d * (a / d) + d * (b / d),
{
    assert forall |a: int, b: int, d: int, r: int| 
    0 < d && r == a % d + b % d - (a + b) % d implies
        #[trigger](d * ((a + b) / d) - r) == #[trigger](d * (a / d) + d * (b / d)) by
    {
        lemma_dividing_sums(a, b, d, r);
    }
}

/// Dividing a whole number by a natural number will result in a quotient that is 
/// greater than or equal to 0
// #[verifier::spinoff_prover]
pub proof fn lemma_div_pos_is_pos(x: int, d: int)
    requires 
        0 <= x,
        0 < d
    ensures 
        0 <= x / d
{
    lemma_div_auto(d);
    assert(div_auto(d));
    let f = |u: int| 0 <= u ==> u / d >= 0;

    assert forall |i: int| #[trigger]is_le(0, i) && f(i) implies f(i + d) by {
        assert(i / d >= 0);
    };

    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u / d >= 0);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_pos_is_pos_auto()
    ensures
        forall |x: int, d: int|  0 <= x && 0 < d ==> 0 <= #[trigger](x / d)
{
    assert forall |x: int, d: int| 0 <= x && 0 < d implies 0 <= #[trigger] (x / d) by
    {
        lemma_div_pos_is_pos(x, d);
    }
}

/// Dividing an integer and then adding 1 to the quotient is the same as adding 
/// the divisor and the integer, and then dividing that sum by the divisor
// #[verifier::spinoff_prover]
pub proof fn lemma_div_plus_one(x: int, d: int)
    requires 0 < d
    ensures 1 + x / d == (d + x) / d
{
    lemma_div_auto(d);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_plus_one_auto()
    ensures
        forall |x: int, d: int| #![trigger (1 + x / d), ((d + x) / d)] 0 < d ==> 1 + (x / d) == (d + x) / d,
{
    assert forall |x: int, d: int|  0 < d implies  #[trigger](1 + x / d) == #[trigger]((d + x) / d) by
    {
        lemma_div_plus_one(x, d);
    }
}

/// Dividing an integer and then subtracting 1 from the quotient is the same as subtracting 
/// the divisor from the integer, and then dividing that difference by the divisor
// #[verifier::spinoff_prover]
pub proof fn lemma_div_minus_one(x: int, d: int)
    requires 0 < d
    ensures -1 + x / d == (-d + x) / d
{
    lemma_div_auto(d);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_minus_one_auto()
    ensures forall |x: int, d: int| 
        #![trigger (-1 + x / d), ((-d + x) / d)] 
        0 < d ==> -1 + x / d == (-d + x) / d,
{
    assert forall |x: int, d: int|  0 < d implies  #[trigger](-1 + x / d) == #[trigger]((-d + x) / d) by
    {
        lemma_div_minus_one(x, d);
    }
}

/// Dividing a smaller integer by a larger integer results in a quotient of 0
// #[verifier::spinoff_prover]
pub proof fn lemma_basic_div(d: int)
    requires 0 < d
    ensures forall |x: int| 0 <= x < d ==> #[trigger](x / d) == 0
{
    lemma_div_auto(d);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_basic_div_auto()
    ensures forall |x: int, d: int| 0 <= x < d ==> #[trigger](x / d) == 0
{
    assert forall |x: int, d: int| 0 <= x < d implies #[trigger](x / d) == 0 by
    {
        lemma_basic_div(d);
    }
}

/// Numerical order is preserved when dividing two seperate integers by a common positive divisor
// #[verifier::spinoff_prover]
pub proof fn lemma_div_is_ordered(x: int, y: int, z: int)
    requires 
        x <= y,
        0 < z,
    ensures x / z <= y / z
{
    lemma_div_auto(z);
    let f = |xy: int| xy <= 0 ==> (xy + y) / z <= y / z;

    assert forall |i: int| #[trigger]is_le(i + 1, z) && f(i) implies f(i - z) by {
        if (i - z <= 0) {
            assert( f(i) );
            assert( i <= 0 ==> (i + y) / z <= y / z );
            if (i > 0) {
                assert ( z > 0 );
                assert( i <= z );
                assert ( ((i + y) - z) / z <= y / z );
            } else {
                assert( (i + y) / z <= y / z );
            }
            assert( (i - z + y) / z <= y / z );
        }
    };

    lemma_div_induction_auto(z, x - y, |xy: int| xy <= 0 ==> (xy + y) / z <= y / z);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_is_ordered_auto()
    ensures forall |x: int, y: int, z: int| x <= y && 0 < z ==> #[trigger](x / z) <= #[trigger](y / z)
{
    assert forall |x: int, y: int, z: int| x <= y && 0 < z implies #[trigger](x / z) <= #[trigger](y / z) by
    {
        lemma_div_is_ordered(x, y, z);
    }
}

/// Dividing an integer by 2 or more results in a quotient that is smaller than the 
/// original dividend
// #[verifier::spinoff_prover]
pub proof fn lemma_div_decreases(x: int, d: int)
    requires 
        0 < x,
        1 < d,
    ensures 
        x / d  < x
{
    lemma_div_induction_auto(d, x, |u: int| 0 < u ==> u / d < u);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_decreases_auto()
    ensures 
        forall |x: int, d: int| 0 < x && 1 < d ==> #[trigger](x / d) < x,
{
    assert forall |x: int, d: int| 0 < x && 1 < d implies #[trigger](x / d) < x by
    {
        lemma_div_decreases(x, d);
    };
}

/// Dividing an integer by 1 or more results in a quotient that is less than or equal to 
/// the original dividend
// #[verifier::spinoff_prover]
pub proof fn lemma_div_nonincreasing(x: int, d: int)
    requires 
        0 <= x,
        0 < d,
    ensures 
        x / d  <= x
{
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u / d <= u);
}

proof fn lemma_div_nonincreasing_auto()
    ensures forall |x: int, d: int| 0 <= x && 0 < d ==> #[trigger](x / d) <= x,
{
    assert forall |x: int, d: int| 0 <= x && 0 < d implies #[trigger](x / d) <= x by
    {
        lemma_div_nonincreasing(x, d);
    }
}

/// A natural number x divided by a larger natural number gives a remainder equal to x
// #[verifier::spinoff_prover]
pub proof fn lemma_small_mod(x: nat, m: nat)
    requires 
        x < m,
        0 < m
    ensures 
        x % m == x
{
    ModINL::lemma_small_mod(x, m);
}

/// The remainder of a nonnegative integer `x` divided by the product of two positive integers
/// `y` and `z` is equivalent to dividing `x` by `y`, dividing the quotient by `z`, multiplying
/// the remainder by `y`, and then adding the product to the remainder of `x` divided by `y`.
// #[verifier::spinoff_prover]
#[verifier::broadcast_forall]
pub proof fn lemma_breakdown(x: int, y: int, z: int)
    requires 
        0 <= x,
        0 < y,
        0 < z,
    ensures 
        0 < y * z,
        #[trigger] (x % (y * z)) == y * ((x / y) % z) + x % y,
{
    lemma_mul_strictly_positive_auto();
    lemma_div_pos_is_pos(x, y);

    calc! {
        (<)
        (y * (x / y)) % (y * z) + (x % y) % (y * z);
        (<=)    { lemma_part_bound1(x, y, z); }
        y * (z - 1) + (x % y) % (y * z);
        (<)    { lemma_part_bound2(x, y, z); }
        y * (z - 1) + y;
        (==)    { lemma_mul_basics_auto(); }
        y * (z - 1) + y * 1;
        (==)    { lemma_mul_is_distributive_auto(); }
        y * (z - 1 + 1);
        (==) {}
        y * z;
    }

    calc! {
        (==)
        x % (y * z);
        { ModINL::lemma_fundamental_div_mod(x,y); }
        (y * (x / y) + x % y) % (y * z);
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
            // comparison op can't be chained in calc!
            // assert forall is also not avaialable in calc!
            assert((x % y) < y && y <= (y * z)); 
            lemma_small_mod((x % y) as nat, (y * z) as nat);
            assert((x % y) % (y * z) == x % y);
        }
        (y * (x / y)) % (y * z) + x % y;
        { lemma_truncate_middle(x / y, y, z); }
        y * ((x / y) % z) + x % y;
    }
}

/* This function doesn't reliably work due to Z3 instability.
   Fortunately, it's obviated by broadcast_forall. You can now
   get this functionality by doing reveal(lemma_breakdown);
pub proof fn lemma_breakdown_auto()
    ensures 
        forall |x: int, y: int, z: int| 
        #![trigger y * z, x % (y * z), y * ((x / y) % z) + x % y] 
        0 <= x && 0 < y && 0 < z ==> 
        0 < y * z && x % (y * z) == y * ((x / y) % z) + x % y,
{
    assert forall |x: int, y: int, z: int| 
        #![trigger y * z, x % (y * z), y * ((x / y) % z) + x % y] 
        0 <= x && 0 < y && 0 < z implies
        0 < y * z && x % (y * z) == y * ((x / y) % z) + x % y by
    {
        lemma_breakdown(x, y, z);
    }
}
    */

/// The difference between a nonnegative integer `x` and a positive integer `d` must
/// be strictly less than the quotient of `x` divided by `d` and then multiplied by `d`.
// #[verifier::spinoff_prover]
pub proof fn lemma_remainder_upper(x: int, d: int)
    requires 
        0 <= x,
        0 < d,
    ensures 
        x - d < x / d * d
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u - d < u / d * d);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_remainder_upper_auto()
    ensures forall |x: int, d: int| #![trigger (x - d), (x / d * d)] 0 <= x && 0 < d ==> (x - d) < (x / d * d)
{
    assert forall |x: int, d: int| 0 <= x && 0 < d implies #[trigger](x - d) < #[trigger](x / d * d) by
    {
        lemma_remainder_upper(x, d);
    }
}

/// The division of a nonnegative integer `x` by a positive integer `d` multiplied by `d`
/// is less than or equal to the value of `x`.
// #[verifier::spinoff_prover]
pub proof fn lemma_remainder_lower(x: int, d: int)
    requires 
        0 <= x,
        0 < d
    ensures
        x >= x / d * d
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u >= u / d * d);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_remainder_lower_auto()
    ensures
        forall |x: int, d: int| 0 <= x && 0 < d ==> x >= #[trigger](x / d * d)
{
    assert forall |x: int, d: int| (0 <= x && 0 < d) implies x >= #[trigger](x / d * d) by
    {
        lemma_remainder_lower(x, d);
    }
}

/// The difference between a nonnegative integer `x` and the division of `x` by a positive integer `d` multiplied by `d`
/// is lower bounded (inclusively) by 0 and upper bounded (exclusively) by `d`.
// #[verifier::spinoff_prover]
pub proof fn lemma_remainder(x: int, d: int)
    requires 
        0 <= x,
        0 < d,
    ensures
        0 <= x - (x / d * d) < d
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x,|u: int| 0 <= u - u / d * d < d);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_remainder_auto()
    ensures 
        forall |x: int, d: int| 0 <= x && 0 < d ==> 0 <= #[trigger](x - (x / d * d)) < d,
{
    assert forall |x: int, d: int| 0 <= x && 0 < d implies 0 <= #[trigger](x - (x / d * d)) < d by
    {
        lemma_remainder(x, d);
    }
}

/// Describes fundamental of the modulus operator
// #[verifier::spinoff_prover]
pub proof fn lemma_fundamental_div_mod(x: int, d: int)
    requires d != 0
    ensures x == d * (x / d) + (x % d)
{
    ModINL::lemma_fundamental_div_mod(x, d);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_fundamental_div_mod_auto()
    ensures forall |x: int, d: int| d != 0 ==> x == #[trigger](d * (x / d) + (x % d))
{
    assert forall |x: int, d: int| d != 0 implies x == #[trigger](d * (x / d) + (x % d)) by
    {
        lemma_fundamental_div_mod(x, d);
    }
}

// change to int because verus `*` does not support mixing nat and int
/// Dividing a fraction by a divisor is equivalent to multiplying the fraction's 
/// denominator with the divisor
// #[verifier::spinoff_prover]
pub proof fn lemma_div_denominator(x: int, c: int, d: int)
    requires 
        0 <= x,
        0 < c,
        0 < d
    ensures 
        c * d != 0,
        (x / c) / d == x / (c * d)
{
    lemma_mul_strictly_positive(c, d);
    let r = x % (c as int * d as int);
    lemma_mod_properties_auto();

    lemma_div_pos_is_pos(r, c as int);
    if (r / c as int >= d) {
    ModINL::lemma_fundamental_div_mod(r, c as int);
    lemma_mul_inequality(d as int, r / c as int, c as int);
    lemma_mul_is_commutative_auto();
    }
    assert(r / (c as int) < d);

    lemma_mul_basics_auto();

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
        c * ((x / c) % d) + x % c;
        { lemma_mod_multiples_vanish(-k, x / c, d); lemma_mul_is_commutative_auto(); }
        c * ((x / c + (-k) * d) % d) + x % c;
        { lemma_hoist_over_denominator(x, (-k) * d, c as nat); }
        c * (((x + (((-k) * d) * c)) / c) % d) + x % c;
        { lemma_mul_is_associative(-k, d, c); }
        c * (((x + ((-k) * (d * c))) / c) % d) + x % c;
        { lemma_mul_unary_negation(k, d * c); }
        c * (((x + (-(k * (d * c)))) / c) % d) + x % c;    { lemma_mul_is_associative(k, d, c); }
        c * (((x + (-(k * d * c))) / c) % d) + x % c;
        { }
        c * (((x - k * d * c) / c) % d) + x % c;
        {
            lemma_mul_is_associative_auto();
            lemma_mul_is_commutative_auto();
        }
        c * ((r / c) % d) + x % c;
        { }
        c * (r / c) + x % c;
        { lemma_fundamental_div_mod(r, c);
            assert(r == c * (r / c) + r % c);
            lemma_mod_mod(x, c, d);
            assert(r % c == x % c);
        }
        r;
        { lemma_mod_is_mod_recursive_auto(); }
        r % (c * d);
        { }
        (x - (c * d) * k) % (c * d);
        { lemma_mul_unary_negation(c * d, k); }
        (x + (c * d) * (-k)) % (c * d);
        { lemma_mod_multiples_vanish(-k, x, c * d); }
        x % (c * d);
    }
    
    assert (c * (x / c) + x % c - r == c * (x / c) - c * ((x / c) % d) ==> x - r == c * (x / c) - c * ((x / c) % d)) by {
        lemma_fundamental_div_mod(x, c);
    };
    
    assert((x / c) / d == x / (c * d)) by {
        lemma_fundamental_div_mod(x / c, d);
        lemma_mul_is_associative_auto();
        lemma_mul_is_distributive_auto();
        lemma_fundamental_div_mod(x, c * d);
        lemma_mul_equality_converse(c * d, (x / c) / d, x / (c * d));
    }

    assert(c * d != 0) by {
        assert(0 < c * d);
    }
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_denominator_auto()
    ensures
        forall |c: int, d: int| 0 < c && 0 < d ==> #[trigger](c * d) != 0,
        forall |x: int, c: int, d: int| 0 <= x && 0 < c && 0 < d ==> #[trigger]((x / c) / d) == x / (c * d)
{
    lemma_mul_nonzero_auto();
    assert forall |x: int, c: int, d: int| 0 <= x && 0 < c && 0 < d implies #[trigger]((x / c) / d) == x / (c * d) by
    {
        lemma_div_denominator(x, c, d);
    }
}

/// Multiplying an integer by a fraction is equivalent to multiplying the integer by the
/// fraction's numerator
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_hoist_inequality(x: int, y: int, z: int)
    requires 
        0 <= x,
        0 < z
    ensures x * (y / z) <= (x * y) / z
{
    calc! {
    (==)
    (x * y) / z;
    (==)   { lemma_fundamental_div_mod(y, z); }
    (x * (z * (y / z) + y % z)) / z;
    (==)    { lemma_mul_is_distributive_auto(); }
    (x * (z * (y / z)) + x * (y % z)) / z;
    }

    assert ((x * (z * (y / z)) + x * (y % z)) / z >=  x * (y / z)) by {
        lemma_mod_properties_auto();
        lemma_mul_nonnegative(x, y % z);
        lemma_div_is_ordered(x * (z * (y / z)), x * (z * (y / z)) + x * (y % z), z);
        lemma_mul_is_associative_auto();
        lemma_mul_is_commutative_auto();
        lemma_div_multiples_vanish(x * (y / z), z);
    };
}

// #[verifier::spinoff_prover]
pub proof fn lemma_mul_hoist_inequality_auto()
    ensures
        forall |x: int, y: int, z: int| #![trigger (x * (y / z)), ((x * y) / z)] 0 <= x && 0 < z ==> (x * (y / z)) <= ((x * y) / z),
{
    assert forall |x: int, y: int, z: int| 0 <= x && 0 < z implies #[trigger](x * (y / z)) <= #[trigger]((x * y) / z) by
    {
        lemma_mul_hoist_inequality(x, y, z);
    }
}

/// For a positive integer `d`, if `a - a % d` is less than or equal to `b` 
/// and `b` is less than `a + d - a % d`, then the quotient of `a` divided by `d`
/// is equivalent to the quotient of `b` divided by `d`.
/// 
/// In other words, if `a` and `b` occur in between the same two multiples of `d`, then
/// their quotient with `d` is equivalent.
// #[verifier::spinoff_prover]
pub proof fn lemma_indistinguishable_quotients(a: int, b: int, d: int)
    requires
        0 < d,
        0 <= a - a % d <= b < a + d - a % d,
    ensures a / d == b / d
{
    lemma_div_induction_auto(d, a - b, |ab: int| {let u = ab + b; 0 <= u - u % d <= b < u + d - u % d ==> u / d == b / d});
}

// #[verifier::spinoff_prover]
pub proof fn lemma_indistinguishable_quotients_auto()
    ensures
        forall |a: int, b: int, d: int| #![trigger (a / d), (b / d)] 0 < d && 0 <= a - a % d <= b < a + d - a % d ==> (a / d) == (b / d)
{
    assert forall |a: int, b: int, d: int| 0 < d && 0 <= a - a % d <= b < a + d - a % d implies #[trigger](a / d) == #[trigger](b / d) by
    {
        lemma_indistinguishable_quotients(a, b, d);
    }
}

/// Common factors from the dividend and divisor of a modulus operation can be factored out
// #[verifier::spinoff_prover]
pub proof fn lemma_truncate_middle(x: int, b: int, c: int)
    requires 
        0 <= x,
        0 < b,
        0 < c,
    ensures
        0 < b * c,
        (b * x) % (b * c) == b * (x % c)
{
    lemma_mul_strictly_positive_auto();
    lemma_mul_nonnegative_auto();
    calc! {
    (==)
    b * x;
    { ModINL::lemma_fundamental_div_mod(b * x, b * c); }
    (b * c) * ((b * x) / (b * c)) + (b * x) % (b * c);
    { lemma_div_denominator(b * x, b, c); }
    (b * c) * (((b * x) / b) / c) + (b * x) % (b * c);
    { lemma_mul_is_commutative_auto(); lemma_div_by_multiple(x, b); }
    (b * c) * (x / c) + (b * x) % (b * c);
    }

    assert(b * x == (b * c) * (x / c) + b * (x % c)) by {
        ModINL::lemma_fundamental_div_mod(x, c);
        lemma_mul_is_distributive_auto();
        lemma_mul_is_associative_auto();
    };
}

// #[verifier::spinoff_prover]
pub proof fn lemma_truncate_middle_auto()
    ensures forall |x: int, b: int, c: int| #![trigger (b * (x % c))] 0 <= x && 0 < b && 0 < c && 0 < b * c ==> (b * x) % (b * c) == b * (x % c)
{
    assert forall |x: int, b: int, c: int| 0 <= x && 0 < b && 0 < c && 0 < b * c implies #[trigger](b * (x % c)) == ((b * x) % (b * c)) by
    {
        lemma_truncate_middle(x, b, c);
    }
}

/// Multiplying the numerator and denominator by an integer does not change the quotient
// #[verifier::spinoff_prover]
pub proof fn lemma_div_multiples_vanish_quotient(x: int, a: int, d: int)
    requires
        0 < x,
        0 <= a,
        0 < d,
    ensures
        0 < x * d,
        a / d == (x * a) / (x * d),
{
    lemma_mul_strictly_positive(x,d);
    calc! { (==)
        (x * a) / (x * d);
        {
            lemma_mul_nonnegative(x, a);
            lemma_div_denominator(x * a, x, d); 
        }
        ((x * a) / x) / d;
        { lemma_div_multiples_vanish(a, x); }
        a / d;
    }
}

pub proof fn lemma_div_multiples_vanish_quotient_auto()
    ensures
        forall |x: int, a: int, d: int| #![trigger (a / d), (x * a), (x * d)]
            0 < x && 0 <= a && 0 < d ==> 0 < x * d && a / d == (x * a) / (x * d)
{
    assert forall |x: int, a: int, d: int| #![trigger (a / d), (x * a), (x * d)]
            0 < x && 0 <= a && 0 < d implies 0 < x * d && a / d == (x * a) / (x * d) by {
        lemma_div_multiples_vanish_quotient(x, a, d);
    }
}

/// Rounds down when adding an integer r to the dividend a that is smaller than the divisor d, and then
/// multiplying by d
// #[verifier::spinoff_prover]
pub proof fn lemma_round_down(a: int, r: int, d: int)
    requires
        0 < d,
        a % d == 0,
        0 <= r < d,
    ensures
        a == d * ((a + r) / d),
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, a, |u: int| u % d == 0 ==> u == d * ((u + r) / d));
}

// #[verifier::spinoff_prover]
pub proof fn lemma_round_down_auto()
    ensures forall |a: int, r: int, d: int| #![trigger (d * ((a + r) / d))] 0 < d && a % d == 0 && 0 <= r < d ==> a == d * ((a + r) / d),
{
    assert forall |a: int, r: int, d: int| 0 < d && a % d == 0 && 0 <= r < d implies #[trigger](d * ((a + r) / d)) == a by
    {
        lemma_round_down(a, r, d);
    }
}

/// This is the same as writing x + (b/d) == x when b is less than d; this is true because (b/d) == 0
// #[verifier::spinoff_prover]
pub proof fn lemma_div_multiples_vanish_fancy(x: int, b: int, d: int)
    requires 
        0 < d,
        0 <= b < d,
    ensures 
        (d * x + b) / d == x
{
    let f = |u: int| (d * u + b) / d == u;
  
    assert(f(0)) by { lemma_div_auto(d); }
    assert forall |i: int| i >= 0 && #[trigger] f(i) implies #[trigger] f(add1(i, 1)) by {
        assert(d * (i + 1) + b == d * i + b + d) by {
            assert(d * (i + 1) == d * i + d) by {
                lemma_mul_is_distributive_add(d, i, 1);
                lemma_mul_basics(d);
            }
        }
        crate::nonlinear_arith::internals::div_internals::lemma_div_basics(d);
    }
    assert forall |i: int| i <= 0 && #[trigger] f(i) implies #[trigger] f(sub1(i, 1)) by {
        assert(d * (i - 1) + b == d * i + b - d) by {
            assert(d * (i - 1) == d * i - d) by {
                lemma_mul_is_distributive_sub(d, i, 1);
                lemma_mul_basics(d);
            }
        }
        crate::nonlinear_arith::internals::div_internals::lemma_div_basics(d);
    }
    lemma_mul_auto();
    lemma_mul_induction(f);
    assert(f(x));
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_multiples_vanish_fancy_auto()
    ensures forall |x: int, b: int, d: int| #![trigger (d * x + b) / d] 0 < d && 0 <= b < d ==> (d * x + b) / d == x,
{
    assert forall |x: int, b: int, d: int| 0 < d && 0 <= b < d implies #[trigger]((d * x + b) / d) == x by
    {
        lemma_div_multiples_vanish_fancy(x, b, d);
    }
}

/// Multiplying an integer by a common numerator and denominator results in the original integer
// #[verifier::spinoff_prover]
pub proof fn lemma_div_multiples_vanish(x: int, d: int)
    requires 0 < d
    ensures (d * x) / d == x
{
    lemma_div_multiples_vanish_fancy(x, 0, d);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_multiples_vanish_auto()
    ensures forall |x: int, d: int| #![trigger (d * x) / d] 0 < d ==> (d * x) / d == x,
{
    assert forall |x: int, d: int| 0 < d implies #[trigger]((d * x) / d) == x by
    {
        lemma_div_multiples_vanish(x, d);
    }
}

/// Multiplying a whole number by a common numerator and denominator results in the original integer
// #[verifier::spinoff_prover]
pub proof fn lemma_div_by_multiple(b: int, d: int)
    requires
        0 <= b,
        0 < d,
    ensures
        (b * d) / d == b
{
    lemma_div_multiples_vanish(b, d);
    lemma_mul_auto();
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_by_multiple_auto()
    ensures forall |b: int, d: int| #![trigger ((b * d) / d)] 0 <= b && 0 < d ==> (b * d) / d == b,
{
    assert forall |b: int, d: int| 0 <= b && 0 < d implies #[trigger]((b * d) / d) == b by
    {
        lemma_div_by_multiple(b, d);
    }
}

/// A dividend y that is a positive multiple of the divisor z will always yield a greater quotient 
/// than a dividend x that is less than y
// #[verifier::spinoff_prover]
pub proof fn lemma_div_by_multiple_is_strongly_ordered(x: int, y: int, m: int, z: int)
    requires
        x < y,
        y == m * z,
        0 < z,
    ensures
        x / z < y / z
{
    lemma_mod_multiples_basic(m, z);
    lemma_div_induction_auto(z, y - x, |yx: int| {let u = yx + x; x < u && u % z == 0 ==> x / z < u / z});
}

// #[verifier::spinoff_prover]
pub proof fn lemma_div_by_multiple_is_strongly_ordered_auto()
    ensures forall |x: int, y: int, m: int, z: int| #![trigger x / z, m * z, y / z] x < y && y == m * z && 0 < z ==> x / z < y / z,
{
    assert forall |x: int, y: int, m: int, z: int| x < y && y == #[trigger](m * z) && 0 < z implies #[trigger](x / z) < #[trigger](y / z) by
    {
        lemma_div_by_multiple_is_strongly_ordered(x, y, m, z);
    }
}

/// If an integer a is less than or equal to the product of two other integers b and c, then the 
/// quotient of a/b will be less than or equal to c
//#[verifier::spinoff_prover]
pub proof fn lemma_multiply_divide_le(a: int, b: int, c: int)
    requires
        0 < b,
        a <= b * c,
    ensures
        a / b <= c
{
    lemma_mod_multiples_basic(c, b);
    let f = |i: int| 0 <= i && (i + a) % b == 0 ==> a / b <= (i + a) / b;
    lemma_div_induction_auto(b, b * c - a, f);
    lemma_div_multiples_vanish(c, b);
}

proof fn lemma_multiply_divide_le_auto()
    ensures forall |a: int, b: int, c: int| #![trigger a / b, b * c] 0 < b && a <= b * c ==> a / b <= c,
{
    assert forall |a: int, b: int, c: int| 0 < b && a <= #[trigger](b * c) implies #[trigger](a / b) <= c by
    {
        lemma_multiply_divide_le(a, b, c);
    }
}

/// If an integer a is less than the product of two other integers b and c, then the quotient 
/// of a/b will be less than c
//#[verifier::spinoff_prover]
pub proof fn lemma_multiply_divide_lt(a: int, b: int, c: int)
    requires 
        0 < b,
        a < b * c,
    ensures
        a / b < c
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

// #[verifier::spinoff_prover]
pub proof fn lemma_multiply_divide_lt_auto()
    ensures forall |a: int, b: int, c: int| #![trigger a / b, b * c] 0 < b && a < b * c ==> a / b < c,
{
    assert forall |a: int, b: int, c: int| 0 < b && a < #[trigger](b * c) implies #[trigger](a / b) < c by
    {
        lemma_multiply_divide_lt(a, b, c);
    }
}

/// Expresses the equality of giving fractions common denominators and then adding them together
// #[verifier::spinoff_prover]
pub proof fn lemma_hoist_over_denominator(x: int, j: int, d: nat)
    requires 0 < d
    ensures x / d as int + j == (x + j * d) / d as int
{
    lemma_div_auto(d as int);
    let f = |u: int| x / d as int + u == (x + u * d) / d as int;
    // OBSERVE: push precondition on its on scope
    assert (  f(0)
        && (forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger]f(add1(i, 1)))
        && (forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger]f(sub1(i, 1)))) by {
            lemma_mul_auto();
    }
    lemma_mul_induction(f);
    assert(f(j));
}

// #[verifier::spinoff_prover]
pub proof fn lemma_hoist_over_denominator_auto()
    ensures forall |x: int, j: int, d: nat| #![trigger x / d as int + j] 0 < d ==> x / d as int + j == (x + j * d) / d as int,
{
    assert forall |x: int, j: int, d: nat| 0 < d implies #[trigger](x / d as int + j) == (x + j * d) / d as int by
    {
        lemma_hoist_over_denominator(x, j, d);
    }
}

/// For nonnegative integer `a` and positive integers `b` and `c`, 
/// the remainder of `b * (a / b)` divided by `b * c` is less than or equal to `b * (c - 1)`.
/// This accounts for the rounding down that occurs in int division.
// #[verifier::spinoff_prover]
pub proof fn lemma_part_bound1(a: int, b: int, c: int)
    requires 
        0 <= a,
        0 < b,
        0 < c,
    ensures
        0 < b * c,
        (b * (a / b) % (b * c)) <= b * (c - 1)
{
    lemma_mul_strictly_positive_auto();
    calc! {
        (==)
        b * (a / b) % (b * c);
        { ModINL::lemma_fundamental_div_mod(b * (a / b), b * c); }
        b * (a / b) - (b * c) * ((b * (a / b)) / (b * c));
        { lemma_mul_is_associative_auto(); }
        b * (a / b) - b * (c * ((b * (a / b)) / (b * c)));
        { lemma_mul_is_distributive_auto(); }
        b * ((a / b) - (c * ((b * (a / b)) / (b * c))));
    }

    assert(b * (a / b) % (b * c) <= b * (c - 1)) by
        { lemma_mul_is_commutative_auto(); lemma_mul_inequality_auto(); };
}

#[verifier::spinoff_prover]
pub proof fn lemma_part_bound1_auto()
    ensures
        forall |b: int, c: int| #![trigger b * c] 0 < b && 0 < c ==> 0 < b * c,
        forall |a: int, b: int, c: int| #![trigger (b * (a / b) % (b * c))] 0 <= a && 0 < b && 0 < c ==> b * (a / b) % (b * c) <= b * (c - 1),
{
    assert forall |b: int, c: int| #![trigger b * c] 0 < b && 0 < c implies 0 < b * c by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall |a: int, b: int, c: int| #![trigger (b * (a / b) % (b * c))]
        0 <= a && 0 < b && 0 < c implies
        b * (a / b) % (b * c) <= b * (c - 1) by
    {
        lemma_part_bound1(a, b, c);
    }
}

}
