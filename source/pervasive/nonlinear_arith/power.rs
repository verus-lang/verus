//! Lemma for Exponentials

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::calc_macro::*;

verus! {

use crate::nonlinear_arith::div::*;
use crate::nonlinear_arith::modulus::*;
use crate::nonlinear_arith::internals::general_internals::{is_le};
use crate::nonlinear_arith::mul::{lemma_mul_inequality, lemma_mul_nonnegative_auto, lemma_mul_strictly_increases, lemma_mul_left_inequality, lemma_mul_basics_auto, lemma_mul_increases_auto, lemma_mul_strictly_increases_auto, lemma_mul_is_commutative_auto, lemma_mul_is_distributive_auto, lemma_mul_is_associative_auto, lemma_mul_nonnegative};
use crate::nonlinear_arith::internals::mul_internals::{lemma_mul_auto, lemma_mul_induction_auto};
use crate::nonlinear_arith::math::{sub as sub1};

#[verifier(opaque)]
pub open spec fn pow(b: int, e: nat) -> int
    decreases e
{
    if e == 0 {
        1
    } else {
        b * pow(b, (e - 1) as nat)
    }
}

/// A number raised to the power of 0 equals
// #[verifier::spinoff_prover]
pub proof fn lemma_pow0(b: int)
    ensures pow(b, 0) == 1
{
    reveal(pow);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_pow0_auto()
    ensures forall |b: int| #[trigger]pow(b, 0 as nat) == 1
{
    reveal(pow);
}

/// A number raised to the power of 1 equals the number itself.
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
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

/// 0 raised to a positive power equals 0.
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
pub proof fn lemma0_pow_auto()
    ensures forall |e: nat| e > 0 ==> #[trigger]pow(0, e) == 0
{
    reveal(pow);
    assert forall |e: nat| e > 0 implies #[trigger]pow(0, e) == 0 by
    {
        lemma0_pow(e);
    }
}

/// 1 raised to any power equals 1.
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
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

/// Squaring a number is equal to raising it to the power of 2.
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
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

/// A positive number raised to any power is positive.
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
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

/// Add exponents when multiplying powers with the same base.
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
pub proof fn lemma_pow_adds_auto()
    ensures forall |x: int, y: nat, z: nat| #[trigger] pow(x, y + z) == pow(x, y) * pow(x, z),
{
    assert forall |x: int, y: nat, z: nat| #[trigger] pow(x, y + z) == pow(x, y) * pow(x, z) by
    {
    lemma_pow_adds(x, y, z);
    }
}

/// Subtracting a natural number `e2` from an exponent `e1` and then multiplying
/// by the same base `b` to the exponent `e2` is the same as just `b` to the exponent `e2`.
// #[verifier::spinoff_prover]
pub proof fn lemma_pow_sub_add_cancel(b: int, e1: nat, e2: nat)
    requires e1 >= e2
    ensures pow(b, (e1 - e2) as nat) * pow(b, e2) == pow(b, e1)
    decreases e1
{
    lemma_pow_adds(b, (e1 - e2) as nat, e2);
}

pub proof fn lemma_pow_sub_add_cancel_auto()
    ensures forall |x: int, y: nat, z: nat| y >= z ==> #[trigger]pow(x, (y - z) as nat) * pow(x, z) == pow(x, y),

{
    assert forall |x: int, y: nat, z: nat| y >= z implies #[trigger]pow(x, (y - z) as nat) * pow(x, z) == pow(x, y) by 
    {
        lemma_pow_sub_add_cancel(x, y, z);
    }
}

/// Subtract exponents when dividing powers.
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
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

/// Multiply exponents when finding the power of a power.
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
pub proof fn lemma_pow_multiplies_auto()
    ensures forall |b: nat, c: nat| 0 <= #[trigger](b * c),
            forall |a: int, b: nat, c: nat| #[trigger]pow(pow(a, b), c) == pow(a, b * c),
{
    assert forall |a: int, b: nat, c: nat| #[trigger]pow(pow(a, b), c) == pow(a, b * c) by
    {
        lemma_pow_multiplies(a, b, c);
    };
}

/// Distribute the power to factors of a product.
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
pub proof fn lemma_pow_distributes_auto()
    ensures forall |x: int, y: nat, z: nat| #[trigger]pow(x * y, z) == pow(x, z) * pow(y as int, z),
{
    // reveal pow();
    assert forall |x: int, y: nat, z: nat| #[trigger]pow(x * y, z) == pow(x, z) * pow(y as int, z) by
    {
    lemma_pow_distributes(x, y as int, z);
    }
}

/// Group properties of powers
/// A convenience function to introduce basic properties about powers.
// #[verifier::spinoff_prover]
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

// TODO: quite longer than dafny
/// A positive number raised to a power strictly increases as the power
/// strictly increases.
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
pub proof fn lemma_pow_strictly_increases_auto()
    ensures forall |b: int, e1: nat, e2: nat| 1 < b && e1 < e2 ==> #[trigger]pow(b, e1) < #[trigger]pow(b, e2),
{
    reveal(pow);
    assert forall |b: int, e1: nat, e2: nat| 1 < b && e1 < e2 implies #[trigger]pow(b, e1) < #[trigger]pow(b, e2) by
    {
        lemma_pow_strictly_increases(b as nat, e1, e2);
    }
}

/// A positive number raised to a power increases as the power increases.
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
pub proof fn lemma_pow_increases_auto()
    ensures forall |b: int, e1: nat, e2: nat| b > 0 && e1 <= e2 ==> #[trigger]pow(b, e1) <= #[trigger]pow(b, e2),
{
    reveal(pow);
    assert forall |b: int, e1: nat, e2: nat| b > 0 && e1 <= e2 implies #[trigger]pow(b, e1) <= #[trigger]pow(b, e2) by
    {
        lemma_pow_increases(b as nat, e1, e2);
    }
}

/// A power strictly increases as a positive number raised to the power
/// strictly increases.
// #[verifier::spinoff_prover]
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

// seems like automatic trigger selection works well in this case
// #[verifier::spinoff_prover]
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

/// A power increases as a positive number raised to the power increases.
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
pub proof fn lemma_pow_increases_converse_auto()
    ensures forall |b: nat, e1: nat, e2: nat| 1 < b && pow(b as int, e1) <= pow(b as int, e2) ==> e1 <= e2,
{
    assert forall |b: nat, e1: nat, e2: nat| 1 < b && pow(b as int, e1) <= pow(b as int, e2) implies e1 <= e2 by
    {
        lemma_pow_increases_converse(b, e1, e2);
    }
}

/// `(b^xy)^z = (b^x)^yz`
// #[verifier::spinoff_prover]
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

// #[verifier::spinoff_prover]
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

/// Inequality due to smaller numerator, same denominator.
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

// #[verifier::spinoff_prover]
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

/// `b^e % b = 0`
// #[verifier::spinoff_prover]
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

pub proof fn lemma_pow_mod_auto()
    ensures forall |b: nat, e: nat| b > 0 && e > 0 ==> #[trigger]pow(b as int, e) % b as int == 0,
{
    assert forall |b: nat, e: nat| b > 0 && e > 0 implies #[trigger]pow(b as int, e) % b as int == 0 by
    {
        lemma_pow_mod(b, e);
    }
}

/// `((b % e)^e) % m = b^e % m`
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

pub proof fn lemma_pow_mod_noop_auto()
    ensures forall |b: int, e: nat, m: int| m > 0 ==> #[trigger]pow(b % m, e) % m == pow(b, e) % m,
{
    assert forall |b: int, e: nat, m: int| m > 0 implies #[trigger]pow(b % m, e) % m == pow(b, e) % m by
    {
        lemma_pow_mod_noop(b, e, m);
    }
}

}
