// most of the codes are copied from: https://github.com/utaal/verified-nrkernel/blob/main/page-table/lib.rs
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use vstd::{pervasive::*, *};

verus! {

proof fn mod_of_mul_int(a: int, b: int)
    by (integer_ring) {
    ensures((a * b) % b == 0);
}

proof fn mod_of_mul(a: nat, b: nat)
    by (nonlinear_arith)
    requires
        b > 0,
    ensures
        (a * b) % b == 0,
{
    mod_of_mul_int(a as int, b as int);
    // if a == 0 {}
    // else {
    //     assert(a > 0);
    //     assert(b > 0);
    //     assert(a*b > 0);
    //     assert( (a*b) % b >= 0);
    // }
}

pub proof fn mod_add_zero_int(a: int, b: int, c: int)
    by (integer_ring)
    requires
        a % c == 0,
        b % c == 0,
    ensures
        (a + b) % c == 0,
{
}

pub proof fn mod_add_zero(a: nat, b: nat, c: nat)
    by (nonlinear_arith)
    requires
        a % c == 0,
        b % c == 0,
        c > 0,
    ensures
        (a + b) % c == 0,
{
    mod_add_zero_int(a as int, b as int, c as int);
}

pub proof fn subtract_mod_aligned_int(a: int, b: int)
    by (integer_ring)
    ensures
        (a - (a % b)) % b == 0,
{
}

pub proof fn subtract_mod_aligned(a: nat, b: nat)
    by (nonlinear_arith)
    requires
        0 < b,
    ensures
        (a - (a % b)) % (b as int) == 0,
{
    subtract_mod_aligned_int(a as int, b as int);
}

pub proof fn mod_mult_zero_implies_mod_zero_int(a: int, b: int, c: int)
    by (integer_ring)
    requires
        a % (b * c) == 0,
    ensures
        a % b == 0,
{
}

pub proof fn mod_mult_zero_implies_mod_zero(a: nat, b: nat, c: nat)
    by (nonlinear_arith)
    requires
        a % (b * c) == 0,
        b > 0,
        c > 0,
    ensures
        a % b == 0,
{
    mod_mult_zero_implies_mod_zero_int(a as int, b as int, c as int);
}

pub proof fn subtract_mod_eq_zero_int(a: int, b: int, c: int)
    by (integer_ring)
    requires
        a % c == 0,
        b % c == 0,
    ensures
        (b - a) % c == 0,
{
}

pub proof fn subtract_mod_eq_zero(a: nat, b: nat, c: nat)
    by (nonlinear_arith)
    requires
        a % c == 0,
        b % c == 0,
        a <= b,
        c > 0,
    ensures
        (b - a) % (c as int) == 0,
{
    subtract_mod_eq_zero_int(a as int, b as int, c as int);
}

pub proof fn multiple_offsed_mod_gt_0_int(a: int, b: int, c: int, ac: int, bc: int, abc: int)
    by (integer_ring)
    requires
        ac == a % c,
        bc == b % c,
        abc == (a - b) % c,
    ensures
        (ac - bc - abc) % c == 0,
{
}

pub proof fn multiple_offsed_mod_gt_0(a: nat, b: nat, c: nat)
    by (nonlinear_arith)
    requires
        a > b,
        c > 0,
        b % c == 0,
        a % c > 0,
    ensures
        (a - b) % (c as int) > 0,
{
    multiple_offsed_mod_gt_0_int(
        a as int,
        b as int,
        c as int,
        (a % c) as int,
        (b % c) as int,
        ((a - b) % (c as int)) as int,
    );
}

// currently can't use Singular for this proof
// however, I think we can extend the encoding for div
pub proof fn FundamentalDivMod(x: int, d: int)
    by (nonlinear_arith)
    requires
        d > 0,
    ensures
        x == d * (x / d) + (x % d),
{
}

// can't use Singular for this proof because of bound
// however, there might be a way to encode this as an "axiom" in Singular
// add an equality to the ring whenever we can prove a bound from Z3
pub proof fn LemmaSmallMod(x: int, m: int)
    by (nonlinear_arith)
    requires
        x >= 0,
        m > 0,
        x < m,
    ensures
        x % m == x,
{
}

// can't use Singular for this proof because of bound
pub proof fn LemmaModBasics(x: int, m: int)
    by (nonlinear_arith)
    requires
        m > 0,
    ensures
        m % m == 0,
        (x % m) % m == x % m,
        0 <= x % m,
        x % m < m,
{
}

// can't use Singular for this proof because of bound
pub proof fn LemmaModDecreases(x: int, m: int)
    by (nonlinear_arith)
    requires
        m > 0,
        x >= 0,
    ensures
        x % m <= x,
{
}

// can't use Singular for this proof because of bound
pub proof fn LemmaModIsZero(x: int, m: int)
    by (nonlinear_arith)
    requires
        m > 0,
        x > 0,
        x % m == 0,
    ensures
        m <= x,
{
}

pub proof fn LemmaModMultiplesBasic(x: int, m: int)
    by (integer_ring)
    ensures
        (x * m) % m == 0,
{
}

pub proof fn LemmaModMultipleVanish(b: int, m: int)
    by (integer_ring)
    ensures
        (b + m) % m == b % m,
        (b - m) % m == b % m,
{
}

pub proof fn LemmaModMultiplesVanish(a: int, b: int, m: int)
    by (integer_ring)
    ensures
        (b + a * m) % m == b % m,
        (b + m * a) % m == b % m,
        (b - a * m) % m == b % m,
        (b - m * a) % m == b % m,
{
}

pub proof fn LemmaAddModNoopLeft(x: int, y: int, m: int)
    by (integer_ring)
    ensures
        ((x % m) + y) % m == (x + y) % m,
{
}

pub proof fn LemmaSubModNoopRight(x: int, y: int, m: int)
    by (integer_ring)
    ensures
        (x - (y % m)) % m == (x - y) % m,
{
}

pub proof fn LemmaModNegNeg(x: int, d: int)
    by (integer_ring)
    ensures
        x % d == (x * (1 - d)) % d,
{
}

pub proof fn LemmaMulModNoopRight(x: int, y: int, m: int)
    by (integer_ring)
    ensures
        x * (y % m) % m == (x * y) % m,
{
}

pub proof fn LemmaMulModNoopGeneral(x: int, y: int, m: int)
    by (integer_ring)
    ensures
        ((x % m) * y) % m == (x * y) % m,
        (x * (y % m)) % m == (x * y) % m,
        ((x % m) * (y % m)) % m == (x * y) % m,
{
}

pub proof fn LemmaMulIsDistributive(x: int, y: int, z: int)
    by (integer_ring)
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
}

fn main() {
}

} // verus!
