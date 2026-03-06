use super::super::prelude::*;

/*
Verus deliberately omits axioms about floating point from vstd,
because the desired set of useful and sound axioms may vary by project and platform.
(See https://github.com/rust-lang/rfcs/blob/master/text/3514-float-semantics.md for details
about why Rust floating point semantics are complex, may be non-deterministic, and may fall short
of desired behavior on some platforms.)

Some platforms may strictly obey IEEE 754 semantics.
For such platforms, you can "broadcast use assume_ieee_float" from this module
to connect the Rust floating point semantics to the IEEE semantics
as defined in SMT solvers according to https://smt-lib.org/theories-FloatingPoint.shtml .
This allows proofs using assert-by-bit_vector, which calls into the SMT solver's bit vector
and floating point theories to prove properties of ieee_add, ieee_eq, ieee_le, etc.
(note that <=, +, etc. in specs are equivalent to ieee_le, ieee_add, etc.):

```
use vstd::std_specs::cmp::{PartialEqSpec, PartialOrdSpec, PartialOrdIs};

fn test(x: f32, y: f32) -> (z: f32)
    requires
        1.0f32 <= x <= 2.0f32,
        4.0f32 <= y <= 8.0f32,
    ensures
        5.0f32 <= z <= 10f32,
{
    broadcast use vstd::contrib::assume_ieee_float::assume_ieee_float;

    let z = x + y;
    assert(5.0f32 <= x + y <= 10.0f32) by(bit_vector)
        requires
            1.0f32 <= x <= 2.0f32,
            4.0f32 <= y <= 8.0f32;
    z
}
```
*/

verus! {

#[cfg(verus_keep_ghost)]
use super::super::std_specs::cmp::{PartialEqSpec, PartialOrdSpec, PartialOrdIs};

#[cfg(verus_keep_ghost)]
use super::super::std_specs::ops::{NegSpec, AddSpec, SubSpec, MulSpec, DivSpec};

use super::super::float::FloatBitsProperties;

// ieee_is_nan picks one particular NaN value, while is_nan_spec covers all possible NaN values
// (i.e. x.ieee_is_nan() && y.ieee_is_nan() ==> x == y, whereas this is not true for is_nan_spec)
pub broadcast axiom fn assume_ieee_f32_is_nan(x: f32)
    ensures
        #![trigger x.is_nan_spec()]
        #![trigger x.ieee_is_nan()]
        x.ieee_is_nan() ==> x.is_nan_spec(),
;

pub broadcast axiom fn assume_ieee_f32_is_infinite(x: f32)
    ensures
        #![trigger x.is_infinite_spec()]
        #![trigger x.ieee_is_infinite()]
        x.is_infinite_spec() == x.ieee_is_infinite(),
;

pub broadcast axiom fn assume_ieee_f32_neg(x: f32)
    ensures
        #![trigger x.neg_req()]
        #![trigger x.neg_spec()]
        #![trigger x.ieee_neg()]
        <f32 as NegSpec>::obeys_neg_spec(),
        x.neg_req(),
        x.neg_spec() == x.ieee_neg(),
;

pub broadcast axiom fn assume_ieee_f32_add(x: f32, y: f32)
    ensures
        #![trigger x.add_req(y)]
        #![trigger x.add_spec(y)]
        #![trigger x.ieee_add(y)]
        <f32 as AddSpec>::obeys_add_spec(),
        x.add_req(y),
        x.add_spec(y) == x.ieee_add(y),
;

pub broadcast axiom fn assume_ieee_f32_sub(x: f32, y: f32)
    ensures
        #![trigger x.sub_req(y)]
        #![trigger x.sub_spec(y)]
        #![trigger x.ieee_sub(y)]
        <f32 as SubSpec>::obeys_sub_spec(),
        x.sub_req(y),
        x.sub_spec(y) == x.ieee_sub(y),
;

pub broadcast axiom fn assume_ieee_f32_mul(x: f32, y: f32)
    ensures
        #![trigger x.mul_req(y)]
        #![trigger x.mul_spec(y)]
        #![trigger x.ieee_mul(y)]
        <f32 as MulSpec>::obeys_mul_spec(),
        x.mul_req(y),
        x.mul_spec(y) == x.ieee_mul(y),
;

pub broadcast axiom fn assume_ieee_f32_div(x: f32, y: f32)
    ensures
        #![trigger x.div_req(y)]
        #![trigger x.div_spec(y)]
        #![trigger x.ieee_div(y)]
        <f32 as DivSpec>::obeys_div_spec(),
        x.div_req(y),
        x.div_spec(y) == x.ieee_div(y),
;

pub broadcast axiom fn assume_ieee_f32_eq(x: f32, y: f32)
    ensures
        #![trigger x.eq_spec(&y)]
        #![trigger x.ieee_eq(y)]
        <f32 as PartialEqSpec>::obeys_eq_spec(),
        x.eq_spec(&y) == x.ieee_eq(y),
;

pub broadcast axiom fn assume_ieee_f32_le(x: f32, y: f32)
    ensures
        #![trigger x.partial_cmp_spec(&y)]
        #![trigger x.ieee_le(y)]
        <f32 as PartialOrdSpec>::obeys_partial_cmp_spec(),
        x.is_le(&y) == x.ieee_le(y),
;

pub broadcast axiom fn assume_ieee_f32_ge(x: f32, y: f32)
    ensures
        #![trigger x.partial_cmp_spec(&y)]
        #![trigger x.ieee_ge(y)]
        <f32 as PartialOrdSpec>::obeys_partial_cmp_spec(),
        x.is_ge(&y) == x.ieee_ge(y),
;

pub broadcast axiom fn assume_ieee_f32_lt(x: f32, y: f32)
    ensures
        #![trigger x.partial_cmp_spec(&y)]
        #![trigger x.ieee_lt(y)]
        <f32 as PartialOrdSpec>::obeys_partial_cmp_spec(),
        x.is_lt(&y) == x.ieee_lt(y),
;

pub broadcast axiom fn assume_ieee_f32_gt(x: f32, y: f32)
    ensures
        #![trigger x.partial_cmp_spec(&y)]
        #![trigger x.ieee_gt(y)]
        <f32 as PartialOrdSpec>::obeys_partial_cmp_spec(),
        x.is_gt(&y) == x.ieee_gt(y),
;

// ieee_is_nan picks one particular NaN value, while is_nan_spec covers all possible NaN values
// (i.e. x.ieee_is_nan() && y.ieee_is_nan() ==> x == y, whereas this is not true for is_nan_spec)
pub broadcast axiom fn assume_ieee_f64_is_nan(x: f64)
    ensures
        #![trigger x.is_nan_spec()]
        #![trigger x.ieee_is_nan()]
        x.ieee_is_nan() ==> x.is_nan_spec(),
;

pub broadcast axiom fn assume_ieee_f64_is_infinite(x: f64)
    ensures
        #![trigger x.is_infinite_spec()]
        #![trigger x.ieee_is_infinite()]
        x.is_infinite_spec() == x.ieee_is_infinite(),
;

pub broadcast axiom fn assume_ieee_f64_neg(x: f64)
    ensures
        #![trigger x.neg_req()]
        #![trigger x.neg_spec()]
        #![trigger x.ieee_neg()]
        <f64 as NegSpec>::obeys_neg_spec(),
        x.neg_req(),
        x.neg_spec() == x.ieee_neg(),
;

pub broadcast axiom fn assume_ieee_f64_add(x: f64, y: f64)
    ensures
        #![trigger x.add_req(y)]
        #![trigger x.add_spec(y)]
        #![trigger x.ieee_add(y)]
        <f64 as AddSpec>::obeys_add_spec(),
        x.add_req(y),
        x.add_spec(y) == x.ieee_add(y),
;

pub broadcast axiom fn assume_ieee_f64_sub(x: f64, y: f64)
    ensures
        #![trigger x.sub_req(y)]
        #![trigger x.sub_spec(y)]
        #![trigger x.ieee_sub(y)]
        <f64 as SubSpec>::obeys_sub_spec(),
        x.sub_req(y),
        x.sub_spec(y) == x.ieee_sub(y),
;

pub broadcast axiom fn assume_ieee_f64_mul(x: f64, y: f64)
    ensures
        #![trigger x.mul_req(y)]
        #![trigger x.mul_spec(y)]
        #![trigger x.ieee_mul(y)]
        <f64 as MulSpec>::obeys_mul_spec(),
        x.mul_req(y),
        x.mul_spec(y) == x.ieee_mul(y),
;

pub broadcast axiom fn assume_ieee_f64_div(x: f64, y: f64)
    ensures
        #![trigger x.div_req(y)]
        #![trigger x.div_spec(y)]
        #![trigger x.ieee_div(y)]
        <f64 as DivSpec>::obeys_div_spec(),
        x.div_req(y),
        x.div_spec(y) == x.ieee_div(y),
;

pub broadcast axiom fn assume_ieee_f64_eq(x: f64, y: f64)
    ensures
        #![trigger x.eq_spec(&y)]
        #![trigger x.ieee_eq(y)]
        <f64 as PartialEqSpec>::obeys_eq_spec(),
        x.eq_spec(&y) == x.ieee_eq(y),
;

pub broadcast axiom fn assume_ieee_f64_le(x: f64, y: f64)
    ensures
        #![trigger x.partial_cmp_spec(&y)]
        #![trigger x.ieee_le(y)]
        <f64 as PartialOrdSpec>::obeys_partial_cmp_spec(),
        x.is_le(&y) == x.ieee_le(y),
;

pub broadcast axiom fn assume_ieee_f64_ge(x: f64, y: f64)
    ensures
        #![trigger x.partial_cmp_spec(&y)]
        #![trigger x.ieee_ge(y)]
        <f64 as PartialOrdSpec>::obeys_partial_cmp_spec(),
        x.is_ge(&y) == x.ieee_ge(y),
;

pub broadcast axiom fn assume_ieee_f64_lt(x: f64, y: f64)
    ensures
        #![trigger x.partial_cmp_spec(&y)]
        #![trigger x.ieee_lt(y)]
        <f64 as PartialOrdSpec>::obeys_partial_cmp_spec(),
        x.is_lt(&y) == x.ieee_lt(y),
;

pub broadcast axiom fn assume_ieee_f64_gt(x: f64, y: f64)
    ensures
        #![trigger x.partial_cmp_spec(&y)]
        #![trigger x.ieee_gt(y)]
        <f64 as PartialOrdSpec>::obeys_partial_cmp_spec(),
        x.is_gt(&y) == x.ieee_gt(y),
;

pub broadcast group assume_ieee_float {
    assume_ieee_f32_is_nan,
    assume_ieee_f32_is_infinite,
    assume_ieee_f32_neg,
    assume_ieee_f32_add,
    assume_ieee_f32_sub,
    assume_ieee_f32_mul,
    assume_ieee_f32_div,
    assume_ieee_f32_eq,
    assume_ieee_f32_le,
    assume_ieee_f32_ge,
    assume_ieee_f32_lt,
    assume_ieee_f32_gt,
    assume_ieee_f64_is_nan,
    assume_ieee_f64_is_infinite,
    assume_ieee_f64_neg,
    assume_ieee_f64_add,
    assume_ieee_f64_sub,
    assume_ieee_f64_mul,
    assume_ieee_f64_div,
    assume_ieee_f64_eq,
    assume_ieee_f64_le,
    assume_ieee_f64_ge,
    assume_ieee_f64_lt,
    assume_ieee_f64_gt,
}

} // verus!
