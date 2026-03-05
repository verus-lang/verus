//! Properties of floating point values.
use super::prelude::*;

verus! {

pub trait FloatBitsProperties {
    type Bits;

    spec fn to_bits_spec(&self) -> Self::Bits;

    // All bits except sign bit
    spec fn to_bits_abs_spec(&self) -> Self::Bits;

    // Sign bit is true (may apply to zero, subnormal, normal, infinite, NaN)
    spec fn is_sign_negative_spec(&self) -> bool;

    // Zero, subnormal, or normal (not infinite, not NaN)
    spec fn is_finite_spec(&self) -> bool;

    // Positive or negative infinity (not zero, not subnormal, not normal, not NaN)
    spec fn is_infinite_spec(&self) -> bool;

    // A NaN value (not zero, not subnormal, not normal, not NaN)
    spec fn is_nan_spec(&self) -> bool;
}

impl FloatBitsProperties for f32 {
    type Bits = u32;

    open spec fn to_bits_spec(&self) -> u32 {
        f32_to_bits(*self)
    }

    open spec fn to_bits_abs_spec(&self) -> u32 {
        let bits = self.to_bits_spec();
        if bits >= 0x8000_0000 {
            (bits - 0x8000_0000) as u32
        } else {
            bits
        }
    }

    // Sign bit is true (may apply to zero, subnormal, normal, infinite, NaN)
    open spec fn is_sign_negative_spec(&self) -> bool {
        self.to_bits_spec() >= 0x8000_0000
    }

    open spec fn is_finite_spec(&self) -> bool {
        self.to_bits_abs_spec() < 0x7f80_0000
    }

    open spec fn is_infinite_spec(&self) -> bool {
        self.to_bits_abs_spec() == 0x7f80_0000
    }

    open spec fn is_nan_spec(&self) -> bool {
        self.to_bits_abs_spec() > 0x7f80_0000
    }
}

impl FloatBitsProperties for f64 {
    type Bits = u64;

    open spec fn to_bits_spec(&self) -> u64 {
        f64_to_bits(*self)
    }

    open spec fn to_bits_abs_spec(&self) -> u64 {
        let bits = self.to_bits_spec();
        if bits >= 0x8000_0000_0000_0000 {
            (bits - 0x8000_0000_0000_0000) as u64
        } else {
            bits
        }
    }

    // Sign bit is true (may apply to zero, subnormal, normal, infinite, NaN)
    open spec fn is_sign_negative_spec(&self) -> bool {
        self.to_bits_spec() >= 0x8000_0000_0000_0000
    }

    open spec fn is_finite_spec(&self) -> bool {
        self.to_bits_abs_spec() < 0x7ff0_0000_0000_0000
    }

    open spec fn is_infinite_spec(&self) -> bool {
        self.to_bits_abs_spec() == 0x7ff0_0000_0000_0000
    }

    open spec fn is_nan_spec(&self) -> bool {
        self.to_bits_abs_spec() > 0x7ff0_0000_0000_0000
    }
}

pub assume_specification[ <f32 as Clone>::clone ](f: &f32) -> (res: f32)
    ensures
        res == f,
;

pub assume_specification[ <f64 as Clone>::clone ](f: &f64) -> (res: f64)
    ensures
        res == f,
;

// Nondeterministic cast specification functions.
// Each `{src}_as_{dst}_ensures(input, output)` predicate constrains the result
// of the Rust `as` cast `input as {dst}`. Because float casts involve rounding
// and platform-dependent behavior, each cast produces a nondeterministic result
// constrained only by this uninterpreted predicate. Users can supply axioms
// about these predicates to reason about specific rounding modes or exactness.
//
// This follows the same pattern as `add_ensures`, `sub_ensures`, etc. for
// float arithmetic.

// --- Integer to f32 ---

pub uninterp spec fn u8_as_f32_ensures(i: u8, o: f32) -> bool;
pub uninterp spec fn u16_as_f32_ensures(i: u16, o: f32) -> bool;
pub uninterp spec fn u32_as_f32_ensures(i: u32, o: f32) -> bool;
pub uninterp spec fn u64_as_f32_ensures(i: u64, o: f32) -> bool;
pub uninterp spec fn u128_as_f32_ensures(i: u128, o: f32) -> bool;
pub uninterp spec fn usize_as_f32_ensures(i: usize, o: f32) -> bool;
pub uninterp spec fn i8_as_f32_ensures(i: i8, o: f32) -> bool;
pub uninterp spec fn i16_as_f32_ensures(i: i16, o: f32) -> bool;
pub uninterp spec fn i32_as_f32_ensures(i: i32, o: f32) -> bool;
pub uninterp spec fn i64_as_f32_ensures(i: i64, o: f32) -> bool;
pub uninterp spec fn i128_as_f32_ensures(i: i128, o: f32) -> bool;
pub uninterp spec fn isize_as_f32_ensures(i: isize, o: f32) -> bool;

// --- Integer to f64 ---

pub uninterp spec fn u8_as_f64_ensures(i: u8, o: f64) -> bool;
pub uninterp spec fn u16_as_f64_ensures(i: u16, o: f64) -> bool;
pub uninterp spec fn u32_as_f64_ensures(i: u32, o: f64) -> bool;
pub uninterp spec fn u64_as_f64_ensures(i: u64, o: f64) -> bool;
pub uninterp spec fn u128_as_f64_ensures(i: u128, o: f64) -> bool;
pub uninterp spec fn usize_as_f64_ensures(i: usize, o: f64) -> bool;
pub uninterp spec fn i8_as_f64_ensures(i: i8, o: f64) -> bool;
pub uninterp spec fn i16_as_f64_ensures(i: i16, o: f64) -> bool;
pub uninterp spec fn i32_as_f64_ensures(i: i32, o: f64) -> bool;
pub uninterp spec fn i64_as_f64_ensures(i: i64, o: f64) -> bool;
pub uninterp spec fn i128_as_f64_ensures(i: i128, o: f64) -> bool;
pub uninterp spec fn isize_as_f64_ensures(i: isize, o: f64) -> bool;

// --- f32 to integer ---

pub uninterp spec fn f32_as_u8_ensures(f: f32, o: u8) -> bool;
pub uninterp spec fn f32_as_u16_ensures(f: f32, o: u16) -> bool;
pub uninterp spec fn f32_as_u32_ensures(f: f32, o: u32) -> bool;
pub uninterp spec fn f32_as_u64_ensures(f: f32, o: u64) -> bool;
pub uninterp spec fn f32_as_u128_ensures(f: f32, o: u128) -> bool;
pub uninterp spec fn f32_as_usize_ensures(f: f32, o: usize) -> bool;
pub uninterp spec fn f32_as_i8_ensures(f: f32, o: i8) -> bool;
pub uninterp spec fn f32_as_i16_ensures(f: f32, o: i16) -> bool;
pub uninterp spec fn f32_as_i32_ensures(f: f32, o: i32) -> bool;
pub uninterp spec fn f32_as_i64_ensures(f: f32, o: i64) -> bool;
pub uninterp spec fn f32_as_i128_ensures(f: f32, o: i128) -> bool;
pub uninterp spec fn f32_as_isize_ensures(f: f32, o: isize) -> bool;

// --- f64 to integer ---

pub uninterp spec fn f64_as_u8_ensures(f: f64, o: u8) -> bool;
pub uninterp spec fn f64_as_u16_ensures(f: f64, o: u16) -> bool;
pub uninterp spec fn f64_as_u32_ensures(f: f64, o: u32) -> bool;
pub uninterp spec fn f64_as_u64_ensures(f: f64, o: u64) -> bool;
pub uninterp spec fn f64_as_u128_ensures(f: f64, o: u128) -> bool;
pub uninterp spec fn f64_as_usize_ensures(f: f64, o: usize) -> bool;
pub uninterp spec fn f64_as_i8_ensures(f: f64, o: i8) -> bool;
pub uninterp spec fn f64_as_i16_ensures(f: f64, o: i16) -> bool;
pub uninterp spec fn f64_as_i32_ensures(f: f64, o: i32) -> bool;
pub uninterp spec fn f64_as_i64_ensures(f: f64, o: i64) -> bool;
pub uninterp spec fn f64_as_i128_ensures(f: f64, o: i128) -> bool;
pub uninterp spec fn f64_as_isize_ensures(f: f64, o: isize) -> bool;

// --- Float to float ---

pub uninterp spec fn f32_as_f64_ensures(f: f32, o: f64) -> bool;
pub uninterp spec fn f64_as_f32_ensures(f: f64, o: f32) -> bool;

} // verus!
