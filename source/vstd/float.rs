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

    // A NaN value (not zero, not subnormal, not normal, not infinity)
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

#[verifier::external_trait_specification]
pub trait ExIeeeFloatCast<To> {
    type ExternalTraitSpecificationFor: IeeeFloatCast<To>;
}

// TODO: when IEEE float support is merged, this should point to IeeeFloatCast::ieee_cast
pub uninterp spec fn ieee_float_cast<From: IeeeFloatCast<To>, To>(from: From) -> To;

pub uninterp spec fn float_cast_spec<From, To>(from: From, to: To) -> bool;

// Used only for internal Verus translation of "as" operator;
// this is not meant to be called directly by user code,
// and it is not actually compiled to executable code
#[cfg(verus_keep_ghost)]
#[doc(hidden)]
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::float::float_cast")]
#[verifier::when_used_as_spec(ieee_float_cast)]
pub fn float_cast<From: Copy + IeeeFloatCast<To>, To>(from: From) -> (to: To)
    ensures
        float_cast_spec(from, to),
    opens_invariants none
    no_unwind
{
    unimplemented!{}
}

} // verus!
