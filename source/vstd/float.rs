//! Properties of floating point values.
use super::prelude::*;

verus! {

pub trait FloatBitsProperties {
    spec fn to_bits_spec(&self) -> int;

    // All bits except sign bit
    spec fn to_bits_abs_spec(&self) -> int;

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
    open spec fn to_bits_spec(&self) -> int {
        f32_to_bits(*self)
    }

    open spec fn to_bits_abs_spec(&self) -> int {
        let bits = self.to_bits_spec();
        if bits >= 0x8000_0000 {
            bits - 0x8000_0000
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
    open spec fn to_bits_spec(&self) -> int {
        f64_to_bits(*self)
    }

    open spec fn to_bits_abs_spec(&self) -> int {
        let bits = self.to_bits_spec();
        if bits >= 0x8000_0000_0000_0000 {
            bits - 0x8000_0000_0000_0000
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

} // verus!
