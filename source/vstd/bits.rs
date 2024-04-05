//! Properties of bitwise operators.
use builtin::*;
use builtin_macros::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::arithmetic::power2::{
    pow2,
    lemma_pow2_adds,
    lemma_pow2_pos,
    lemma2_to64,
    lemma_pow2_strictly_increases,
};
#[cfg(verus_keep_ghost)]
use crate::arithmetic::div_mod::lemma_div_denominator;
#[cfg(verus_keep_ghost)]
use crate::arithmetic::mul::{
    lemma_mul_inequality,
    lemma_mul_is_commutative,
    lemma_mul_is_associative,
};
#[cfg(verus_keep_ghost)]
use crate::calc_macro::*;

} // verus!
  // Proofs that shift right is equivalent to division by power of 2.
macro_rules! lemma_shr_is_div {
    ($name:ident, $name_auto:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "Proof that for given x and n of type "]
        #[doc = stringify!($uN)]
        #[doc = ", shifting x right by n is equivalent to division of x by 2^n."]
        pub proof fn $name(x: $uN, shift: $uN)
            requires
                0 <= shift < <$uN>::BITS,
            ensures
                x >> shift == x as nat / pow2(shift as nat),
            decreases shift,
        {
            reveal(pow2);
            if shift == 0 {
                assert(x >> 0 == x) by (bit_vector);
                assert(pow2(0) == 1) by (compute_only);
            } else {
                assert(x >> shift == (x >> ((sub(shift, 1)) as $uN)) / 2) by (bit_vector)
                    requires
                        0 < shift < <$uN>::BITS,
                ;
                calc!{ (==)
                    (x >> shift) as nat;
                        {}
                    ((x >> ((sub(shift, 1)) as $uN)) / 2) as nat;
                        { $name(x, (shift - 1) as $uN); }
                    (x as nat / pow2((shift - 1) as nat)) / 2;
                        {
                            lemma_pow2_pos((shift - 1) as nat);
                            lemma2_to64();
                            lemma_div_denominator(x as int, pow2((shift - 1) as nat) as int, 2);
                        }
                    x as nat / (pow2((shift - 1) as nat) * pow2(1));
                        {
                            lemma_pow2_adds((shift - 1) as nat, 1);
                        }
                    x as nat / pow2(shift as nat);
                }
            }
        }

        #[doc = "Proof that for all x and n of type "]
        #[doc = stringify!($uN)]
        #[doc = ", shifting x right by n is equivalent to division of x by 2^n."]
        pub proof fn $name_auto()
            ensures
                forall|x: $uN, shift: $uN|
                    0 <= shift < <$uN>::BITS ==> #[trigger] (x >> shift) == x as nat / pow2(shift as nat),
        {
            assert forall|x: $uN, shift: $uN| 0 <= shift < <$uN>::BITS implies #[trigger] (x >> shift) == x as nat
                / pow2(shift as nat) by {
                $name(x, shift);
            }
        }
        }
    };
}

lemma_shr_is_div!(lemma_u64_shr_is_div, lemma_u64_shr_is_div_auto, u64);
lemma_shr_is_div!(lemma_u32_shr_is_div, lemma_u32_shr_is_div_auto, u32);
lemma_shr_is_div!(lemma_u16_shr_is_div, lemma_u16_shr_is_div_auto, u16);
lemma_shr_is_div!(lemma_u8_shr_is_div, lemma_u8_shr_is_div_auto, u8);

// Proofs that a given power of 2 fits in an unsigned type.
macro_rules! lemma_pow2_no_overflow {
    ($name:ident, $name_auto:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "Proof that 2^n does not overflow "]
        #[doc = stringify!($uN)]
        #[doc = " for a given exponent n."]
        pub proof fn $name(n: nat)
            requires
                0 <= n < <$uN>::BITS,
            ensures
                pow2(n) <= <$uN>::MAX,
        {
            lemma_pow2_strictly_increases(n, <$uN>::BITS as nat);
            lemma2_to64();
        }

        #[doc = "Proof that 2^n does not overflow "]
        #[doc = stringify!($uN)]
        #[doc = " for all exponents in bounds."]
        pub proof fn $name_auto()
            ensures
                forall|n: nat| 0 <= n < <$uN>::BITS ==> #[trigger] pow2(n) <= <$uN>::MAX,
        {
            assert forall|n: nat| 0 <= n < <$uN>::BITS implies #[trigger] pow2(n) <= <$uN>::MAX by {
                $name(n);
            }
        }
        }
    };
}

lemma_pow2_no_overflow!(lemma_u64_pow2_no_overflow, lemma_u64_pow2_no_overflow_auto, u64);
lemma_pow2_no_overflow!(lemma_u32_pow2_no_overflow, lemma_u32_pow2_no_overflow_auto, u32);
lemma_pow2_no_overflow!(lemma_u16_pow2_no_overflow, lemma_u16_pow2_no_overflow_auto, u16);
lemma_pow2_no_overflow!(lemma_u8_pow2_no_overflow, lemma_u8_pow2_no_overflow_auto, u8);

// Proofs that shift left is equivalent to multiplication by power of 2.
macro_rules! lemma_shl_is_mul {
    ($name:ident, $name_auto:ident, $no_overflow:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "Proof that for given x and n of type "]
        #[doc = stringify!($uN)]
        #[doc = ", shifting x left by n is equivalent to multiplication of x by 2^n (provided no overflow)."]
        pub proof fn $name(x: $uN, shift: $uN)
            requires
                0 <= shift < <$uN>::BITS,
                x * pow2(shift as nat) <= <$uN>::MAX,
            ensures
                x << shift == x * pow2(shift as nat),
            decreases shift,
        {
            $no_overflow(shift as nat);
            if shift == 0 {
                assert(x << 0 == x) by (bit_vector);
                assert(pow2(0) == 1) by (compute_only);
            } else {
                assert(x << shift == mul(x << ((sub(shift, 1)) as $uN), 2)) by (bit_vector)
                    requires
                        0 < shift < <$uN>::BITS,
                ;
                assert((x << (sub(shift, 1) as $uN)) == x * pow2(sub(shift, 1) as nat)) by {
                    lemma_pow2_strictly_increases((shift - 1) as nat, shift as nat);
                    lemma_mul_inequality(
                        pow2((shift - 1) as nat) as int,
                        pow2(shift as nat) as int,
                        x as int,
                    );
                    lemma_mul_is_commutative(x as int, pow2((shift - 1) as nat) as int);
                    lemma_mul_is_commutative(x as int, pow2(shift as nat) as int);
                    $name(x, (shift - 1) as $uN);
                }
                calc!{ (==)
                    ((x << (sub(shift, 1) as $uN)) * 2);
                        {}
                    ((x * pow2(sub(shift, 1) as nat)) * 2);
                        {
                            lemma_mul_is_associative(x as int, pow2(sub(shift, 1) as nat) as int, 2);
                        }
                    x * ((pow2(sub(shift, 1) as nat)) * 2);
                        {
                            lemma_pow2_adds((shift - 1) as nat, 1);
                            lemma2_to64();
                        }
                    x * pow2(shift as nat);
                }
            }
        }

        #[doc = "Proof that for all x and n of type "]
        #[doc = stringify!($uN)]
        #[doc = ", shifting x left by n is equivalent to multiplication of x by 2^n (provided no overflow)."]
        pub proof fn $name_auto()
            ensures
                forall|x: $uN, shift: $uN|
                    0 <= shift < <$uN>::BITS && x * pow2(shift as nat) <= <$uN>::MAX ==> #[trigger] (x << shift)
                        == x * pow2(shift as nat),
        {
            assert forall|x: $uN, shift: $uN|
                0 <= shift < <$uN>::BITS && x * pow2(shift as nat) <= <$uN>::MAX implies #[trigger] (x << shift)
                == x * pow2(shift as nat) by {
                $name(x, shift);
            }
        }
        }
    };
}

lemma_shl_is_mul!(lemma_u64_shl_is_mul, lemma_u64_shl_is_mul_auto, lemma_u64_pow2_no_overflow, u64);
lemma_shl_is_mul!(lemma_u32_shl_is_mul, lemma_u32_shl_is_mul_auto, lemma_u32_pow2_no_overflow, u32);
lemma_shl_is_mul!(lemma_u16_shl_is_mul, lemma_u16_shl_is_mul_auto, lemma_u16_pow2_no_overflow, u16);
lemma_shl_is_mul!(lemma_u8_shl_is_mul, lemma_u8_shl_is_mul_auto, lemma_u8_pow2_no_overflow, u8);
