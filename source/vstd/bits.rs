//! Properties of bitwise operators.
use builtin::*;
use builtin_macros::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::arithmetic::power2::{
    pow2,
    lemma_pow2_unfold,
    lemma_pow2_adds,
    lemma_pow2_pos,
    lemma2_to64,
    lemma_pow2_strictly_increases,
};
#[cfg(verus_keep_ghost)]
use crate::arithmetic::div_mod::{
    lemma_div_denominator,
    lemma_mod_breakdown,
    lemma_mod_multiples_vanish,
};
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

verus! {

/// Mask with low n bits set.
pub open spec fn low_bits_mask(n: nat) -> nat {
    (pow2(n) - 1) as nat
}

/// Proof relating the n-bit mask to a function of the (n-1)-bit mask, for given
/// n.
pub proof fn lemma_low_bits_mask_unfold(n: nat)
    requires
        n > 0,
    ensures
        low_bits_mask(n) == 2 * low_bits_mask((n - 1) as nat) + 1,
{
    calc!{ (==)
        low_bits_mask(n);
            {}
        (pow2(n) - 1) as nat;
            { lemma_pow2_unfold(n); }
        (2*pow2((n-1) as nat) - 1) as nat;
            {}
        (2*(pow2((n-1) as nat) - 1) + 1) as nat;
            { lemma_pow2_pos((n-1) as nat); }
        (2*low_bits_mask((n-1) as nat) + 1) as nat;
    }
}

/// Proof relating the n-bit mask to a function of the (n-1)-bit mask, for all
/// n.
pub proof fn lemma_low_bits_mask_unfold_auto()
    ensures
        forall|n: nat|
            #![trigger low_bits_mask(n)]
            n > 0 ==> low_bits_mask(n) == 2 * low_bits_mask((n - 1) as nat) + 1,
{
    assert forall|n: nat| n > 0 implies #[trigger] low_bits_mask(n) == 2 * low_bits_mask(
        (n - 1) as nat,
    ) + 1 by {
        lemma_low_bits_mask_unfold(n);
    }
}

/// Proof that low_bits_mask(n) is odd, for given n.
pub proof fn lemma_low_bits_mask_is_odd(n: nat)
    requires
        n > 0,
    ensures
        low_bits_mask(n) % 2 == 1,
{
    calc!{ (==)
        low_bits_mask(n) % 2;
            { lemma_low_bits_mask_unfold(n); }
        (2 * low_bits_mask((n-1) as nat) + 1) % 2;
            { lemma_mod_multiples_vanish(low_bits_mask((n-1) as nat) as int, 1, 2); }
        1nat % 2;
    }
}

/// Proof that low_bits_mask(n) is odd, for all n.
pub proof fn lemma_low_bits_mask_is_odd_auto()
    ensures
        forall|n: nat| n > 0 ==> #[trigger] (low_bits_mask(n) % 2) == 1,
{
    assert forall|n: nat| n > 0 implies #[trigger] (low_bits_mask(n) % 2) == 1 by {
        lemma_low_bits_mask_is_odd(n);
    }
}

/// Proof that for given n, dividing the low n bit mask by 2 gives the low n-1
/// bit mask.
pub proof fn lemma_low_bits_mask_div2(n: nat)
    requires
        n > 0,
    ensures
        low_bits_mask(n) / 2 == low_bits_mask((n - 1) as nat),
{
    lemma_low_bits_mask_unfold(n);
}

/// Proof that for all n, dividing the low n bit mask by 2 gives the low n-1
/// bit mask.
pub proof fn lemma_low_bits_mask_div2_auto()
    ensures
        forall|n: nat|
            #![trigger low_bits_mask(n)]
            n > 0 ==> low_bits_mask(n) / 2 == low_bits_mask((n - 1) as nat),
{
    assert forall|n: nat| n > 0 implies #[trigger] low_bits_mask(n) / 2 == low_bits_mask(
        (n - 1) as nat,
    ) by {
        lemma_low_bits_mask_div2(n);
    }
}

/// Proof establishing the concrete values of all masks of bit sizes from 0 to
/// 64.
pub proof fn lemma_low_bits_mask_values_to64()
    ensures
        low_bits_mask(0) == 0x0,
        low_bits_mask(1) == 0x1,
        low_bits_mask(2) == 0x3,
        low_bits_mask(3) == 0x7,
        low_bits_mask(4) == 0xf,
        low_bits_mask(5) == 0x1f,
        low_bits_mask(6) == 0x3f,
        low_bits_mask(7) == 0x7f,
        low_bits_mask(8) == 0xff,
        low_bits_mask(9) == 0x1ff,
        low_bits_mask(10) == 0x3ff,
        low_bits_mask(11) == 0x7ff,
        low_bits_mask(12) == 0xfff,
        low_bits_mask(13) == 0x1fff,
        low_bits_mask(14) == 0x3fff,
        low_bits_mask(15) == 0x7fff,
        low_bits_mask(16) == 0xffff,
        low_bits_mask(17) == 0x1ffff,
        low_bits_mask(18) == 0x3ffff,
        low_bits_mask(19) == 0x7ffff,
        low_bits_mask(20) == 0xfffff,
        low_bits_mask(21) == 0x1fffff,
        low_bits_mask(22) == 0x3fffff,
        low_bits_mask(23) == 0x7fffff,
        low_bits_mask(24) == 0xffffff,
        low_bits_mask(25) == 0x1ffffff,
        low_bits_mask(26) == 0x3ffffff,
        low_bits_mask(27) == 0x7ffffff,
        low_bits_mask(28) == 0xfffffff,
        low_bits_mask(29) == 0x1fffffff,
        low_bits_mask(30) == 0x3fffffff,
        low_bits_mask(31) == 0x7fffffff,
        low_bits_mask(32) == 0xffffffff,
        low_bits_mask(33) == 0x1ffffffff,
        low_bits_mask(34) == 0x3ffffffff,
        low_bits_mask(35) == 0x7ffffffff,
        low_bits_mask(36) == 0xfffffffff,
        low_bits_mask(37) == 0x1fffffffff,
        low_bits_mask(38) == 0x3fffffffff,
        low_bits_mask(39) == 0x7fffffffff,
        low_bits_mask(40) == 0xffffffffff,
        low_bits_mask(41) == 0x1ffffffffff,
        low_bits_mask(42) == 0x3ffffffffff,
        low_bits_mask(43) == 0x7ffffffffff,
        low_bits_mask(44) == 0xfffffffffff,
        low_bits_mask(45) == 0x1fffffffffff,
        low_bits_mask(46) == 0x3fffffffffff,
        low_bits_mask(47) == 0x7fffffffffff,
        low_bits_mask(48) == 0xffffffffffff,
        low_bits_mask(49) == 0x1ffffffffffff,
        low_bits_mask(50) == 0x3ffffffffffff,
        low_bits_mask(51) == 0x7ffffffffffff,
        low_bits_mask(52) == 0xfffffffffffff,
        low_bits_mask(53) == 0x1fffffffffffff,
        low_bits_mask(54) == 0x3fffffffffffff,
        low_bits_mask(55) == 0x7fffffffffffff,
        low_bits_mask(56) == 0xffffffffffffff,
        low_bits_mask(57) == 0x1ffffffffffffff,
        low_bits_mask(58) == 0x3ffffffffffffff,
        low_bits_mask(59) == 0x7ffffffffffffff,
        low_bits_mask(60) == 0xfffffffffffffff,
        low_bits_mask(61) == 0x1fffffffffffffff,
        low_bits_mask(62) == 0x3fffffffffffffff,
        low_bits_mask(63) == 0x7fffffffffffffff,
        low_bits_mask(64) == 0xffffffffffffffff,
{
    reveal(pow2);
    #[verusfmt::skip]
    assert(
        low_bits_mask(0) == 0x0 &&
        low_bits_mask(1) == 0x1 &&
        low_bits_mask(2) == 0x3 &&
        low_bits_mask(3) == 0x7 &&
        low_bits_mask(4) == 0xf &&
        low_bits_mask(5) == 0x1f &&
        low_bits_mask(6) == 0x3f &&
        low_bits_mask(7) == 0x7f &&
        low_bits_mask(8) == 0xff &&
        low_bits_mask(9) == 0x1ff &&
        low_bits_mask(10) == 0x3ff &&
        low_bits_mask(11) == 0x7ff &&
        low_bits_mask(12) == 0xfff &&
        low_bits_mask(13) == 0x1fff &&
        low_bits_mask(14) == 0x3fff &&
        low_bits_mask(15) == 0x7fff &&
        low_bits_mask(16) == 0xffff &&
        low_bits_mask(17) == 0x1ffff &&
        low_bits_mask(18) == 0x3ffff &&
        low_bits_mask(19) == 0x7ffff &&
        low_bits_mask(20) == 0xfffff &&
        low_bits_mask(21) == 0x1fffff &&
        low_bits_mask(22) == 0x3fffff &&
        low_bits_mask(23) == 0x7fffff &&
        low_bits_mask(24) == 0xffffff &&
        low_bits_mask(25) == 0x1ffffff &&
        low_bits_mask(26) == 0x3ffffff &&
        low_bits_mask(27) == 0x7ffffff &&
        low_bits_mask(28) == 0xfffffff &&
        low_bits_mask(29) == 0x1fffffff &&
        low_bits_mask(30) == 0x3fffffff &&
        low_bits_mask(31) == 0x7fffffff &&
        low_bits_mask(32) == 0xffffffff &&
        low_bits_mask(33) == 0x1ffffffff &&
        low_bits_mask(34) == 0x3ffffffff &&
        low_bits_mask(35) == 0x7ffffffff &&
        low_bits_mask(36) == 0xfffffffff &&
        low_bits_mask(37) == 0x1fffffffff &&
        low_bits_mask(38) == 0x3fffffffff &&
        low_bits_mask(39) == 0x7fffffffff &&
        low_bits_mask(40) == 0xffffffffff &&
        low_bits_mask(41) == 0x1ffffffffff &&
        low_bits_mask(42) == 0x3ffffffffff &&
        low_bits_mask(43) == 0x7ffffffffff &&
        low_bits_mask(44) == 0xfffffffffff &&
        low_bits_mask(45) == 0x1fffffffffff &&
        low_bits_mask(46) == 0x3fffffffffff &&
        low_bits_mask(47) == 0x7fffffffffff &&
        low_bits_mask(48) == 0xffffffffffff &&
        low_bits_mask(49) == 0x1ffffffffffff &&
        low_bits_mask(50) == 0x3ffffffffffff &&
        low_bits_mask(51) == 0x7ffffffffffff &&
        low_bits_mask(52) == 0xfffffffffffff &&
        low_bits_mask(53) == 0x1fffffffffffff &&
        low_bits_mask(54) == 0x3fffffffffffff &&
        low_bits_mask(55) == 0x7fffffffffffff &&
        low_bits_mask(56) == 0xffffffffffffff &&
        low_bits_mask(57) == 0x1ffffffffffffff &&
        low_bits_mask(58) == 0x3ffffffffffffff &&
        low_bits_mask(59) == 0x7ffffffffffffff &&
        low_bits_mask(60) == 0xfffffffffffffff &&
        low_bits_mask(61) == 0x1fffffffffffffff &&
        low_bits_mask(62) == 0x3fffffffffffffff &&
        low_bits_mask(63) == 0x7fffffffffffffff &&
        low_bits_mask(64) == 0xffffffffffffffff
    ) by (compute_only);
}

} // verus!
// Proofs that and with mask is equivalent to modulo with power of two.
macro_rules! lemma_low_bits_mask_is_mod {
    ($name:ident, $name_auto:ident, $and_split_low_bit:ident, $no_overflow:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "Proof that for given natural n and x of type "]
        #[doc = stringify!($uN)]
        #[doc = ", and with the low n-bit mask is equivalent to modulo 2^n."]
        pub proof fn $name(x: $uN, n: nat)
            requires
                n < <$uN>::BITS,
            ensures
                x & (low_bits_mask(n) as $uN) == x % (pow2(n) as $uN),
            decreases n,
        {
            // Bounds.
            $no_overflow(n);
            lemma_pow2_pos(n);

            // Inductive proof.
            if n == 0 {
                assert(low_bits_mask(0) == 0) by (compute_only);
                assert(x & 0 == 0) by (bit_vector);
                assert(pow2(0) == 1) by (compute_only);
                assert(x % 1 == 0);
            } else {
                lemma_pow2_unfold(n);
                assert((x % 2) == ((x % 2) & 1)) by (bit_vector);
                calc!{ (==)
                    x % (pow2(n) as $uN);
                        {}
                    x % ((2 * pow2((n-1) as nat)) as $uN);
                        {
                            lemma_pow2_pos((n-1) as nat);
                            lemma_mod_breakdown(x as int, 2, pow2((n-1) as nat) as int);
                        }
                    add(mul(2, (x / 2) % (pow2((n-1) as nat) as $uN)), x % 2);
                        {
                            $name(x/2, (n-1) as nat);
                        }
                    add(mul(2, (x / 2) & (low_bits_mask((n-1) as nat) as $uN)), x % 2);
                        {
                            lemma_low_bits_mask_div2(n);
                        }
                    add(mul(2, (x / 2) & (low_bits_mask(n) as $uN / 2)), x % 2);
                        {
                            lemma_low_bits_mask_is_odd(n);
                        }
                    add(mul(2, (x / 2) & (low_bits_mask(n) as $uN / 2)), (x % 2) & ((low_bits_mask(n) as $uN) % 2));
                        {
                            $and_split_low_bit(x as $uN, low_bits_mask(n) as $uN);
                        }
                    x & (low_bits_mask(n) as $uN)
                }
            }
        }

        #[doc = "Proof that for all natural n and x of type "]
        #[doc = stringify!($uN)]
        #[doc = ", and with the low n-bit mask is equivalent to modulo 2^n."]
        pub proof fn $name_auto()
            ensures
                forall|x: $uN, n: nat| n < <$uN>::BITS ==> #[trigger] (x & (low_bits_mask(n) as $uN)) == (x % (pow2(n) as $uN)),
        {
            assert forall|x: $uN, n: nat| n < <$uN>::BITS implies #[trigger] (x & (low_bits_mask(n) as $uN)) == (x % (pow2(n) as $uN)) by {
                $name(x, n);
            }
        }

        // Helper lemma breaking an and operation into the low bit and the rest.
        proof fn $and_split_low_bit(x: $uN, m: $uN)
            by (bit_vector)
            ensures
                x & m == add(mul(((x / 2) & (m / 2)), 2), (x % 2) & (m % 2)),
        {
        }
        }
    };
}

lemma_low_bits_mask_is_mod!(
    lemma_u64_low_bits_mask_is_mod,
    lemma_u64_low_bits_mask_is_mod_auto,
    lemma_u64_and_split_low_bit,
    lemma_u64_pow2_no_overflow,
    u64
);
lemma_low_bits_mask_is_mod!(
    lemma_u32_low_bits_mask_is_mod,
    lemma_u32_low_bits_mask_is_mod_auto,
    lemma_u32_and_split_low_bit,
    lemma_u32_pow2_no_overflow,
    u32
);
lemma_low_bits_mask_is_mod!(
    lemma_u16_low_bits_mask_is_mod,
    lemma_u16_low_bits_mask_is_mod_auto,
    lemma_u16_and_split_low_bit,
    lemma_u16_pow2_no_overflow,
    u16
);
lemma_low_bits_mask_is_mod!(
    lemma_u8_low_bits_mask_is_mod,
    lemma_u8_low_bits_mask_is_mod_auto,
    lemma_u8_and_split_low_bit,
    lemma_u8_pow2_no_overflow,
    u8
);
