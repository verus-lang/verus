//! Contains trusted specifications for wrapping arithmetic behavior on the
//! primitive integer types.
//!
//! Structured as follows:
//! To get the spec for `wrapping_add` on `u8`, for example, call `u8_specs::wrapping_add`.
//! (The module formulation seemed cleaner than defining a `wrapping_add_u8` for every
//! operation and type.)
use super::prelude::*;

macro_rules! wrapping_specs {
    ([$(($uN: ty, $iN: ty, $modname_u:ident, $modname_i:ident, $range:expr, $bits:expr),)*]) => {
        $(
            verus! {

            pub mod $modname_u {
                use super::*;

                pub open spec fn wrapping_add(x: $uN, y: $uN) -> $uN {
                    if x + y > <$uN>::MAX {
                        (x + y - $range) as $uN
                    } else {
                        (x + y) as $uN
                    }
                }

                pub open spec fn wrapping_add_signed(x: $uN, y: $iN) -> $uN {
                    if x + y > <$uN>::MAX {
                        (x + y - $range) as $uN
                    } else if x + y < 0 {
                        (x + y + $range) as $uN
                    } else {
                        (x + y) as $uN
                    }
                }

                pub open spec fn wrapping_sub(x: $uN, y: $uN) -> $uN {
                    if x - y < 0 {
                        (x - y + $range) as $uN
                    } else {
                        (x - y) as $uN
                    }
                }

                pub open spec fn wrapping_mul(x: $uN, y: $uN) -> $uN {
                    ((x as nat * y as nat) % $range as nat) as $uN
                }

                pub open spec fn count_ones(x: $uN) -> nat
                    decreases x,
                {
                    if x == 0 {
                        0
                    } else {
                        (x % 2) as nat + count_ones(x / 2)
                    }
                }

                pub proof fn lemma_count_ones_pos(x: $uN)
                    requires
                        x >= 1,
                    ensures
                        count_ones(x) >= 1,
                    decreases x,
                {
                    if x > 1 && x % 2 == 0 {
                        lemma_count_ones_pos(x / 2);
                    }
                }

                pub broadcast proof fn lemma_count_ones_is_pow2(x: $uN)
                    ensures
                        #![trigger count_ones(x)]
                        #![trigger is_pow2(x as int)]
                        count_ones(x) == 1
                            <==> is_pow2(x as int),
                    decreases x,
                {
                    use super::super::arithmetic::power2::is_pow2;
                    reveal(is_pow2);
                    reveal_with_fuel(count_ones, 2);
                    if x > 1 {
                        assert((x as int) / 2 == (x / 2) as int);
                        if x % 2 == 0 {
                            lemma_count_ones_is_pow2(x / 2);
                        } else {
                            // x is odd and > 1, so x / 2 > 0 contributes at least one more bit
                            lemma_count_ones_pos(x / 2);
                        }
                    }
                }

                pub open spec fn wrapping_shl(x: $uN, shift: u32) -> $uN {
                    x << (shift % $bits)
                }
                pub open spec fn wrapping_shr(x: $uN, shift: u32) -> $uN {
                    x >> (shift % $bits)
                }

                /// The bits of `x` shifted left by `n % BITS`, with the bits shifted out
                /// of the top moved into the bottom. A rotation by zero is `x`; it is a
                /// separate case so that no shift is by the full width.
                pub open spec fn rotate_left(x: $uN, n: u32) -> $uN {
                    let r = n % $bits;
                    if r == 0 {
                        x
                    } else {
                        (x << r) | (x >> (($bits - r) as u32))
                    }
                }

                /// The bits of `x` shifted right by `n % BITS`, with the bits shifted out
                /// of the bottom moved into the top.
                pub open spec fn rotate_right(x: $uN, n: u32) -> $uN {
                    let r = n % $bits;
                    if r == 0 {
                        x
                    } else {
                        (x >> r) | (x << (($bits - r) as u32))
                    }
                }

            }
            pub mod $modname_i {
                use super::*;

                pub open spec fn wrapping_add(x: $iN, y: $iN) -> $iN {
                    if x + y > <$iN>::MAX {
                        (x + y - $range) as $iN
                    } else if x + y < <$iN>::MIN {
                        (x + y + $range) as $iN
                    } else {
                        (x + y) as $iN
                    }
                }

                pub open spec fn wrapping_add_unsigned(x: $iN, y: $uN) -> $iN {
                    if x + y > <$iN>::MAX {
                        (x + y - $range) as $iN
                    } else {
                        (x + y) as $iN
                    }
                }

                pub open spec fn wrapping_sub(x: $iN, y: $iN) -> $iN {
                    if x - y > <$iN>::MAX {
                        (x - y - $range) as $iN
                    } else if x - y < <$iN>::MIN {
                        (x - y + $range) as $iN
                    } else {
                        (x - y) as $iN
                    }
                }

                pub open spec fn signed_crop(x: int) -> $iN {
                    if (x % ($range as int)) > (<$iN>::MAX as int) {
                        ((x % ($range as int)) - $range) as $iN
                    } else {
                        (x % ($range as int)) as $iN
                    }
                }

                pub open spec fn wrapping_mul(x: $iN, y: $iN) -> $iN {
                    signed_crop(x * y)
                }

                pub open spec fn count_ones(x: $iN) -> nat {
                    super::$modname_u::count_ones(x as $uN)
                }

                pub open spec fn wrapping_shl(x: $iN, shift: u32) -> $iN {
                    x << (shift % $bits)
                }
                pub open spec fn wrapping_shr(x: $iN, shift: u32) -> $iN {
                    x >> (shift % $bits)
                }

                /// Rotates the two's-complement bits of `x`, as the unsigned
                /// `rotate_left` does. A rotation by a multiple of `BITS` is `x`
                /// directly, so that case needs no reasoning about the casts.
                pub open spec fn rotate_left(x: $iN, n: u32) -> $iN {
                    if n % $bits == 0 {
                        x
                    } else {
                        $modname_u::rotate_left(x as $uN, n) as $iN
                    }
                }

                /// Rotates the two's-complement bits of `x`, as the unsigned
                /// `rotate_right` does.
                pub open spec fn rotate_right(x: $iN, n: u32) -> $iN {
                    if n % $bits == 0 {
                        x
                    } else {
                        $modname_u::rotate_right(x as $uN, n) as $iN
                    }
                }

            }

            }
            )*
    }
}
wrapping_specs!([
    (u8, i8, u8_specs, i8_specs, 0x100, 8u32),
    (u16, i16, u16_specs, i16_specs, 0x1_0000, 16u32),
    (u32, i32, u32_specs, i32_specs, 0x1_0000_0000, 32u32),
    (u64, i64, u64_specs, i64_specs, 0x1_0000_0000_0000_0000, 64u32),
    (u128, i128, u128_specs, i128_specs, 0x1_0000_0000_0000_0000_0000_0000_0000_0000, 128u32),
    (usize, isize, usize_specs, isize_specs, (usize::MAX - usize::MIN + 1), usize::BITS),
]);

verus! {

pub broadcast group group_count_ones_is_pow2 {
    u8_specs::lemma_count_ones_is_pow2,
    u16_specs::lemma_count_ones_is_pow2,
    u32_specs::lemma_count_ones_is_pow2,
    u64_specs::lemma_count_ones_is_pow2,
    u128_specs::lemma_count_ones_is_pow2,
    usize_specs::lemma_count_ones_is_pow2,
}

} // verus!
