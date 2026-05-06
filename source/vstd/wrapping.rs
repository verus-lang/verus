//! Contains trusted specifications for wrapping arithmetic behavior on the
//! primitive integer types.
//!
//! Structured as follows:
//! To get the spec for `wrapping_add` on `u8`, for example, call `u8_specs::wrapping_add`.
//! (The module formulation seemed cleaner than defining a `wrapping_add_u8` for every
//! operation and type.)
use super::prelude::*;
use super::arithmetic::power2::is_pow2;

macro_rules! wrapping_specs {
    ([$(($uN: ty, $iN: ty, $modname_u:ident, $modname_i:ident, $range:expr),)*]) => {
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
                    // decreases x,
                {
                    assume(false);
                    // use super::super::arithmetic::power2::is_pow2;
                    // reveal(is_pow2);
                    // if x == 0 {
                    // } else if x == 1 {
                    // } else {
                    //     lemma_count_ones_is_pow2(x / 2);
                    //     if x % 2 == 1 {
                    //         lemma_count_ones_pos(x / 2);
                    //     }
                    // }

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
            }

            }
            )*

    }
}

wrapping_specs!([
    (u8, i8, u8_specs, i8_specs, 0x100),
    (u16, i16, u16_specs, i16_specs, 0x1_0000),
    (u32, i32, u32_specs, i32_specs, 0x1_0000_0000),
    (u64, i64, u64_specs, i64_specs, 0x1_0000_0000_0000_0000),
    (u128, i128, u128_specs, i128_specs, 0x1_0000_0000_0000_0000_0000_0000_0000_0000),
    (usize, isize, usize_specs, isize_specs, (usize::MAX - usize::MIN + 1)),
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
