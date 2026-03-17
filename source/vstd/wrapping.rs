//! Contains trusted specifications for wrapping arithmetic behavior on the
//! primitive integer types.
//!
//! Structured as follows:
//! To get the spec for `wrapping_add` on `u8`, for example, call `u8_specs::wrapping_add`.
//! (The module formulation seemed cleaner than defining a `wrapping_add_u8` for every
//! operation and type.)
use super::arithmetic::power2::pow2;
use super::layout::unsigned_int_max_values;
use super::prelude::*;

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

                pub broadcast proof fn wrapping_equiv(x: $uN, y: $uN)
                    ensures
                        #![trigger wrapping_add(x, y)]
                        #![trigger wrapping_sub(x, y)]
                        #![trigger wrapping_mul(x, y)]
                        wrapping_add(x, y) == (x + y) % pow2($uN::BITS as nat) as int,
                        wrapping_sub(x, y) == (x - y) % pow2($uN::BITS as nat) as int,
                        wrapping_mul(x, y) == (x * y) % pow2($uN::BITS as nat) as int,
                {
                    unsigned_int_max_values();
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

pub broadcast group group_wrapping_equiv {
    u8_specs::wrapping_equiv,
    u16_specs::wrapping_equiv,
    u32_specs::wrapping_equiv,
    u64_specs::wrapping_equiv,
    u128_specs::wrapping_equiv,
    usize_specs::wrapping_equiv,
}

} // verus!
