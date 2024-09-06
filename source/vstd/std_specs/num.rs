#![allow(unused_imports)]
use super::super::prelude::*;

macro_rules! num_specs {
    ($uN: ty, $iN: ty, $modname_u:ident, $modname_i:ident, $range:expr) => {
        verus! {

        // Unsigned ints (u8, u16, etc.)

        // Put in separate module to avoid name collisions.
        // Names don't matter - the user uses the stdlib functions.
        mod $modname_u {
            use super::*;

            #[verifier::external_fn_specification]
            pub fn ex_num_clone(x: &$uN) -> (res: $uN)
                ensures res == x,
            {
                x.clone()
            }

            pub open spec fn wrapping_add(x: $uN, y: $uN) -> $uN {
                if x + y > <$uN>::MAX {
                    (x + y - $range) as $uN
                } else {
                    (x + y) as $uN
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_add)]
            pub fn ex_wrapping_add(x: $uN, y: $uN) -> (res: $uN)
                ensures res == wrapping_add(x, y)
            {
                x.wrapping_add(y)
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

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_add_signed)]
            pub fn ex_wrapping_add_signed(x: $uN, y: $iN) -> (res: $uN)
                ensures res == wrapping_add_signed(x, y)
            {
                x.wrapping_add_signed(y)
            }

            pub open spec fn wrapping_sub(x: $uN, y: $uN) -> $uN {
                if x - y < 0 {
                    (x - y + $range) as $uN
                } else {
                    (x - y) as $uN
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_sub)]
            pub fn ex_wrapping_sub(x: $uN, y: $uN) -> (res: $uN)
                ensures res == wrapping_sub(x, y)
            {
                x.wrapping_sub(y)
            }

            pub open spec fn checked_add(x: $uN, y: $uN) -> Option<$uN> {
                if x + y > <$uN>::MAX {
                    None
                } else {
                    Some((x + y) as $uN)
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(checked_add)]
            pub fn ex_checked_add(x: $uN, y: $uN) -> (res: Option<$uN>)
                ensures res == checked_add(x, y)
            {
                x.checked_add(y)
            }

            pub open spec fn checked_add_signed(x: $uN, y: $iN) -> Option<$uN> {
                if x + y > <$uN>::MAX || x + y < 0 {
                    None
                } else {
                    Some((x + y) as $uN)
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(checked_add_signed)]
            pub fn ex_checked_add_signed(x: $uN, y: $iN) -> (res: Option<$uN>)
                ensures res == checked_add_signed(x, y)
            {
                x.checked_add_signed(y)
            }

            pub open spec fn checked_sub(x: $uN, y: $uN) -> Option<$uN> {
                if x - y < 0 {
                    None
                } else {
                    Some((x - y) as $uN)
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(checked_sub)]
            pub fn ex_checked_sub(x: $uN, y: $uN) -> (res: Option<$uN>)
                ensures res == checked_sub(x, y)
            {
                x.checked_sub(y)
            }

            pub open spec fn checked_mul(x: $uN, y: $uN) -> Option<$uN> {
                if x * y > <$uN>::MAX {
                    None
                } else {
                    Some((x * y) as $uN)
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(checked_mul)]
            pub fn ex_checked_mul(lhs: $uN, rhs: $uN) -> (result: Option<$uN>)
                ensures
                    result == checked_mul(lhs, rhs)
            {
                lhs.checked_mul(rhs)
            }

            pub open spec fn checked_div(x: $uN, y: $uN) -> Option<$uN> {
                if y == 0 {
                    None
                } else {
                    Some(x / y)
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(checked_div)]
            pub fn ex_checked_div(lhs: $uN, rhs: $uN) -> (result: Option<$uN>)
                ensures
                    result == checked_div(lhs, rhs)
            {
                lhs.checked_div(rhs)
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(checked_div)]
            pub fn ex_checked_div_euclid(lhs: $uN, rhs: $uN) -> (result: Option<$uN>)
                ensures
                    // checked_div is the same as checked_div_euclid for unsigned ints
                    result == checked_div(lhs, rhs)
            {
                lhs.checked_div_euclid(rhs)
            }


        }

        // Signed ints (i8, i16, etc.)

        mod $modname_i {
            use super::*;

            #[verifier::external_fn_specification]
            pub fn ex_num_clone(x: &$iN) -> (res: $iN)
                ensures res == x,
            {
                x.clone()
            }

            pub open spec fn wrapping_add(x: $iN, y: $iN) -> $iN {
                if x + y > <$iN>::MAX {
                    (x + y - $range) as $iN
                } else if x + y < <$iN>::MIN {
                    (x + y + $range) as $iN
                } else {
                    (x + y) as $iN
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_add)]
            pub fn ex_wrapping_add(x: $iN, y: $iN) -> (res: $iN)
                ensures res == wrapping_add(x, y)
            {
                x.wrapping_add(y)
            }

            pub open spec fn wrapping_add_unsigned(x: $iN, y: $uN) -> $iN {
                if x + y > <$iN>::MAX {
                    (x + y - $range) as $iN
                } else {
                    (x + y) as $iN
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_add_unsigned)]
            pub fn ex_wrapping_add_unsigned(x: $iN, y: $uN) -> (res: $iN)
                ensures res == wrapping_add_unsigned(x, y)
            {
                x.wrapping_add_unsigned(y)
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

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_sub)]
            pub fn ex_wrapping_sub(x: $iN, y: $iN) -> (res: $iN)
                ensures res == wrapping_sub(x, y)
            {
                x.wrapping_sub(y)
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

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_mul)]
            pub fn ex_wrapping_mul(x: $iN, y: $iN) -> (res: $iN)
                ensures res == wrapping_mul(x, y)
            {
                x.wrapping_mul(y)
            }

            pub open spec fn checked_add(x: $iN, y: $iN) -> Option<$iN> {
                if x + y > <$iN>::MAX || x + y < <$iN>::MIN {
                    None
                } else {
                    Some((x + y) as $iN)
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(checked_add)]
            pub fn ex_checked_add(x: $iN, y: $iN) -> (res: Option<$iN>)
                ensures res == checked_add(x, y)
            {
                x.checked_add(y)
            }

            pub open spec fn checked_add_unsigned(x: $iN, y: $uN) -> Option<$iN> {
                if x + y > <$iN>::MAX {
                    None
                } else {
                    Some((x + y) as $iN)
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(checked_add_unsigned)]
            pub fn ex_checked_add_unsigned(x: $iN, y: $uN) -> (res: Option<$iN>)
                ensures res == checked_add_unsigned(x, y)
            {
                x.checked_add_unsigned(y)
            }

            pub open spec fn checked_sub(x: $iN, y: $iN) -> Option<$iN> {
                if x - y > <$iN>::MAX || x - y < <$iN>::MIN {
                    None
                } else {
                    Some((x - y) as $iN)
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(checked_sub)]
            pub fn ex_checked_sub(x: $iN, y: $iN) -> (res: Option<$iN>)
                ensures res == checked_sub(x, y)
            {
                x.checked_sub(y)
            }

            pub open spec fn checked_sub_unsigned(x: $iN, y: $uN) -> Option<$iN> {
                if x - y < <$iN>::MIN {
                    None
                } else {
                    Some((x - y) as $iN)
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(checked_sub_unsigned)]
            pub fn ex_checked_sub_unsigned(x: $iN, y: $uN) -> (res: Option<$iN>)
                ensures res == checked_sub_unsigned(x, y)
            {
                x.checked_sub_unsigned(y)
            }

            pub open spec fn checked_mul(x: $iN, y: $iN) -> Option<$iN> {
                if x * y > <$iN>::MAX || x * y < <$iN>::MIN {
                    None
                } else {
                    Some((x * y) as $iN)
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(checked_mul)]
            pub fn ex_checked_mul(x: $iN, y: $iN) -> (res: Option<$iN>)
                ensures res == checked_mul(x, y)
            {
                x.checked_mul(y)
            }
        }

        }
    };
}

num_specs!(u8, i8, u8_specs, i8_specs, 0x100);
num_specs!(u16, i16, u16_specs, i16_specs, 0x1_0000);
num_specs!(u32, i32, u32_specs, i32_specs, 0x1_0000_0000);
num_specs!(u64, i64, u64_specs, i64_specs, 0x1_0000_0000_0000_0000);
num_specs!(u128, i128, u128_specs, i128_specs, 0x1_0000_0000_0000_0000_0000_0000_0000_0000);
num_specs!(usize, isize, usize_specs, isize_specs, (usize::MAX - usize::MIN + 1));

verus! {

// TODO move all these into the num_specs! macro to handle them for other integer widths
// == u32 methods ==
#[verifier::external_fn_specification]
pub fn ex_u32_checked_rem(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> result == Some((lhs % rhs) as u32),
{
    lhs.checked_rem(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_rem_euclid(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> result == Some((lhs % rhs) as u32),
{
    lhs.checked_rem_euclid(rhs)
}

// == i32 methods ==
#[verifier::external_fn_specification]
pub fn ex_i32_checked_div(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        rhs == 0 ==> result.is_None(),
        ({
            let x = lhs as int;
            let d = rhs as int;
            let output = if x == 0 {
                0
            } else if x > 0 && d > 0 {
                x / d
            } else if x < 0 && d < 0 {
                ((x * -1) / (d * -1))
            } else if x < 0 {
                ((x * -1) / d) * -1
            } else {  // d < 0
                (x / (d * -1)) * -1
            };
            if output < i32::MIN || output > i32::MAX {
                result.is_None()
            } else {
                result == Some(output as i32)
            }
        }),
{
    lhs.checked_div(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_div_euclid(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        rhs == 0 ==> result.is_None(),
        lhs / rhs < i32::MIN || lhs / rhs > i32::MAX ==> result.is_None(),
        i32::MIN <= lhs / rhs <= i32::MAX ==> result == Some((lhs / rhs) as i32),
{
    lhs.checked_div_euclid(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_rem(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        rhs == 0 ==> result.is_None(),
        ({
            let x = lhs as int;
            let d = rhs as int;
            let output = if x == 0 {
                0
            } else if x > 0 && d > 0 {
                x % d
            } else if x < 0 && d < 0 {
                ((x * -1) % (d * -1)) * -1
            } else if x < 0 {
                ((x * -1) % d) * -1
            } else {  // d < 0
                x % (d * -1)
            };
            if output < i32::MIN || output > i32::MAX {
                result.is_None()
            } else {
                result == Some(output as i32)
            }
        }),
{
    lhs.checked_rem(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_rem_euclid(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        rhs == 0 ==> result.is_None(),
        lhs % rhs < i32::MIN || lhs % rhs > i32::MAX ==> result.is_None(),
        i32::MIN <= lhs % rhs <= i32::MAX ==> result == Some((lhs % rhs) as i32),
{
    lhs.checked_rem_euclid(rhs)
}

} // verus!
