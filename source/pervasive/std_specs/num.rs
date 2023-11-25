#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::prelude::*;

macro_rules! num_specs {
    ($uN: ty, $iN: ty, $modname_u:ident, $modname_i:ident, $range:expr) => {
        verus!{

        // Unsigned ints (u8, u16, etc.)

        // Put in separate module to avoid name collisions.
        // Names don't matter - the user uses the stdlib functions.
        mod $modname_u {
            use super::*;

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
        }

        // Signed ints (i8, i16, etc.)

        mod $modname_i {
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
        }

        }
    }
}

num_specs!(u8, i8, u8_specs, i8_specs, 0x100);
num_specs!(u16, i16, u16_specs, i16_specs, 0x1_0000);
num_specs!(u32, i32, u32_specs, i32_specs, 0x1_0000_0000);
num_specs!(u64, i64, u64_specs, i64_specs, 0x1_0000_0000_0000_0000);
num_specs!(u128, i128, u128_specs, i128_specs, 0x1_0000_0000_0000_0000_0000_0000_0000_0000);
num_specs!(usize, isize, usize_specs, isize_specs, (usize::MAX - usize::MIN + 1));

verus!{

// == u32 methods ==

#[verifier::external_fn_specification]
pub fn ex_u32_checked_add(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        lhs + rhs > u32::MAX ==> result.is_None(),
        lhs + rhs <= u32::MAX ==> result == Some((lhs + rhs) as u32)
{
    lhs.checked_add(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_add_signed(lhs: u32, rhs: i32) -> (result: Option<u32>)
    ensures
        lhs + rhs > u32::MAX || lhs + rhs < 0 ==> result.is_None(),
        lhs + rhs <= u32::MAX ==> result == Some((lhs + rhs) as u32)
{
    lhs.checked_add_signed(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_sub(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        lhs - rhs < 0 ==> result.is_None(),
        lhs - rhs >= 0 ==> result == Some((lhs - rhs) as u32)
{
    lhs.checked_sub(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_mul(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        lhs * rhs > u32::MAX ==> result.is_None(),
        lhs * rhs <= u32::MAX ==> result == Some((lhs * rhs) as u32)
{
    lhs.checked_mul(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_div(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> result == Some((lhs / rhs) as u32)
{
    lhs.checked_div(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_div_euclid(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> result == Some((lhs / rhs) as u32)
{
    lhs.checked_div_euclid(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_rem(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> result == Some((lhs % rhs) as u32)
{
    lhs.checked_rem(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_rem_euclid(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> result == Some((lhs % rhs) as u32)
{
    lhs.checked_rem_euclid(rhs)
}

// == i32 methods ==

#[verifier::external_fn_specification]
pub fn ex_i32_checked_add(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures 
        lhs + rhs > i32::MAX || lhs + rhs < i32::MIN ==> result.is_None(),
        i32::MIN <= lhs + rhs <= i32::MAX ==> result == Some((lhs + rhs) as i32)
{
    lhs.checked_add(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_add_unsigned(lhs: i32, rhs: u32) -> (result: Option<i32>)
    ensures 
        lhs + rhs > i32::MAX ==> result.is_None(),
        lhs + rhs <= i32::MAX ==> result == Some((lhs + rhs) as i32)
{
    lhs.checked_add_unsigned(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_sub(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures 
        lhs - rhs > i32::MAX || lhs - rhs < i32::MIN ==> result.is_None(),
        i32::MIN <= lhs - rhs <= i32::MAX ==> result == Some((lhs - rhs) as i32)
{
    lhs.checked_sub(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_sub_unsigned(lhs: i32, rhs: u32) -> (result: Option<i32>)
    ensures
        lhs - rhs < i32::MIN ==> result.is_None(),
        i32::MIN <= lhs - rhs ==> result == Some((lhs - rhs) as i32)
{
    lhs.checked_sub_unsigned(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_mul(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures 
        lhs * rhs < i32::MIN || lhs * rhs > i32::MAX ==> result.is_None(),
        i32::MIN <= lhs * rhs <= i32::MAX ==> result == Some((lhs * rhs) as i32)
{
    lhs.checked_mul(rhs)
}

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
            } else { // d < 0
                (x / (d * -1)) * -1
            };
            if output < i32::MIN || output > i32::MAX {
                result.is_None()
            } else {
                result == Some(output as i32)
            }
        })
{
    lhs.checked_div(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_div_euclid(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        rhs == 0 ==> result.is_None(), 
        lhs / rhs < i32::MIN || lhs / rhs > i32::MAX ==> result.is_None(),
        i32::MIN <= lhs / rhs <= i32::MAX ==> result == Some((lhs / rhs) as i32)
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
            let output = if x == 0  {
                0
            } else if x > 0 && d > 0 {
                x % d
            } else if x < 0 && d < 0 {
                ((x * -1) % (d * -1)) * -1
            } else if x < 0 {
                ((x * -1) % d) * -1
            } else { // d < 0
                x % (d * -1)
            };
            if output < i32::MIN || output > i32::MAX {
                result.is_None()
            } else {
                result == Some(output as i32)
            }
        })
{
    lhs.checked_rem(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_rem_euclid(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures 
        rhs == 0 ==> result.is_None(),
        lhs % rhs < i32::MIN || lhs % rhs > i32::MAX ==> result.is_None(),
        i32::MIN <= lhs % rhs <= i32::MAX ==> result == Some((lhs % rhs) as i32)
{
    lhs.checked_rem_euclid(rhs)
}

} // verus!
