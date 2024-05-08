use num_bigint::BigInt;
use std::convert::TryFrom;

// "A char is a 'Unicode scalar value', which is any 'Unicode code point'
// other than a surrogate code point. This has a fixed numerical definition:
// code points are in the range 0 to 0x10FFFF, inclusive.
// Surrogate code points, used by UTF-16, are in the range 0xD800 to 0xDFFF."
//
// From https://doc.rust-lang.org/std/primitive.char.html

pub const CHAR_RANGE_1_MIN: u32 = 0;
pub const CHAR_RANGE_1_MAX: u32 = 0xD7FF;

pub const CHAR_RANGE_2_MIN: u32 = 0xE000;
pub const CHAR_RANGE_2_MAX: u32 = char::MAX as u32;

fn valid_unicode_scalar(i: u32) -> bool {
    (CHAR_RANGE_1_MIN <= i && i <= CHAR_RANGE_1_MAX)
        || (CHAR_RANGE_2_MIN <= i && i <= CHAR_RANGE_2_MAX)
}

pub(crate) fn valid_unicode_scalar_bigint(i: &BigInt) -> bool {
    match u32::try_from(i) {
        Ok(x) => valid_unicode_scalar(x),
        Err(_) => false,
    }
}
