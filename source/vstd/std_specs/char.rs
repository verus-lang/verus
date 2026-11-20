use super::super::prelude::*;
use super::super::utf8::encode_scalar;

verus! {

/// The byte width of `c`'s UTF-8 encoding, using the same scalar-value
/// boundaries as [`encode_scalar`].
#[verifier::allow_in_spec]
pub assume_specification[ char::len_utf8 ](c: char) -> usize
    returns
        encode_scalar(c as u32).len() as usize,
;

/// Unicode's `White_Space` property:
/// <https://www.unicode.org/reports/tr44/#White_Space>.
pub open spec fn is_white_space(c: char) -> bool {
    c == '\u{9}' || c == '\u{A}' || c == '\u{B}' || c == '\u{C}' || c == '\u{D}' || c == '\u{20}'
        || c == '\u{85}' || c == '\u{A0}' || c == '\u{1680}' || c == '\u{2000}' || c == '\u{2001}'
        || c == '\u{2002}' || c == '\u{2003}' || c == '\u{2004}' || c == '\u{2005}' || c
        == '\u{2006}' || c == '\u{2007}' || c == '\u{2008}' || c == '\u{2009}' || c == '\u{200A}'
        || c == '\u{2028}' || c == '\u{2029}' || c == '\u{202F}' || c == '\u{205F}' || c
        == '\u{3000}'
}

#[verifier::allow_in_spec]
pub assume_specification[ char::is_whitespace ](c: char) -> bool
    returns
        is_white_space(c),
;

/// ASCII characters:
/// <https://www.unicode.org/charts/nameslist/c_0000.html>.
pub open spec fn is_ascii(c: char) -> bool {
    c <= '\u{7F}'
}

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii ](c: &char) -> bool
    returns
        is_ascii(*c),
;

// skip as_ascii, as_ascii_unchecked since they are nightly-only experimental API.
/// Makes a copy of the value in its ASCII upper case equivalent.
/// <https://doc.rust-lang.org/std/primitive.char.html#method.to_ascii_uppercase>/
pub open spec fn to_ascii_uppercase(c: char) -> char {
    if is_ascii_lowercase(c) {
        (c as u32 - 32) as char
    } else {
        c
    }
}

#[verifier::allow_in_spec]
pub assume_specification[ char::to_ascii_uppercase ](c: &char) -> char
    returns
        to_ascii_uppercase(*c),
;

/// Makes a copy of the value in its ASCII lower case equivalent.
/// <https://doc.rust-lang.org/std/primitive.char.html#method.to_ascii_lowercase>.
pub open spec fn to_ascii_lowercase(c: char) -> char {
    if is_ascii_uppercase(c) {
        (c as u32 + 32) as char
    } else {
        c
    }
}

#[verifier::allow_in_spec]
pub assume_specification[ char::to_ascii_lowercase ](c: &char) -> char
    returns
        to_ascii_lowercase(*c),
;

/// ASCII case-insensitive equality property.
/// <https://doc.rust-lang.org/std/primitive.char.html#method.eq_ignore_ascii_case>.
pub assume_specification[ char::eq_ignore_ascii_case ](c: &char, other: &char) -> bool
    returns
        to_ascii_lowercase(*c) == to_ascii_lowercase(*other),
;

/// Converts this type to its ASCII upper case equivalent in-place.
/// <https://doc.rust-lang.org/std/primitive.char.html#method.make_ascii_uppercase>.
pub assume_specification[ char::make_ascii_uppercase ](c: &mut char)
    ensures
        to_ascii_uppercase(*old(c)) == *final(c),
;

pub assume_specification[ char::make_ascii_lowercase ](c: &mut char)
    ensures
        to_ascii_lowercase(*old(c)) == *final(c),
;

/// ASCII alphabetic property
/// <https://www.unicode.org/reports/tr18/#character_ranges>.
pub open spec fn is_ascii_uppercase(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_uppercase ](c: &char) -> bool
    returns
        is_ascii_uppercase(*c),
;

pub open spec fn is_ascii_lowercase(c: char) -> bool {
    'a' <= c && c <= 'z'
}

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_lowercase ](c: &char) -> bool
    returns
        is_ascii_lowercase(*c),
;

pub open spec fn is_ascii_alphabetic(c: char) -> bool {
    is_ascii_uppercase(c) || is_ascii_lowercase(c)
}

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_alphabetic ](c: &char) -> bool
    returns
        is_ascii_alphabetic(*c),
;

/// ASCII alphanumeric property
pub open spec fn is_ascii_digit(c: char) -> bool {
    '0' <= c && c <= '9'
}

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_digit ](c: &char) -> bool
    returns
        is_ascii_digit(*c),
;

pub open spec fn is_ascii_alphanumeric(c: char) -> bool {
    is_ascii_uppercase(c) || is_ascii_lowercase(c) || is_ascii_digit(c)
}

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_alphanumeric ](c: &char) -> bool
    returns
        is_ascii_alphanumeric(*c),
;

// skip is_ascii_octdigit since is is a nightly-only experimental API.
/// ASCII hexadecimal digit property:
/// <https://www.unicode.org/reports/tr18/#Hex_notation>.
pub open spec fn is_ascii_hexdigit(c: char) -> bool {
    ('0' <= c && c <= '9') || ('A' <= c && c <= 'F') || ('a' <= c && c <= 'f')
}

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_hexdigit ](c: &char) -> bool
    returns
        is_ascii_hexdigit(*c),
;

/// ASCII punctuation property
/// <https://www.unicode.org/reports/tr18/#General_Category_Property>.
pub open spec fn is_ascii_punctuation(c: char) -> bool {
    ('!' <= c && c <= '/') || (':' <= c && c <= '@') || ('[' <= c && c <= '`') || ('{' <= c && c
        <= '~')
}

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_punctuation ](c: &char) -> bool
    returns
        is_ascii_punctuation(*c),
;

/// ASCII graphic character property
/// <https://doc.rust-lang.org/std/primitive.char.html#method.is_ascii_graphic>/
pub open spec fn is_ascii_graphic(c: char) -> bool {
    '!' <= c && c <= '~'
}

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_graphic ](c: &char) -> bool
    returns
        is_ascii_graphic(*c),
;

pub open spec fn is_ascii_whitespace(c: char) -> bool {
    c == '\u{9}' || c == '\u{A}' || c == '\u{C}' || c == '\u{D}' || c == '\u{20}'
}

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_whitespace ](c: &char) -> bool
    returns
        is_ascii_whitespace(*c),
;

pub open spec fn is_ascii_control(c: char) -> bool {
    ('\u{0}' <= c && c <= '\u{1F}') || c == '\u{7F}'
}

#[verifier::allow_in_spec]
pub assume_specification[ char::is_ascii_control ](c: &char) -> bool
    returns
        is_ascii_control(*c),
;

} // verus!
