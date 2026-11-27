//! Specifications for the ASCII methods on `u8`.
//!
//! These mirror the `char` specifications in [`super::char`], restricted to
//! bytes: each predicate is the corresponding byte range.
use super::super::prelude::*;

verus! {

/// ASCII bytes are `0x00..=0x7F`:
/// <https://doc.rust-lang.org/std/primitive.u8.html#method.is_ascii>.
pub open spec fn u8_is_ascii(b: u8) -> bool {
    b <= 0x7F
}

#[verifier::allow_in_spec]
pub assume_specification[ u8::is_ascii ](b: &u8) -> bool
    returns
        u8_is_ascii(*b),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.is_ascii_uppercase>.
pub open spec fn u8_is_ascii_uppercase(b: u8) -> bool {
    b'A' <= b && b <= b'Z'
}

#[verifier::allow_in_spec]
pub assume_specification[ u8::is_ascii_uppercase ](b: &u8) -> bool
    returns
        u8_is_ascii_uppercase(*b),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.is_ascii_lowercase>.
pub open spec fn u8_is_ascii_lowercase(b: u8) -> bool {
    b'a' <= b && b <= b'z'
}

#[verifier::allow_in_spec]
pub assume_specification[ u8::is_ascii_lowercase ](b: &u8) -> bool
    returns
        u8_is_ascii_lowercase(*b),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.is_ascii_alphabetic>.
pub open spec fn u8_is_ascii_alphabetic(b: u8) -> bool {
    u8_is_ascii_uppercase(b) || u8_is_ascii_lowercase(b)
}

#[verifier::allow_in_spec]
pub assume_specification[ u8::is_ascii_alphabetic ](b: &u8) -> bool
    returns
        u8_is_ascii_alphabetic(*b),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.is_ascii_digit>.
pub open spec fn u8_is_ascii_digit(b: u8) -> bool {
    b'0' <= b && b <= b'9'
}

#[verifier::allow_in_spec]
pub assume_specification[ u8::is_ascii_digit ](b: &u8) -> bool
    returns
        u8_is_ascii_digit(*b),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.is_ascii_alphanumeric>.
pub open spec fn u8_is_ascii_alphanumeric(b: u8) -> bool {
    u8_is_ascii_uppercase(b) || u8_is_ascii_lowercase(b) || u8_is_ascii_digit(b)
}

#[verifier::allow_in_spec]
pub assume_specification[ u8::is_ascii_alphanumeric ](b: &u8) -> bool
    returns
        u8_is_ascii_alphanumeric(*b),
    opens_invariants none
    no_unwind
;

// skip is_ascii_octdigit since it is a nightly-only experimental API.
/// <https://doc.rust-lang.org/std/primitive.u8.html#method.is_ascii_hexdigit>.
pub open spec fn u8_is_ascii_hexdigit(b: u8) -> bool {
    (b'0' <= b && b <= b'9') || (b'A' <= b && b <= b'F') || (b'a' <= b && b <= b'f')
}

#[verifier::allow_in_spec]
pub assume_specification[ u8::is_ascii_hexdigit ](b: &u8) -> bool
    returns
        u8_is_ascii_hexdigit(*b),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.is_ascii_punctuation>.
pub open spec fn u8_is_ascii_punctuation(b: u8) -> bool {
    (b'!' <= b && b <= b'/') || (b':' <= b && b <= b'@') || (b'[' <= b && b <= b'`') || (b'{' <= b
        && b <= b'~')
}

#[verifier::allow_in_spec]
pub assume_specification[ u8::is_ascii_punctuation ](b: &u8) -> bool
    returns
        u8_is_ascii_punctuation(*b),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.is_ascii_graphic>.
pub open spec fn u8_is_ascii_graphic(b: u8) -> bool {
    b'!' <= b && b <= b'~'
}

#[verifier::allow_in_spec]
pub assume_specification[ u8::is_ascii_graphic ](b: &u8) -> bool
    returns
        u8_is_ascii_graphic(*b),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.is_ascii_whitespace>.
/// Like `char::is_ascii_whitespace`, this excludes U+000B VERTICAL TAB.
pub open spec fn u8_is_ascii_whitespace(b: u8) -> bool {
    b == 0x09 || b == 0x0A || b == 0x0C || b == 0x0D || b == 0x20
}

#[verifier::allow_in_spec]
pub assume_specification[ u8::is_ascii_whitespace ](b: &u8) -> bool
    returns
        u8_is_ascii_whitespace(*b),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.is_ascii_control>.
pub open spec fn u8_is_ascii_control(b: u8) -> bool {
    b <= 0x1F || b == 0x7F
}

#[verifier::allow_in_spec]
pub assume_specification[ u8::is_ascii_control ](b: &u8) -> bool
    returns
        u8_is_ascii_control(*b),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.to_ascii_uppercase>.
pub open spec fn u8_to_ascii_uppercase(b: u8) -> u8 {
    if u8_is_ascii_lowercase(b) {
        (b - 32) as u8
    } else {
        b
    }
}

#[verifier::allow_in_spec]
pub assume_specification[ u8::to_ascii_uppercase ](b: &u8) -> u8
    returns
        u8_to_ascii_uppercase(*b),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.to_ascii_lowercase>.
pub open spec fn u8_to_ascii_lowercase(b: u8) -> u8 {
    if u8_is_ascii_uppercase(b) {
        (b + 32) as u8
    } else {
        b
    }
}

#[verifier::allow_in_spec]
pub assume_specification[ u8::to_ascii_lowercase ](b: &u8) -> u8
    returns
        u8_to_ascii_lowercase(*b),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.eq_ignore_ascii_case>.
pub assume_specification[ u8::eq_ignore_ascii_case ](b: &u8, other: &u8) -> bool
    returns
        u8_to_ascii_lowercase(*b) == u8_to_ascii_lowercase(*other),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.make_ascii_uppercase>.
pub assume_specification[ u8::make_ascii_uppercase ](b: &mut u8)
    ensures
        *final(b) == u8_to_ascii_uppercase(*old(b)),
    opens_invariants none
    no_unwind
;

/// <https://doc.rust-lang.org/std/primitive.u8.html#method.make_ascii_lowercase>.
pub assume_specification[ u8::make_ascii_lowercase ](b: &mut u8)
    ensures
        *final(b) == u8_to_ascii_lowercase(*old(b)),
    opens_invariants none
    no_unwind
;

} // verus!
