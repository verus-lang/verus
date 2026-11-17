//! Harnesses for vstd's `char` specifications (`vstd/std_specs/char.rs`) and the UTF-8
//! encoding they rest on (`vstd/utf8.rs`, `encode_scalar`).
//!
//! Each `spec_*` function transcribes the vstd spec function of the same name; each harness
//! checks it against std for every `char`.

#![allow(clippy::all)]

pub fn spec_is_ascii(c: char) -> bool {
    c <= '\u{7F}'
}
pub fn spec_is_ascii_uppercase(c: char) -> bool {
    'A' <= c && c <= 'Z'
}
pub fn spec_is_ascii_lowercase(c: char) -> bool {
    'a' <= c && c <= 'z'
}
pub fn spec_is_ascii_alphabetic(c: char) -> bool {
    spec_is_ascii_uppercase(c) || spec_is_ascii_lowercase(c)
}
pub fn spec_is_ascii_digit(c: char) -> bool {
    '0' <= c && c <= '9'
}
pub fn spec_is_ascii_alphanumeric(c: char) -> bool {
    spec_is_ascii_uppercase(c) || spec_is_ascii_lowercase(c) || spec_is_ascii_digit(c)
}
pub fn spec_is_ascii_hexdigit(c: char) -> bool {
    ('0' <= c && c <= '9') || ('A' <= c && c <= 'F') || ('a' <= c && c <= 'f')
}
pub fn spec_is_ascii_punctuation(c: char) -> bool {
    ('!' <= c && c <= '/')
        || (':' <= c && c <= '@')
        || ('[' <= c && c <= '`')
        || ('{' <= c && c <= '~')
}
pub fn spec_is_ascii_graphic(c: char) -> bool {
    '!' <= c && c <= '~'
}
pub fn spec_is_ascii_whitespace(c: char) -> bool {
    c == '\u{9}' || c == '\u{A}' || c == '\u{C}' || c == '\u{D}' || c == '\u{20}'
}
pub fn spec_is_ascii_control(c: char) -> bool {
    ('\u{0}' <= c && c <= '\u{1F}') || c == '\u{7F}'
}
pub fn spec_to_ascii_uppercase(c: char) -> char {
    if spec_is_ascii_lowercase(c) {
        char::from_u32(c as u32 - 32).unwrap()
    } else {
        c
    }
}
pub fn spec_to_ascii_lowercase(c: char) -> char {
    if spec_is_ascii_uppercase(c) {
        char::from_u32(c as u32 + 32).unwrap()
    } else {
        c
    }
}

/// `is_white_space` (Unicode's `White_Space` property), the spec of `char::is_whitespace`
pub fn spec_is_white_space(c: char) -> bool {
    matches!(
        c,
        '\u{9}'
            | '\u{A}'
            | '\u{B}'
            | '\u{C}'
            | '\u{D}'
            | '\u{20}'
            | '\u{85}'
            | '\u{A0}'
            | '\u{1680}'
            | '\u{2000}'
            | '\u{2001}'
            | '\u{2002}'
            | '\u{2003}'
            | '\u{2004}'
            | '\u{2005}'
            | '\u{2006}'
            | '\u{2007}'
            | '\u{2008}'
            | '\u{2009}'
            | '\u{200A}'
            | '\u{2028}'
            | '\u{2029}'
            | '\u{202F}'
            | '\u{205F}'
            | '\u{3000}'
    )
}

/// `encode_scalar(v)` (`vstd/utf8.rs`): the UTF-8 encoding of a scalar value, as
/// (bytes, length)
pub fn spec_encode_scalar(v: u32) -> ([u8; 4], usize) {
    let last = 0x80 | (v & 0x3F) as u8;
    let second_last = 0x80 | ((v >> 6) & 0x3F) as u8;
    let third_last = 0x80 | ((v >> 12) & 0x3F) as u8;
    if v <= 0x7F {
        ([(v & 0x7F) as u8, 0, 0, 0], 1)
    } else if 0x80 <= v && v <= 0x7FF {
        ([0xC0 | ((v >> 6) & 0x1F) as u8, last, 0, 0], 2)
    } else if 0x800 <= v && v <= 0xFFFF && !(0xD800 <= v && v <= 0xDFFF) {
        ([0xE0 | ((v >> 12) & 0x0F) as u8, second_last, last, 0], 3)
    } else {
        (
            [
                0xF0 | ((v >> 18) & 0x7) as u8,
                third_last,
                second_last,
                last,
            ],
            4,
        )
    }
}

/// Every claim of `std_specs/char.rs` about `c`
pub fn char_specs_hold(c: char) -> bool {
    let (mut up, mut low) = (c, c);
    up.make_ascii_uppercase();
    low.make_ascii_lowercase();
    c.is_ascii() == spec_is_ascii(c)
        && c.is_ascii_uppercase() == spec_is_ascii_uppercase(c)
        && c.is_ascii_lowercase() == spec_is_ascii_lowercase(c)
        && c.is_ascii_alphabetic() == spec_is_ascii_alphabetic(c)
        && c.is_ascii_digit() == spec_is_ascii_digit(c)
        && c.is_ascii_alphanumeric() == spec_is_ascii_alphanumeric(c)
        && c.is_ascii_hexdigit() == spec_is_ascii_hexdigit(c)
        && c.is_ascii_punctuation() == spec_is_ascii_punctuation(c)
        && c.is_ascii_graphic() == spec_is_ascii_graphic(c)
        && c.is_ascii_whitespace() == spec_is_ascii_whitespace(c)
        && c.is_ascii_control() == spec_is_ascii_control(c)
        && c.to_ascii_uppercase() == spec_to_ascii_uppercase(c)
        && c.to_ascii_lowercase() == spec_to_ascii_lowercase(c)
        && up == spec_to_ascii_uppercase(c)
        && low == spec_to_ascii_lowercase(c)
        && c.is_whitespace() == spec_is_white_space(c)
}

/// `char::len_utf8` is `encode_scalar(c as u32).len()`, and std's encoding is
/// `encode_scalar`'s
pub fn utf8_specs_hold(c: char) -> bool {
    let (bytes, len) = spec_encode_scalar(c as u32);
    let mut buf = [0u8; 4];
    let n = c.encode_utf8(&mut buf).len();
    // compare the four bytes one by one (a slice comparison is a loop for Kani)
    c.len_utf8() == len
        && n == len
        && buf[0] == bytes[0]
        && (len < 2 || buf[1] == bytes[1])
        && (len < 3 || buf[2] == bytes[2])
        && (len < 4 || buf[3] == bytes[3])
}

/// `eq_ignore_ascii_case` compares the ASCII lower-case forms
pub fn eq_ignore_ascii_case_spec_holds(c: char, d: char) -> bool {
    c.eq_ignore_ascii_case(&d) == (spec_to_ascii_lowercase(c) == spec_to_ascii_lowercase(d))
}

#[cfg(kani)]
#[kani::proof]
fn char_specs() {
    assert!(char_specs_hold(kani::any()));
}

#[cfg(kani)]
#[kani::proof]
fn char_utf8_encoding() {
    assert!(utf8_specs_hold(kani::any()));
}

#[cfg(kani)]
#[kani::proof]
fn char_eq_ignore_ascii_case() {
    assert!(eq_ignore_ascii_case_spec_holds(kani::any(), kani::any()));
}

#[cfg(test)]
mod tests {
    #[test]
    fn exhaustive_char_specs_match_std() {
        for v in 0..=0x10FFFFu32 {
            if let Some(c) = char::from_u32(v) {
                assert!(super::char_specs_hold(c), "{:?}", c);
                assert!(super::utf8_specs_hold(c), "{:?}", c);
            }
        }
        for c in (0u8..=0x7F)
            .map(char::from)
            .chain(['\u{E9}', '\u{C9}', '\u{1F600}'])
        {
            for d in (0u8..=0x7F).map(char::from) {
                assert!(super::eq_ignore_ascii_case_spec_holds(c, d));
            }
        }
    }
}
