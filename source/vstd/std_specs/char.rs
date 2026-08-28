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

pub assume_specification[ char::is_whitespace ](c: char) -> (res: bool)
    returns
        is_white_space(c),
;

} // verus!
