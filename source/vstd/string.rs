#![feature(rustc_attrs)]
#![allow(unused_imports)]

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
use alloc::str::Chars;
#[cfg(all(feature = "alloc", not(verus_verify_core)))]
use alloc::string::{self, String, ToString};

use super::prelude::*;
use super::seq::Seq;
use super::slice::*;
#[cfg(verus_keep_ghost)]
#[cfg(all(feature = "alloc", not(verus_verify_core)))]
use super::std_specs::iter::IteratorSpec;
use super::utf8::*;
use super::view::*;

verus! {

broadcast use {super::seq::group_seq_lemmas, super::slice::group_slice_axioms};

#[cfg(not(verus_verify_core))]
impl View for str {
    type V = Seq<char>;

    uninterp spec fn view(&self) -> Seq<char>;
}

#[cfg(not(verus_verify_core))]
impl DeepView for str {
    type V = Seq<char>;

    open spec fn deep_view(&self) -> Seq<char> {
        self.view()
    }
}

#[cfg(not(verus_verify_core))]
pub trait StringSliceAdditionalSpecFns {
    spec fn spec_bytes(&self) -> Seq<u8>;
}

#[cfg(not(verus_verify_core))]
impl StringSliceAdditionalSpecFns for str {
    open spec fn spec_bytes(&self) -> Seq<u8> {
        encode_utf8(self@)
    }
}

#[cfg(not(verus_verify_core))]
pub open spec fn is_ascii(s: &str) -> bool {
    is_ascii_chars(s@)
}

#[cfg(not(verus_verify_core))]
pub broadcast proof fn is_ascii_spec_bytes(s: &str)
    ensures
        #[trigger] is_ascii(s) ==> #[trigger] s.spec_bytes() =~= Seq::new(
            s@.len(),
            |i| s@.index(i) as u8,
        ),
{
    if (is_ascii(s)) {
        is_ascii_chars_encode_utf8(s@);
    }
}

#[cfg(not(verus_verify_core))]
pub broadcast proof fn is_ascii_concat(s1: &str, s2: &str, s3: &str)
    requires
        s1@ =~= s2@ + s3@,
    ensures
        #![trigger s2@ + s3@, is_ascii(s1), is_ascii(s2), is_ascii(s3)]
        is_ascii(s1) <==> is_ascii(s2) && is_ascii(s3),
{
    broadcast use is_ascii_chars_concat;

    if (is_ascii(s1)) {
        is_ascii_chars_concat(s1@, s2@, s3@);
    }
}

#[cfg(not(verus_verify_core))]
#[verifier::when_used_as_spec(is_ascii)]
pub assume_specification[ str::is_ascii ](s: &str) -> (b: bool)
    ensures
        b == is_ascii(s),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
use crate::alloc::borrow::ToOwned;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ str::to_owned ](s: &str) -> (res: String)
    ensures
        s@ == res@,
;

#[cfg(not(verus_verify_core))]
pub assume_specification[ str::as_bytes ](s: &str) -> (b: &[u8])
    ensures
        b@ == s.spec_bytes(),
;

#[cfg(not(verus_verify_core))]
#[verifier::allow_in_spec]
pub assume_specification[ str::len ](s: &str) -> usize
    returns
        s.spec_bytes().len() as usize,
;

#[cfg(not(verus_verify_core))]
#[verifier::allow_in_spec]
pub assume_specification[ str::is_empty ](s: &str) -> bool
    returns
        s@.len() == 0,
;

#[cfg(not(verus_verify_core))]
#[verifier::allow_in_spec]
pub assume_specification[ str::is_char_boundary ](s: &str, index: usize) -> bool
    returns
        is_char_boundary(s.spec_bytes(), index as int),
;

#[cfg(not(verus_verify_core))]
pub assume_specification[ str::split_at ](s: &str, mid: usize) -> (res: (&str, &str))
    requires
        is_char_boundary(s.spec_bytes(), mid as int),
    ensures
        res.0.spec_bytes() =~= s.spec_bytes().subrange(0, mid as int),
        res.1.spec_bytes() =~= s.spec_bytes().subrange(mid as int, s.spec_bytes().len() as int),
;

/// Specifies `Pattern` for `str::starts_with`/`ends_with`/`contains`/`find`/`rfind`.
/// `matches_at`/`matches_at_bytes` describe which spans a pattern matches;
/// ensures are gated on `obeys_pattern_spec()`, same as `PartialEqSpec`.
///
/// Excludes `FnMut(char) -> bool`: Verus only learns a closure's `ensures()`
/// from an actual traced call, and `str`'s real methods are external, so it
/// never sees the internal call. Predicates keep the hand-written
/// `str_*_pred` wrappers below, whose bodies call the predicate directly.
///
/// Unconditional (not `verus_verify_core`-gated): `#[cfg(...)]` isn't
/// reliably respected on a trait combining external_trait_specification
/// with external_trait_extension, and verifying core needs this registered
/// regardless. `vstd.rs`'s `#![feature(pattern)]` is unconditional too, for
/// the same reason.
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(PatternSpec via PatternSpecImpl)]
pub trait ExPattern: Sized {
    type ExternalTraitSpecificationFor: core::str::pattern::Pattern;

    spec fn obeys_pattern_spec(&self) -> bool;

    /// True iff this pattern instance matches exactly haystack[start..end).
    spec fn matches_at(&self, haystack: Seq<char>, start: int, end: int) -> bool;

    /// Byte-offset sibling of `matches_at`: `find`/`rfind` return byte
    /// offsets, not char positions.
    spec fn matches_at_bytes(&self, haystack: Seq<u8>, start: int, end: int) -> bool;
}

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
impl PatternSpecImpl for char {
    open spec fn obeys_pattern_spec(&self) -> bool {
        true
    }

    open spec fn matches_at(&self, haystack: Seq<char>, start: int, end: int) -> bool {
        0 <= start && end == start + 1 && end <= haystack.len() && haystack[start] == *self
    }

    open spec fn matches_at_bytes(&self, haystack: Seq<u8>, start: int, end: int) -> bool {
        0 <= start && end <= haystack.len() && haystack.subrange(start, end) =~= encode_scalar(
            *self as u32,
        )
    }
}

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
impl<'b> PatternSpecImpl for &'b str {
    open spec fn obeys_pattern_spec(&self) -> bool {
        true
    }

    open spec fn matches_at(&self, haystack: Seq<char>, start: int, end: int) -> bool {
        0 <= start <= end <= haystack.len() && haystack.subrange(start, end) =~= self@
    }

    open spec fn matches_at_bytes(&self, haystack: Seq<u8>, start: int, end: int) -> bool {
        0 <= start <= end <= haystack.len() && haystack.subrange(start, end) =~= self.spec_bytes()
    }
}

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
impl<'b> PatternSpecImpl for &'b [char] {
    open spec fn obeys_pattern_spec(&self) -> bool {
        true
    }

    // `&[char]` matches by set membership of a single char, not by sequence -
    // e.g. `"hello".starts_with(&['h', 'x'])` is true because 'h' is in the set.
    open spec fn matches_at(&self, haystack: Seq<char>, start: int, end: int) -> bool {
        0 <= start < haystack.len() && end == start + 1 && self@.contains(haystack[start])
    }

    open spec fn matches_at_bytes(&self, haystack: Seq<u8>, start: int, end: int) -> bool {
        0 <= start <= end <= haystack.len() && exists|c: char|
            self@.contains(c) && haystack.subrange(start, end) =~= encode_scalar(c as u32)
    }
}

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification<P: core::str::pattern::Pattern>[ str::starts_with::<P> ](
    s: &str,
    pat: P,
) -> (r: bool)
    ensures
        pat.obeys_pattern_spec() ==> r == exists|len: int|
            0 <= len <= s@.len() && pat.matches_at(s@, 0, len),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification<P: core::str::pattern::Pattern>[ str::contains::<P> ](
    s: &str,
    pat: P,
) -> (r: bool)
    ensures
        pat.obeys_pattern_spec() ==> r == exists|i: int, j: int|
            0 <= i <= j <= s@.len() && pat.matches_at(s@, i, j),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
#[verifier::allow(undeclared_external_trait)]
pub assume_specification<P: core::str::pattern::Pattern>[ str::ends_with::<P> ](
    s: &str,
    pat: P,
) -> (r: bool) where for <'a>P::Searcher<'a>: core::str::pattern::ReverseSearcher<'a>
    ensures
        pat.obeys_pattern_spec() ==> r == exists|start: int|
            0 <= start <= s@.len() as int && pat.matches_at(s@, start, s@.len() as int),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification<P: core::str::pattern::Pattern>[ str::find::<P> ](s: &str, pat: P) -> (res:
    Option<usize>)
    ensures
        pat.obeys_pattern_spec() ==> {
            &&& (res is Some) == exists|i: int, j: int|
                0 <= i <= j <= s.spec_bytes().len() as int && pat.matches_at_bytes(
                    s.spec_bytes(),
                    i,
                    j,
                )
            &&& res is Some ==> {
                let i = res.unwrap() as int;
                &&& exists|j: int|
                    i <= j <= s.spec_bytes().len() as int && pat.matches_at_bytes(
                        s.spec_bytes(),
                        i,
                        j,
                    )
                &&& forall|k: int, j: int|
                    0 <= k < i && k <= j <= s.spec_bytes().len() as int ==> !pat.matches_at_bytes(
                        s.spec_bytes(),
                        k,
                        j,
                    )
            }
        },
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
#[verifier::allow(undeclared_external_trait)]
pub assume_specification<P: core::str::pattern::Pattern>[ str::rfind::<P> ](
    s: &str,
    pat: P,
) -> (res: Option<usize>) where for <'a>P::Searcher<'a>: core::str::pattern::ReverseSearcher<'a>
    ensures
        pat.obeys_pattern_spec() ==> {
            &&& (res is Some) == exists|i: int, j: int|
                0 <= i <= j <= s.spec_bytes().len() as int && pat.matches_at_bytes(
                    s.spec_bytes(),
                    i,
                    j,
                )
            &&& res is Some ==> {
                let i = res.unwrap() as int;
                &&& exists|j: int|
                    i <= j <= s.spec_bytes().len() as int && pat.matches_at_bytes(
                        s.spec_bytes(),
                        i,
                        j,
                    )
                &&& forall|k: int, j: int|
                    i < k && k <= j <= s.spec_bytes().len() as int ==> !pat.matches_at_bytes(
                        s.spec_bytes(),
                        k,
                        j,
                    )
            }
        },
;

#[cfg(not(verus_verify_core))]
pub fn str_starts_with_pred<F: Fn(char) -> bool>(s: &str, pred: F) -> (res: bool)
    requires
        s@.len() > 0 ==> pred.requires((s@[0],)),
    ensures
        s@.len() == 0 ==> !res,
        res ==> (s@.len() > 0 && pred.ensures((s@[0],), true)),
        (s@.len() > 0 && !res) ==> pred.ensures((s@[0],), false),
{
    if s.unicode_len() == 0 {
        false
    } else {
        let c = s.get_char(0);
        pred(c)
    }
}

#[cfg(not(verus_verify_core))]
pub fn str_ends_with_pred<F: Fn(char) -> bool>(s: &str, pred: F) -> (res: bool)
    requires
        s@.len() > 0 ==> pred.requires((s@[s@.len() - 1],)),
    ensures
        s@.len() == 0 ==> !res,
        res ==> (s@.len() > 0 && pred.ensures((s@[s@.len() - 1],), true)),
        (s@.len() > 0 && !res) ==> pred.ensures((s@[s@.len() - 1],), false),
{
    let n = s.unicode_len();
    if n == 0 {
        false
    } else {
        let c = s.get_char(n - 1);
        pred(c)
    }
}

#[cfg(not(verus_verify_core))]
pub fn str_contains_pred<F: Fn(char) -> bool>(s: &str, pred: F) -> (res: bool)
    requires
        forall|i: int| 0 <= i < s@.len() ==> pred.requires((#[trigger] s@[i],)),
    ensures
        res ==> exists|i: int| 0 <= i < s@.len() && pred.ensures((#[trigger] s@[i],), true),
        !res ==> forall|i: int| 0 <= i < s@.len() ==> pred.ensures((#[trigger] s@[i],), false),
{
    let n = s.unicode_len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == s@.len(),
            forall|i: int| 0 <= i < s@.len() ==> pred.requires((#[trigger] s@[i],)),
            forall|i: int| 0 <= i < idx ==> pred.ensures((#[trigger] s@[i],), false),
        decreases n - idx,
    {
        let c = s.get_char(idx);
        if pred(c) {
            return true;
        }
        idx += 1;
    }
    false
}

#[cfg(not(verus_verify_core))]
pub fn str_find_pred<F: Fn(char) -> bool>(s: &str, pred: F) -> (res: Option<usize>)
    requires
        forall|i: int| 0 <= i < s@.len() ==> pred.requires((#[trigger] s@[i],)),
    ensures
        res is None ==> forall|i: int|
            0 <= i < s@.len() ==> pred.ensures((#[trigger] s@[i],), false),
        res is Some ==> exists|i: int|
            0 <= i < s@.len() && pred.ensures((#[trigger] s@[i],), true) && res.unwrap() as int
                == encode_utf8(s@.subrange(0, i)).len() && forall|j: int|
                0 <= j < i ==> pred.ensures((#[trigger] s@[j],), false),
{
    let bytes = s.as_bytes();
    let total_bytes = bytes.len();
    proof {
        assert(total_bytes as nat == bytes@.len());
        assert(bytes@ == s.spec_bytes());
        assert(s.spec_bytes() =~= encode_utf8(s@));
    }
    let n = s.unicode_len();
    let mut idx: usize = 0;
    let mut byte_idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == s@.len(),
            total_bytes as nat == s.spec_bytes().len(),
            s.spec_bytes() =~= encode_utf8(s@),
            byte_idx == encode_utf8(s@.subrange(0, idx as int)).len(),
            forall|i: int| 0 <= i < s@.len() ==> pred.requires((#[trigger] s@[i],)),
            forall|i: int| 0 <= i < idx ==> pred.ensures((#[trigger] s@[i],), false),
        decreases n - idx,
    {
        let c = s.get_char(idx);
        if pred(c) {
            return Some(byte_idx);
        }
        let clen = c.len_utf8();
        proof {
            let prefix = s@.subrange(0, idx as int);
            let new_prefix = s@.subrange(0, idx as int + 1);
            let new_suffix = s@.subrange(idx as int + 1, n as int);
            assert(prefix.push(c) =~= new_prefix);
            encode_utf8_push(prefix, c);
            assert(new_prefix + new_suffix == s@) by {
                assert(new_prefix + new_suffix =~= s@);
            }
            encode_utf8_concat(new_prefix, new_suffix);
            assert(byte_idx + clen == encode_utf8(new_prefix).len());
            assert(encode_utf8(new_prefix).len() <= encode_utf8(s@).len());
            assert((byte_idx + clen) as nat <= total_bytes as nat);
        }
        byte_idx = byte_idx + clen;
        idx = idx + 1;
    }
    None
}

#[cfg(not(verus_verify_core))]
pub fn str_rfind_pred<F: Fn(char) -> bool>(s: &str, pred: F) -> (res: Option<usize>)
    requires
        forall|i: int| 0 <= i < s@.len() ==> pred.requires((#[trigger] s@[i],)),
    ensures
        res is None ==> forall|i: int|
            0 <= i < s@.len() ==> pred.ensures((#[trigger] s@[i],), false),
        res is Some ==> exists|i: int|
            0 <= i < s@.len() && pred.ensures((#[trigger] s@[i],), true) && res.unwrap() as int
                == encode_utf8(s@.subrange(0, i)).len() && forall|j: int|
                i < j < s@.len() ==> pred.ensures((#[trigger] s@[j],), false),
{
    let bytes = s.as_bytes();
    let total_bytes = bytes.len();
    proof {
        assert(total_bytes as nat == bytes@.len());
        assert(bytes@ == s.spec_bytes());
        assert(s.spec_bytes() =~= encode_utf8(s@));
    }
    let n = s.unicode_len();
    let mut idx: usize = 0;
    let mut byte_idx: usize = 0;
    let mut found: bool = false;
    let mut found_idx: usize = 0;
    let mut found_byte_idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == s@.len(),
            total_bytes as nat == s.spec_bytes().len(),
            s.spec_bytes() =~= encode_utf8(s@),
            byte_idx == encode_utf8(s@.subrange(0, idx as int)).len(),
            found ==> {
                &&& 0 <= found_idx < idx
                &&& pred.ensures((#[trigger] s@[found_idx as int],), true)
                &&& found_byte_idx as int == encode_utf8(s@.subrange(0, found_idx as int)).len()
                &&& forall|j: int| found_idx < j < idx ==> pred.ensures((#[trigger] s@[j],), false)
            },
            !found ==> forall|i: int| 0 <= i < idx ==> pred.ensures((#[trigger] s@[i],), false),
            forall|i: int| 0 <= i < s@.len() ==> pred.requires((#[trigger] s@[i],)),
        decreases n - idx,
    {
        let c = s.get_char(idx);
        if pred(c) {
            found = true;
            found_idx = idx;
            found_byte_idx = byte_idx;
        }
        let clen = c.len_utf8();
        proof {
            let prefix = s@.subrange(0, idx as int);
            let new_prefix = s@.subrange(0, idx as int + 1);
            let new_suffix = s@.subrange(idx as int + 1, n as int);
            assert(prefix.push(c) =~= new_prefix);
            encode_utf8_push(prefix, c);
            assert(new_prefix + new_suffix == s@) by {
                assert(new_prefix + new_suffix =~= s@);
            }
            encode_utf8_concat(new_prefix, new_suffix);
            assert(byte_idx + clen == encode_utf8(new_prefix).len());
            assert(encode_utf8(new_prefix).len() <= encode_utf8(s@).len());
            assert((byte_idx + clen) as nat <= total_bytes as nat);
        }
        byte_idx = byte_idx + clen;
        idx = idx + 1;
    }
    if found {
        Some(found_byte_idx)
    } else {
        None
    }
}

#[cfg(not(verus_verify_core))]
pub assume_specification[ str::from_utf8_unchecked ](v: &[u8]) -> (res: &str)
    requires
        valid_utf8(v@),
    ensures
        res.spec_bytes() =~= v@,
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub uninterp spec fn to_string_from_display_ensures<T: core::fmt::Display + ?Sized>(
    t: &T,
    s: String,
) -> bool;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub broadcast proof fn to_string_from_display_ensures_for_str(t: &str, res: String)
    ensures
        #[trigger] to_string_from_display_ensures::<str>(t, res) <==> (t@ == res@),
{
    admit();
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification<T: core::fmt::Display + ?Sized>[ <T as ToString>::to_string ](
    t: &T,
) -> (res: String)
    ensures
        to_string_from_display_ensures::<T>(t, res),
;

#[cfg(not(verus_verify_core))]
#[verifier::external]
pub trait StrSliceExecFns {
    fn unicode_len(&self) -> usize;

    fn get_char(&self, i: usize) -> char;

    fn substring_ascii<'a>(&'a self, from: usize, to: usize) -> &'a str;

    fn substring_char<'a>(&'a self, from: usize, to: usize) -> &'a str;

    fn get_ascii(&self, i: usize) -> u8;

    #[cfg(feature = "alloc")]
    fn as_bytes_vec(&self) -> alloc::vec::Vec<u8>;
}

#[cfg(not(verus_verify_core))]
impl StrSliceExecFns for str {
    /// The len() function in rust returns the byte length.
    /// It is more useful to talk about the length of characters and therefore this function was added.
    /// Please note that this function counts the unicode variation selectors as characters.
    /// Warning: O(n)
    #[verifier::external_body]
    fn unicode_len(&self) -> (l: usize)
        ensures
            l as nat == self@.len(),
    {
        self.chars().count()
    }

    /// Warning: O(n) not O(1) due to unicode decoding needed
    #[verifier::external_body]
    fn get_char(&self, i: usize) -> (c: char)
        requires
            i < self@.len(),
        ensures
            self@.index(i as int) == c,
    {
        self.chars().nth(i).unwrap()
    }

    #[verifier::external_body]
    fn substring_ascii<'a>(&'a self, from: usize, to: usize) -> (ret: &'a str)
        requires
            self.is_ascii(),
            from <= to <= self@.len(),
        ensures
            ret@ == self@.subrange(from as int, to as int),
            ret.is_ascii(),
    {
        // Range::index panics if from > to or from > self@.len()
        &self[from..to]
    }

    #[verifier::external_body]
    fn substring_char<'a>(&'a self, from: usize, to: usize) -> (ret: &'a str)
        requires
            from <= to <= self@.len(),
        ensures
            ret@ == self@.subrange(from as int, to as int),
    {
        let mut char_pos = 0;
        let mut byte_start = None;
        let mut byte_end = None;
        let mut byte_pos = 0;
        let mut it = self.chars();
        loop {
            if char_pos == from {
                byte_start = Some(byte_pos);
            }
            if char_pos == to {
                byte_end = Some(byte_pos);
                break;
            }
            if let Some(c) = it.next() {
                char_pos += 1;
                byte_pos += c.len_utf8();
            } else {
                break;
            }
        }
        let byte_start = byte_start.unwrap();
        let byte_end = byte_end.unwrap();
        // Range::index panics if from > to or from > self@.len()
        &self[byte_start..byte_end]
    }

    fn get_ascii(&self, i: usize) -> (b: u8)
        requires
            self.is_ascii(),
            i < self@.len(),
        ensures
            self@.index(i as int) as u8 == b,
    {
        broadcast use is_ascii_spec_bytes;
        // panics if i is not a valid index

        self.as_bytes()[i]
    }

    #[cfg(feature = "alloc")]
    fn as_bytes_vec(&self) -> (ret: alloc::vec::Vec<u8>)
        ensures
            ret@ == self.spec_bytes(),
    {
        slice_to_vec(self.as_bytes())
    }
}

#[cfg(not(verus_verify_core))]
pub broadcast axiom fn axiom_str_literal_len<'a>(s: &'a str)
    ensures
        #[trigger] s@.len() == strslice_len(s),
;

#[cfg(not(verus_verify_core))]
pub broadcast axiom fn axiom_str_literal_get_char<'a>(s: &'a str, i: int)
    ensures
        #[trigger] s@.index(i) == strslice_get_char(s, i),
;

#[cfg(all(not(feature = "alloc"), not(verus_verify_core)))]
pub broadcast group group_string_axioms {
    axiom_str_literal_len,
    axiom_str_literal_get_char,
    is_ascii_spec_bytes,
    is_ascii_concat,
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub broadcast group group_string_axioms {
    axiom_str_literal_len,
    axiom_str_literal_get_char,
    to_string_from_display_ensures_for_str,
    is_ascii_spec_bytes,
    is_ascii_concat,
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
impl View for String {
    type V = Seq<char>;

    uninterp spec fn view(&self) -> Seq<char>;
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
impl DeepView for String {
    type V = Seq<char>;

    open spec fn deep_view(&self) -> Seq<char> {
        self.view()
    }
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExString(String);

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub open spec fn string_is_ascii(s: &String) -> bool {
    is_ascii_chars(s@)
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification<'a>[ String::as_str ](s: &'a String) -> (res: &'a str)
    ensures
        res@ == s@,
;

// same as above
#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification<'a>[ <String as core::ops::Deref>::deref ](s: &'a String) -> (res: &'a str)
    ensures
        res@ == s@,
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ <String as Clone>::clone ](s: &String) -> (res: String)
    ensures
        res == s,
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ <String as PartialEq>::eq ](s: &String, other: &String) -> (res: bool)
    ensures
        res == (s@ == other@),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ String::new ]() -> (res: String)
    ensures
        res@ == Seq::<char>::empty(),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ String::push ](s: &mut String, c: char)
    ensures
        final(s)@ == old(s)@.push(c),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ String::pop ](s: &mut String) -> (res: Option<char>)
    ensures
        old(s)@.len() == 0 ==> res is None && final(s)@ == old(s)@,
        old(s)@.len() > 0 ==> res == Some(old(s)@.last()) && final(s)@ == old(s)@.drop_last(),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ String::push_str ](s: &mut String, other: &str)
    ensures
        final(s)@ == old(s)@ + other@,
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ String::is_empty ](s: &String) -> (res: bool)
    ensures
        res == (s@.len() == 0),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ String::clear ](s: &mut String)
    ensures
        final(s)@ == Seq::<char>::empty(),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ <String as core::default::Default>::default ]() -> (r: String)
    ensures
        r@ == Seq::<char>::empty(),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub trait StringExecFnsIsAscii: Sized {
    fn is_ascii(&self) -> bool;
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
impl StringExecFnsIsAscii for String {
    #[inline(always)]
    #[verifier::when_used_as_spec(string_is_ascii)]
    fn is_ascii(&self) -> (ret: bool)
        ensures
            ret == string_is_ascii(self),
    {
        self.as_str().is_ascii()
    }
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
#[verifier::external]
pub trait StringExecFns: Sized {
    fn from_str<'a>(s: &'a str) -> String;

    fn append<'a, 'b>(&'a mut self, other: &'b str);

    fn concat<'b>(self, other: &'b str) -> String;
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
impl StringExecFns for String {
    #[verifier::external_body]
    fn from_str<'a>(s: &'a str) -> (ret: String)
        ensures
            s@ == ret@,
    {
        s.to_string()
    }

    #[verifier::external_body]
    fn append<'a, 'b>(&'a mut self, other: &'b str)
        ensures
            final(self)@ == old(self)@ + other@,
    {
        *self += other;
    }

    #[verifier::external_body]
    fn concat<'b>(self, other: &'b str) -> (ret: String)
        ensures
            ret@ == self@ + other@,
    {
        self + other
    }
}

// The `chars` method of a `str` returns an iterator of type `Chars`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub struct ExChars<'a>(Chars<'a>);

// To allow reasoning about the "contents" of the string iterator, without using
// a prophecy, we need a function that gives us the underlying sequence of the original string.
#[cfg(feature = "alloc")]
pub uninterp spec fn into_iter_elts<'a>(i: Chars<'a>) -> Seq<char>;

#[cfg(feature = "alloc")]
pub assume_specification[ str::chars ](s: &str) -> (iter: Chars<'_>)
    ensures
        IteratorSpec::remaining(&iter) == s@,
        IteratorSpec::decrease(&iter) is Some,
;

#[cfg(verus_keep_ghost)]
#[cfg(feature = "alloc")]
impl<'a> super::std_specs::iter::IteratorSpecImpl for Chars<'a> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    uninterp spec fn remaining(&self) -> Seq<Self::Item>;

    uninterp spec fn will_return_none(&self) -> bool;

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < into_iter_elts(*self).len() {
            Some(into_iter_elts(*self)[index])
        } else {
            None
        }
    }
}

pub use super::view::View;

} // verus!
