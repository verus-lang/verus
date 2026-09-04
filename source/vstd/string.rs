#![feature(rustc_attrs)]
#![allow(unused_imports)]

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
use alloc::str::Chars;
#[cfg(all(feature = "alloc", not(verus_verify_core)))]
use alloc::string::{self, String, ToString};
#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
use core::ops::{Bound, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};
#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
use core::slice::SliceIndex;

use super::prelude::*;
use super::seq::Seq;
use super::slice::*;
#[cfg(verus_keep_ghost)]
#[cfg(all(feature = "alloc", not(verus_verify_core)))]
use super::std_specs::iter::IteratorSpec;
#[cfg(verus_keep_ghost)]
use super::std_specs::range::{
    ExRange, RangeBoundsSpec, slice_range_end, slice_range_start, slice_range_valid,
};
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

// There are various types you can use to index into a `str` to get a
// slice, i.e., to implement `SliceIndex<str>`. Here we indicate, for
// any such type (e.g., `Range<usize>`), whether an index of that
// type is valid when applied to a given `&str`.
#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub open spec fn str_slice_in_bounds<R: RangeBoundsSpec<usize>>(range: &R, s: &str) -> bool {
    &&& slice_range_valid(range, s.spec_bytes().len())
    &&& is_char_boundary(s.spec_bytes(), slice_range_start(range))
    &&& is_char_boundary(s.spec_bytes(), slice_range_end(range, s.spec_bytes().len()))
}

// There are various types you can use to index into a `str` to get a
// slice, i.e., to implement `SliceIndex<str>`. Here we indicate, for
// any such type (e.g., `Range<usize>`), the semantics of immutably
// indexing a string.
#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub open spec fn str_slice_index_postcondition<R: RangeBoundsSpec<usize>>(
    range: &R,
    s: Seq<u8>,
    r: Seq<u8>,
) -> bool {
    r == s.subrange(slice_range_start(range), slice_range_end(range, s.len()))
}

// There are various types you can use to index into a `str` to get a
// slice, i.e., to implement `SliceIndex<str>`. Here we indicate, for
// any such type (e.g., `Range<usize>`), the semantics of mutably
// indexing a string.
#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub open spec fn str_slice_index_mut_postcondition<R: RangeBoundsSpec<usize>>(
    range: &R,
    old_s: Seq<u8>,
    final_s: Seq<u8>,
    r: Seq<u8>,
    final_r: Seq<u8>,
) -> bool {
    let start = slice_range_start(range);
    let end = slice_range_end(range, old_s.len());
    &&& r == old_s.subrange(start, end)
    &&& final_s.len() == old_s.len()
    &&& final_s.subrange(0, start) == old_s.subrange(0, start)
    &&& final_s.subrange(start, end) == final_r
    &&& final_s.subrange(end, old_s.len() as int) == old_s.subrange(end, old_s.len() as int)
}

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
impl super::slice::SliceIndexSpecImpl<str> for (Bound<usize>, Bound<usize>) {
    open spec fn in_bounds(&self, s: &str) -> bool {
        str_slice_in_bounds(self, s)
    }
}

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <(Bound<usize>, Bound<usize>) as SliceIndex<str>>::get ](
    i: (Bound<usize>, Bound<usize>),
    s: &str,
) -> (r: Option<&str>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <(Bound<usize>, Bound<usize>) as SliceIndex<str>>::index ](
    i: (Bound<usize>, Bound<usize>),
    s: &str,
) -> (r: &str)
    ensures
        str_slice_index_postcondition(&i, s.spec_bytes(), r.spec_bytes()),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <(Bound<usize>, Bound<usize>) as SliceIndex<str>>::get_mut ](
    i: (Bound<usize>, Bound<usize>),
    s: &mut str,
) -> (r: Option<&mut str>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <(Bound<usize>, Bound<usize>) as SliceIndex<str>>::index_mut ](
    i: (Bound<usize>, Bound<usize>),
    s: &mut str,
) -> (r: &mut str)
    ensures
        str_slice_index_mut_postcondition(
            &i,
            old(s).spec_bytes(),
            final(s).spec_bytes(),
            r.spec_bytes(),
            final(r).spec_bytes(),
        ),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
impl super::slice::SliceIndexSpecImpl<str> for Range<usize> {
    open spec fn in_bounds(&self, s: &str) -> bool {
        str_slice_in_bounds(self, s)
    }
}

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <Range<usize> as SliceIndex<str>>::get ](i: Range<usize>, s: &str) -> (r:
    Option<&<Range<usize> as SliceIndex<str>>::Output>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <Range<usize> as SliceIndex<str>>::index ](
    i: Range<usize>,
    s: &str,
) -> (r: &<Range<usize> as SliceIndex<str>>::Output)
    ensures
        str_slice_index_postcondition(&i, s.spec_bytes(), r.spec_bytes()),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <Range<usize> as SliceIndex<str>>::get_mut ](
    i: Range<usize>,
    s: &mut str,
) -> (r: Option<&mut <Range<usize> as SliceIndex<str>>::Output>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <Range<usize> as SliceIndex<str>>::index_mut ](
    i: Range<usize>,
    s: &mut str,
) -> (r: &mut <Range<usize> as SliceIndex<str>>::Output)
    ensures
        str_slice_index_mut_postcondition(
            &i,
            old(s).spec_bytes(),
            final(s).spec_bytes(),
            r.spec_bytes(),
            final(r).spec_bytes(),
        ),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
impl super::slice::SliceIndexSpecImpl<str> for RangeFrom<usize> {
    open spec fn in_bounds(&self, s: &str) -> bool {
        str_slice_in_bounds(self, s)
    }
}

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeFrom<usize> as SliceIndex<str>>::get ](
    i: RangeFrom<usize>,
    s: &str,
) -> (r: Option<&<RangeFrom<usize> as SliceIndex<str>>::Output>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeFrom<usize> as SliceIndex<str>>::index ](
    i: RangeFrom<usize>,
    s: &str,
) -> (r: &<RangeFrom<usize> as SliceIndex<str>>::Output)
    ensures
        str_slice_index_postcondition(&i, s.spec_bytes(), r.spec_bytes()),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeFrom<usize> as SliceIndex<str>>::get_mut ](
    i: RangeFrom<usize>,
    s: &mut str,
) -> (r: Option<&mut <RangeFrom<usize> as SliceIndex<str>>::Output>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeFrom<usize> as SliceIndex<str>>::index_mut ](
    i: RangeFrom<usize>,
    s: &mut str,
) -> (r: &mut <RangeFrom<usize> as SliceIndex<str>>::Output)
    ensures
        str_slice_index_mut_postcondition(
            &i,
            old(s).spec_bytes(),
            final(s).spec_bytes(),
            r.spec_bytes(),
            final(r).spec_bytes(),
        ),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
impl super::slice::SliceIndexSpecImpl<str> for RangeFull {
    open spec fn in_bounds(&self, s: &str) -> bool {
        str_slice_in_bounds(self, s)
    }
}

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeFull as SliceIndex<str>>::get ](i: RangeFull, s: &str) -> (r:
    Option<&<RangeFull as SliceIndex<str>>::Output>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeFull as SliceIndex<str>>::index ](i: RangeFull, s: &str) -> (r:
    &<RangeFull as SliceIndex<str>>::Output)
    ensures
        str_slice_index_postcondition(&i, s.spec_bytes(), r.spec_bytes()),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeFull as SliceIndex<str>>::get_mut ](
    i: RangeFull,
    s: &mut str,
) -> (r: Option<&mut <RangeFull as SliceIndex<str>>::Output>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeFull as SliceIndex<str>>::index_mut ](
    i: RangeFull,
    s: &mut str,
) -> (r: &mut <RangeFull as SliceIndex<str>>::Output)
    ensures
        str_slice_index_mut_postcondition(
            &i,
            old(s).spec_bytes(),
            final(s).spec_bytes(),
            r.spec_bytes(),
            final(r).spec_bytes(),
        ),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
impl super::slice::SliceIndexSpecImpl<str> for RangeInclusive<usize> {
    open spec fn in_bounds(&self, s: &str) -> bool {
        str_slice_in_bounds(self, s)
    }
}

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeInclusive<usize> as SliceIndex<str>>::get ](
    i: RangeInclusive<usize>,
    s: &str,
) -> (r: Option<&<RangeInclusive<usize> as SliceIndex<str>>::Output>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeInclusive<usize> as SliceIndex<str>>::index ](
    i: RangeInclusive<usize>,
    s: &str,
) -> (r: &<RangeInclusive<usize> as SliceIndex<str>>::Output)
    ensures
        str_slice_index_postcondition(&i, s.spec_bytes(), r.spec_bytes()),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeInclusive<usize> as SliceIndex<str>>::get_mut ](
    i: RangeInclusive<usize>,
    s: &mut str,
) -> (r: Option<&mut <RangeInclusive<usize> as SliceIndex<str>>::Output>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeInclusive<usize> as SliceIndex<str>>::index_mut ](
    i: RangeInclusive<usize>,
    s: &mut str,
) -> (r: &mut <RangeInclusive<usize> as SliceIndex<str>>::Output)
    ensures
        str_slice_index_mut_postcondition(
            &i,
            old(s).spec_bytes(),
            final(s).spec_bytes(),
            r.spec_bytes(),
            final(r).spec_bytes(),
        ),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
impl super::slice::SliceIndexSpecImpl<str> for RangeTo<usize> {
    open spec fn in_bounds(&self, s: &str) -> bool {
        str_slice_in_bounds(self, s)
    }
}

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeTo<usize> as SliceIndex<str>>::get ](
    i: RangeTo<usize>,
    s: &str,
) -> (r: Option<&<RangeTo<usize> as SliceIndex<str>>::Output>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeTo<usize> as SliceIndex<str>>::index ](
    i: RangeTo<usize>,
    s: &str,
) -> (r: &<RangeTo<usize> as SliceIndex<str>>::Output)
    ensures
        str_slice_index_postcondition(&i, s.spec_bytes(), r.spec_bytes()),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeTo<usize> as SliceIndex<str>>::get_mut ](
    i: RangeTo<usize>,
    s: &mut str,
) -> (r: Option<&mut <RangeTo<usize> as SliceIndex<str>>::Output>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeTo<usize> as SliceIndex<str>>::index_mut ](
    i: RangeTo<usize>,
    s: &mut str,
) -> (r: &mut <RangeTo<usize> as SliceIndex<str>>::Output)
    ensures
        str_slice_index_mut_postcondition(
            &i,
            old(s).spec_bytes(),
            final(s).spec_bytes(),
            r.spec_bytes(),
            final(r).spec_bytes(),
        ),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
impl super::slice::SliceIndexSpecImpl<str> for RangeToInclusive<usize> {
    open spec fn in_bounds(&self, s: &str) -> bool {
        str_slice_in_bounds(self, s)
    }
}

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeToInclusive<usize> as SliceIndex<str>>::get ](
    i: RangeToInclusive<usize>,
    s: &str,
) -> (r: Option<&<RangeToInclusive<usize> as SliceIndex<str>>::Output>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeToInclusive<usize> as SliceIndex<str>>::index ](
    i: RangeToInclusive<usize>,
    s: &str,
) -> (r: &<RangeToInclusive<usize> as SliceIndex<str>>::Output)
    ensures
        str_slice_index_postcondition(&i, s.spec_bytes(), r.spec_bytes()),
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeToInclusive<usize> as SliceIndex<str>>::get_mut ](
    i: RangeToInclusive<usize>,
    s: &mut str,
) -> (r: Option<&mut <RangeToInclusive<usize> as SliceIndex<str>>::Output>)
;

#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
pub assume_specification[ <RangeToInclusive<usize> as SliceIndex<str>>::index_mut ](
    i: RangeToInclusive<usize>,
    s: &mut str,
) -> (r: &mut <RangeToInclusive<usize> as SliceIndex<str>>::Output)
    ensures
        str_slice_index_mut_postcondition(
            &i,
            old(s).spec_bytes(),
            final(s).spec_bytes(),
            r.spec_bytes(),
            final(r).spec_bytes(),
        ),
;

// `<str as ops::Index<I>>::index(&self, index: I)` just invokes
// `index.index(self)`. So we likewise delegate determining the meaning
// of the string-index operation to that of the index type.
#[cfg(all(verus_keep_ghost, not(verus_verify_core)))]
impl<I: SliceIndexSpec<str>> super::std_specs::core::IndexSpecImpl<I> for str {
    open spec fn index_req(&self, index: &I) -> bool {
        index.in_bounds(self)
    }
}

pub use super::view::View;

} // verus!
