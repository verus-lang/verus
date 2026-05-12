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

broadcast use {super::seq::group_seq_axioms, super::slice::group_slice_axioms};

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
    axiom_spec_iter,
    next_postcondition,
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

// To allow reasoning about the ghost iterator when the executable
// function `iter()` is invoked in a `for` loop header (e.g., in
// `for x in it: v.iter() { ... }`), we need to specify the behavior of
// the iterator in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_iter)` to the specification for
// the executable `iter` method and define that spec function here.
#[cfg(feature = "alloc")]
pub uninterp spec fn spec_iter<'a>(s: &'a str) -> (r: Chars<'a>);

#[cfg(feature = "alloc")]
pub broadcast proof fn axiom_spec_iter<'a>(s: &'a str)
    ensures
        #[trigger] spec_iter(s).remaining() == s@,
{
    admit();
}

#[cfg(feature = "alloc")]
pub assume_specification[ str::chars ](s: &str) -> (iter: Chars<'_>)
    ensures
        iter == spec_iter(s),
        IteratorSpec::decrease(&iter) is Some,
        IteratorSpec::initial_value_relation(&iter, &iter),
;

#[cfg(verus_keep_ghost)]
#[cfg(feature = "alloc")]
impl<'a> super::std_specs::iter::IteratorSpecImpl for Chars<'a> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    uninterp spec fn remaining(&self) -> Seq<Self::Item>;

    uninterp spec fn will_return_none(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_relation(&self, init: &Self) -> bool {
        &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
        &&& into_iter_elts(*self) == IteratorSpec::remaining(self)
    }

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < into_iter_elts(*self).len() {
            Some(into_iter_elts(*self)[index])
        } else {
            None
        }
    }
}

// Ideally, we would write this postcondition directly on the definition of
// next below.  However, Verus says that this introduces a cyclic  dependency.
// Hence we introduce a layer of indirection via this uninterp spec function.
#[cfg(feature = "alloc")]
pub uninterp spec fn next_post<'a>(
    old_chars: &Chars<'a>,
    new_chars: &Chars<'a>,
    ret: Option<char>,
) -> bool;

#[cfg(feature = "alloc")]
pub broadcast axiom fn next_postcondition<'a>(
    old_chars: &Chars<'a>,
    new_chars: &Chars<'a>,
    ret: Option<char>,
)
    requires
        #[trigger] next_post(
            old_chars,
            new_chars,
            ret,
        ),
// TODO: These are copied from the Iterator::next function.  Eventually, we should
//       relax Verus's retrictions and allow this function to inherit those specs.

    ensures
// The iterator consistently obeys, completes, and decreases throughout its lifetime

        new_chars.obeys_prophetic_iter_laws() == old_chars.obeys_prophetic_iter_laws(),
        new_chars.obeys_prophetic_iter_laws() ==> new_chars.will_return_none()
            == old_chars.will_return_none(),
        new_chars.obeys_prophetic_iter_laws() ==> (old_chars.decrease() is Some
            <==> new_chars.decrease() is Some),
        // `next` pops the head of the prophesized remaining(), or returns None
        new_chars.obeys_prophetic_iter_laws() ==> ({
            if old_chars.remaining().len() > 0 {
                &&& new_chars.remaining() == old_chars.remaining().drop_first()
                &&& ret == Some(old_chars.remaining()[0])
            } else {
                new_chars.remaining() === old_chars.remaining() && ret === None
                    && new_chars.will_return_none()
            }
        }),
        // If the iterator isn't done yet, then it successfully decreases its metric (if any)
        new_chars.obeys_prophetic_iter_laws() && old_chars.remaining().len() > 0
            && new_chars.decrease() is Some
            ==> decreases_to!(old_chars.decrease()->0 => new_chars.decrease()->0),
;

#[cfg(feature = "alloc")]
pub assume_specification<'a>[ Chars::<'a>::next ](chars: &mut Chars<'a>) -> (ret: Option<char>)
    ensures
        next_post(old(chars), final(chars), ret),
;

pub use super::view::View;

} // verus!
