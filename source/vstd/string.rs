#![feature(rustc_attrs)]
#![allow(unused_imports)]

#[cfg(feature = "alloc")]
use alloc::str::Chars;
#[cfg(feature = "alloc")]
use alloc::string::{self, String, ToString};

use super::prelude::*;
use super::seq::Seq;
#[cfg(verus_keep_ghost)]
use super::std_specs::iter::IteratorSpec;
use super::view::*;

verus! {

impl View for str {
    type V = Seq<char>;

    uninterp spec fn view(&self) -> Seq<char>;
}

impl DeepView for str {
    type V = Seq<char>;

    open spec fn deep_view(&self) -> Seq<char> {
        self.view()
    }
}

pub uninterp spec fn str_slice_is_ascii(s: &str) -> bool;

#[verifier::when_used_as_spec(str_slice_is_ascii)]
pub assume_specification[ str::is_ascii ](s: &str) -> (b: bool)
    ensures
        b == str_slice_is_ascii(s),
;

pub open spec fn new_strlit_spec(s: &str) -> &str {
    s
}

#[cfg(feature = "alloc")]
use crate::alloc::borrow::ToOwned;

#[cfg(feature = "alloc")]
pub assume_specification[ str::to_owned ](s: &str) -> (res: String)
    ensures
        s@ == res@,
        s.is_ascii() == res.is_ascii(),
;

#[cfg(feature = "alloc")]
pub uninterp spec fn to_string_from_display_ensures<T: core::fmt::Display + ?Sized>(
    t: &T,
    s: String,
) -> bool;

#[cfg(feature = "alloc")]
pub broadcast proof fn to_string_from_display_ensures_for_str(t: &str, res: String)
    ensures
        #[trigger] to_string_from_display_ensures::<str>(t, res) <==> (t@ == res@ && t.is_ascii()
            == res.is_ascii()),
{
    admit();
}

#[cfg(feature = "alloc")]
pub assume_specification<T: core::fmt::Display + ?Sized>[ <T as ToString>::to_string ](
    t: &T,
) -> (res: String)
    ensures
        to_string_from_display_ensures::<T>(t, res),
;

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
            self.is_ascii() ==> forall|i: int| i < self@.len() ==> (self@.index(i) as nat) < 256,
    {
        self.chars().nth(i).unwrap()
    }

    #[verifier::external_body]
    fn substring_ascii<'a>(&'a self, from: usize, to: usize) -> (ret: &'a str)
        requires
            self.is_ascii(),
            from < self@.len(),
            to <= self@.len(),
        ensures
            ret@ == self@.subrange(from as int, to as int),
            ret.is_ascii() == self.is_ascii(),
    {
        &self[from..to]
    }

    #[verifier::external_body]
    fn substring_char<'a>(&'a self, from: usize, to: usize) -> (ret: &'a str)
        requires
            from < self@.len(),
            to <= self@.len(),
        ensures
            ret@ == self@.subrange(from as int, to as int),
            ret.is_ascii() == self.is_ascii(),
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
                break ;
            }
            if let Some(c) = it.next() {
                char_pos += 1;
                byte_pos += c.len_utf8();
            } else {
                break ;
            }
        }
        let byte_start = byte_start.unwrap();
        let byte_end = byte_end.unwrap();
        &self[byte_start..byte_end]
    }

    #[verifier::external_body]
    fn get_ascii(&self, i: usize) -> (b: u8)
        requires
            self.is_ascii(),
        ensures
            self.view().index(i as int) as u8 == b,
    {
        self.as_bytes()[i]
    }

    // TODO:This should be the as_bytes function after
    // slice support is added
    // pub fn as_bytes<'a>(&'a [u8]) -> (ret: &'a [u8])
    #[cfg(feature = "alloc")]
    #[verifier::external_body]
    fn as_bytes_vec(&self) -> (ret: alloc::vec::Vec<u8>)
        requires
            self.is_ascii(),
        ensures
            ret.view() == Seq::new(self.view().len(), |i| self.view().index(i) as u8),
    {
        let mut v = alloc::vec::Vec::new();
        for c in self.as_bytes().iter() {
            v.push(*c);
        }
        v
    }
}

pub broadcast axiom fn axiom_str_literal_is_ascii<'a>(s: &'a str)
    ensures
        #[trigger] s.is_ascii() == strslice_is_ascii(s),
;

pub broadcast axiom fn axiom_str_literal_len<'a>(s: &'a str)
    ensures
        #[trigger] s@.len() == strslice_len(s),
;

pub broadcast axiom fn axiom_str_literal_get_char<'a>(s: &'a str, i: int)
    ensures
        #[trigger] s@.index(i) == strslice_get_char(s, i),
;

#[cfg(not(feature = "alloc"))]
pub broadcast group group_string_axioms {
    axiom_str_literal_is_ascii,
    axiom_str_literal_len,
    axiom_str_literal_get_char,
}

#[cfg(feature = "alloc")]
pub broadcast group group_string_axioms {
    axiom_str_literal_is_ascii,
    axiom_str_literal_len,
    axiom_str_literal_get_char,
    to_string_from_display_ensures_for_str,
    axiom_spec_iter,
    next_postcondition,
}

#[cfg(feature = "alloc")]
impl View for String {
    type V = Seq<char>;

    uninterp spec fn view(&self) -> Seq<char>;
}

#[cfg(feature = "alloc")]
impl DeepView for String {
    type V = Seq<char>;

    open spec fn deep_view(&self) -> Seq<char> {
        self.view()
    }
}

#[cfg(feature = "alloc")]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExString(String);

#[cfg(feature = "alloc")]
pub uninterp spec fn string_is_ascii(s: &String) -> bool;

#[cfg(feature = "alloc")]
#[verifier::when_used_as_spec(string_is_ascii)]
pub assume_specification[ String::is_ascii ](s: &String) -> (b: bool)
    ensures
        b == string_is_ascii(s),
;

#[cfg(feature = "alloc")]
pub assume_specification<'a>[ String::as_str ](s: &'a String) -> (res: &'a str)
    ensures
        res@ == s@,
        s.is_ascii() == res.is_ascii(),
;

// same as above
#[cfg(feature = "alloc")]
pub assume_specification<'a>[ <String as core::ops::Deref>::deref ](s: &'a String) -> (res: &'a str)
    ensures
        res@ == s@,
        s.is_ascii() == res.is_ascii(),
;

#[cfg(feature = "alloc")]
pub assume_specification[ <String as Clone>::clone ](s: &String) -> (res: String)
    ensures
        res == s,
;

#[cfg(feature = "alloc")]
pub assume_specification[ <String as PartialEq>::eq ](s: &String, other: &String) -> (res: bool)
    ensures
        res == (s@ == other@),
;

#[cfg(feature = "alloc")]
pub assume_specification[ String::new ]() -> (res: String)
    ensures
        res@ == Seq::<char>::empty(),
        string_is_ascii(&res),
;

#[cfg(feature = "alloc")]
pub assume_specification[ <String as core::default::Default>::default ]() -> (r: String)
    ensures
        r@ == Seq::<char>::empty(),
        string_is_ascii(&r),
;

#[cfg(feature = "alloc")]
#[verifier::external]
pub trait StringExecFnsIsAscii: Sized {
    fn is_ascii(&self) -> bool;
}

#[cfg(feature = "alloc")]
#[verifier::external]
impl StringExecFnsIsAscii for String {
    #[inline(always)]
    fn is_ascii(&self) -> bool {
        self.as_str().is_ascii()
    }
}

#[cfg(feature = "alloc")]
#[verifier::external]
pub trait StringExecFns: Sized {
    fn from_str<'a>(s: &'a str) -> String;

    fn append<'a, 'b>(&'a mut self, other: &'b str);

    fn concat<'b>(self, other: &'b str) -> String;
}

#[cfg(feature = "alloc")]
impl StringExecFns for String {
    #[verifier::external_body]
    fn from_str<'a>(s: &'a str) -> (ret: String)
        ensures
            s@ == ret@,
            s.is_ascii() == ret.is_ascii(),
    {
        s.to_string()
    }

    #[verifier::external_body]
    fn append<'a, 'b>(&'a mut self, other: &'b str)
        ensures
            self@ == old(self)@ + other@,
            self.is_ascii() == old(self).is_ascii() && other.is_ascii(),
    {
        *self += other;
    }

    #[verifier::external_body]
    fn concat<'b>(self, other: &'b str) -> (ret: String)
        ensures
            ret@ == self@ + other@,
            ret.is_ascii() == self.is_ascii() && other.is_ascii(),
    {
        self + other
    }
}

// The `chars` method of a `str` returns an iterator of type `Chars`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[cfg(feature = "alloc")]
pub struct ExChars<'a>(Chars<'a>);

// To allow reasoning about the "contents" of the string iterator, without using
// a prophecy, we need a function that gives us the underlying sequence of the original string.
#[cfg(feature = "alloc")]
pub uninterp spec fn into_iter_elts<'a>(i: Chars<'a>) -> Seq<char>;

// #[cfg(feature = "alloc")]
// impl<'a> View for Chars<'a> {
//     type V = (int, Seq<char>);

//     uninterp spec fn view(&self) -> (int, Seq<char>);
// }

// #[cfg(feature = "alloc")]
// impl<'a> DeepView for Chars<'a> {
//     type V = <Self as View>::V;

//     open spec fn deep_view(&self) -> Self::V {
//         self@
//     }

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
        IteratorSpec::initial_value_inv(&iter, &iter),
;

#[cfg(verus_keep_ghost)]
#[cfg(feature = "alloc")]
impl <'a> super::std_specs::iter::IteratorSpecImpl for Chars<'a> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    uninterp spec fn remaining(&self) -> Seq<Self::Item>;
    uninterp spec fn completes(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_inv(&self, init: &Self) -> bool {
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
pub uninterp spec fn next_post<'a>(old_chars: &Chars<'a>, new_chars: &Chars<'a>, ret: Option<char>) -> bool;

#[cfg(feature = "alloc")]
pub broadcast axiom fn next_postcondition<'a>(old_chars: &Chars<'a>, new_chars: &Chars<'a>, ret: Option<char>)
    requires
        #[trigger] next_post(old_chars, new_chars, ret),
    // TODO: These are copied from the Iterator::next function.  Eventually, we should
    //       relax Verus's retrictions and allow this function to inherit those specs.
    ensures
        // The iterator consistently obeys, completes, and decreases throughout its lifetime
        new_chars.obeys_prophetic_iter_laws() == old_chars.obeys_prophetic_iter_laws(),
        new_chars.obeys_prophetic_iter_laws() ==> new_chars.completes() == old_chars.completes(),
        new_chars.obeys_prophetic_iter_laws() ==> (old_chars.decrease() is Some <==> new_chars.decrease() is Some),
        // `next` pops the head of the prophesized remaining(), or returns None
        new_chars.obeys_prophetic_iter_laws() ==>
        ({
            if old_chars.remaining().len() > 0 {
                &&& new_chars.remaining() == old_chars.remaining().drop_first()
                &&& ret == Some(old_chars.remaining()[0])
            } else {
                new_chars.remaining() === old_chars.remaining() && ret === None && new_chars.completes()
            }
        }),
        // If the iterator isn't done yet, then it successfully decreases its metric (if any)
        new_chars.obeys_prophetic_iter_laws() && old_chars.remaining().len() > 0 && new_chars.decrease() is Some ==>
            decreases_to!(old_chars.decrease()->0 => new_chars.decrease()->0),
;


#[cfg(feature = "alloc")]
pub assume_specification<'a>[ Chars::<'a>::next ](chars: &mut Chars<'a>) -> (ret: Option<char>)
    // TODO: These are copied from the Iterator::next function.  Eventually, we should
    //       relax Verus's retrictions and allow this function to inherit those specs.
    ensures
        next_post(old(chars), chars, ret),
        // // The iterator consistently obeys, completes, and decreases throughout its lifetime
        // (&*chars).obeys_prophetic_iter_laws() == (&*old(chars)).obeys_prophetic_iter_laws(),
        // (&*chars).obeys_prophetic_iter_laws() ==> (&*chars).completes() == (&*old(chars)).completes(),
        // (&*chars).obeys_prophetic_iter_laws() ==> ((&*old(chars)).decrease() is Some <==> (&*chars).decrease() is Some),
        // // `next` pops the head of the prophesized remaining(), or returns None
        // (&*chars).obeys_prophetic_iter_laws() ==>
        // ({
        //     if (&*old(chars)).remaining().len() > 0 {
        //         &&& (&*chars).remaining() == (&*old(chars)).remaining().drop_first()
        //         &&& ret == Some((&*old(chars)).remaining()[0])
        //     } else {
        //         (&*chars).remaining() === (&*old(chars)).remaining() && ret === None && (&*chars).completes()
        //     }
        // }),
        // // If the iterator isn't done yet, then it successfully decreases its metric (if any)
        // (&*chars).obeys_prophetic_iter_laws() && (&*old(chars)).remaining().len() > 0 && (&*chars).decrease() is Some ==>
        //     decreases_to!((&*old(chars)).decrease()->0 => (&*chars).decrease()->0),
;

pub use super::view::View;

} // verus!
