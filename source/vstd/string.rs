#![feature(rustc_attrs)]
#![allow(unused_imports)]
#![cfg_attr(rustfmt, rustfmt::skip)]

#[cfg(feature = "alloc")]
use alloc::string::{self, String, ToString};

use super::prelude::*;
use super::seq::Seq;
use super::view::*;

verus! {

impl View for str {
    type V = Seq<char>;

    spec fn view(&self) -> Seq<char>;
}

pub spec fn str_slice_is_ascii(s: &str) -> bool;

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(str_slice_is_ascii)]
pub fn ex_str_slice_is_ascii(s: &str) -> (b: bool)
    ensures
        b == str_slice_is_ascii(s),
{
    s.is_ascii()
}

#[deprecated = "Use `&str` instead"]
pub type StrSlice<'a> = &'a str;

pub open spec fn new_strlit_spec(s: &str) -> &str {
    s
}

#[deprecated = "new_strlit is no longer necessary"]
#[verifier::when_used_as_spec(new_strlit_spec)]
pub fn new_strlit(s: &str) -> (t: &str)
    ensures
        t == s,
{
    s
}

#[cfg(feature = "alloc")]
#[verifier::external_fn_specification]
pub fn ex_str_to_string(s: &str) -> (res: String)
    ensures
        s@ == res@,
        s.is_ascii() == res.is_ascii(),
{
    s.to_string()
}

#[verifier::external]
pub trait StrSliceExecFns {
    fn unicode_len(&self) -> usize;

    fn get_char(&self, i: usize) -> char;

    fn substring_ascii<'a>(&'a self, from: usize, to: usize) -> &'a str;

    fn substring_char<'a>(&'a self, from: usize, to: usize) -> &'a str;

    fn get_ascii(&self, i: usize) -> u8;

    #[cfg(feature = "alloc")]
    fn as_bytes_vec(&self) -> alloc::vec::Vec<u8>;

    #[deprecated = "from_rust_str is no longer necessary"]
    fn from_rust_str<'a>(&'a self) -> &'a str;

    #[deprecated = "into_rust_str is no longer necessary"]
    fn into_rust_str<'a>(&'a self) -> &'a str;
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

    fn from_rust_str<'a>(&'a self) -> &'a str {
        self
    }

    fn into_rust_str<'a>(&'a self) -> &'a str {
        self
    }
}

pub broadcast proof fn axiom_str_literal_is_ascii<'a>(s: &'a str)
    ensures
        #[trigger] s.is_ascii() == strslice_is_ascii(s),
{
    admit();
}

pub broadcast proof fn axiom_str_literal_len<'a>(s: &'a str)
    ensures
        #[trigger] s@.len() == strslice_len(s),
{
    admit();
}

pub broadcast proof fn axiom_str_literal_get_char<'a>(s: &'a str, i: int)
    ensures
        #[trigger] s@.index(i) == strslice_get_char(s, i),
{
    admit();
}

#[cfg_attr(verus_keep_ghost, verifier::prune_unless_this_module_is_used)]
pub broadcast group group_string_axioms {
    axiom_str_literal_is_ascii,
    axiom_str_literal_len,
    axiom_str_literal_get_char,
}

#[cfg(feature = "alloc")]
impl View for String {
    type V = Seq<char>;

    spec fn view(&self) -> Seq<char>;
}

#[cfg(feature = "alloc")]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExString(String);

#[cfg(feature = "alloc")]
pub spec fn string_is_ascii(s: &String) -> bool;

#[cfg(feature = "alloc")]
#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(string_is_ascii)]
pub fn ex_string_is_ascii(s: &String) -> (b: bool)
    ensures
        b == string_is_ascii(s),
{
    s.is_ascii()
}

#[cfg(feature = "alloc")]
#[verifier::external_fn_specification]
pub fn ex_string_as_str<'a>(s: &'a String) -> (res: &'a str)
    ensures
        res@ == s@,
        s.is_ascii() == res.is_ascii(),
{
    s.as_str()
}

#[cfg(feature = "alloc")]
#[verifier::external_fn_specification]
pub fn ex_string_clone(s: &String) -> (res: String)
    ensures
        res == s,
{
    s.clone()
}

#[cfg(feature = "alloc")]
#[verifier::external_fn_specification]
pub fn ex_string_eq(s: &String, other: &String) -> (res: bool)
    ensures
        res == (s@ == other@),
{
    s.eq(other)
}

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

    #[deprecated = "from_rust_string is no longer necessary"]
    fn from_rust_string(self) -> String;

    #[deprecated = "into_rust_string is no longer necessary"]
    fn into_rust_string(self) -> String;

    #[deprecated = "as_rust_string_ref is no longer necessary"]
    fn as_rust_string_ref(&self) -> &String;
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

    fn from_rust_string(self) -> String {
        self
    }

    fn into_rust_string(self) -> String {
        self
    }

    fn as_rust_string_ref(&self) -> &String {
        self
    }
}

pub use super::view::View;

} // verus!
