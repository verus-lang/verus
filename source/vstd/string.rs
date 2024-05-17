#![feature(rustc_attrs)]
#![allow(unused_imports)]

#[cfg(feature = "alloc")]
use alloc::string::{self, ToString};

use super::prelude::*;
use super::seq::Seq;
use super::view::*;

verus! {

#[cfg(feature = "alloc")]
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
pub struct String {
    inner: string::String,
}

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::string::StrSlice")]
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
pub struct StrSlice<'a> {
    inner: &'a str,
}

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::string::new_strlit")]
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
pub const fn new_strlit<'a>(s: &'a str) -> StrSlice<'a> {
    StrSlice { inner: s }
}

impl<'a> StrSlice<'a> {
    pub spec fn view(&self) -> Seq<char>;

    pub spec fn is_ascii(&self) -> bool;

    /// The len() function in rust returns the byte length.
    /// It is more useful to talk about the length of characters and therefore this function was added.
    /// Please note that this function counts the unicode variation selectors as characters.
    /// Warning: O(n)
    #[verifier::external_body]
    pub fn unicode_len(&self) -> (l: usize)
        ensures
            l as nat == self@.len(),
    {
        self.inner.chars().count()
    }

    /// Warning: O(n) not O(1) due to unicode decoding needed
    #[verifier::external_body]
    pub fn get_char(&self, i: usize) -> (c: char)
        requires
            i < self@.len(),
        ensures
            self@.index(i as int) == c,
            self.is_ascii() ==> forall|i: int| i < self@.len() ==> (self@.index(i) as nat) < 256,
    {
        self.inner.chars().nth(i).unwrap()
    }

    #[verifier::external_body]
    pub fn substring_ascii(&self, from: usize, to: usize) -> (ret: StrSlice<'a>)
        requires
            self.is_ascii(),
            from < self@.len(),
            to <= self@.len(),
        ensures
            ret@ == self@.subrange(from as int, to as int),
            ret.is_ascii() == self.is_ascii(),
    {
        StrSlice { inner: &self.inner[from..to] }
    }

    #[verifier::external_body]
    pub fn substring_char(&self, from: usize, to: usize) -> (ret: StrSlice<'a>)
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
        let mut it = self.inner.chars();
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
        StrSlice { inner: &self.inner[byte_start..byte_end] }
    }

    #[cfg(feature = "alloc")]
    pub fn to_string(self) -> (ret: String)
        ensures
            self@ == ret@,
            self.is_ascii() == ret.is_ascii(),
    {
        String::from_str(self)
    }

    #[verifier::external_body]
    pub fn get_ascii(&self, i: usize) -> (b: u8)
        requires
            self.is_ascii(),
        ensures
            self.view().index(i as int) as u8 == b,
    {
        self.inner.as_bytes()[i]
    }

    // TODO:This should be the as_bytes function after
    // slice support is added
    // pub fn as_bytes<'a>(&'a [u8]) -> (ret: &'a [u8])
    #[cfg(feature = "alloc")]
    #[verifier::external_body]
    pub fn as_bytes(&self) -> (ret: alloc::vec::Vec<u8>)
        requires
            self.is_ascii(),
        ensures
            ret.view() == Seq::new(self.view().len(), |i| self.view().index(i) as u8),
    {
        let mut v = alloc::vec::Vec::new();
        for c in self.inner.as_bytes().iter() {
            v.push(*c);
        }
        v
    }

    #[verifier::external]
    pub fn from_rust_str(inner: &'a str) -> StrSlice<'a> {
        StrSlice { inner }
    }

    #[verifier::external]
    pub fn into_rust_str(&'a self) -> &'a str {
        self.inner
    }
}

pub broadcast proof fn axiom_str_literal_is_ascii<'a>(s: StrSlice<'a>)
    ensures
        #[trigger] s.is_ascii() == strslice_is_ascii(s),
{
    admit();
}

pub broadcast proof fn axiom_str_literal_len<'a>(s: StrSlice<'a>)
    ensures
        #[trigger] s@.len() == strslice_len(s),
{
    admit();
}

pub broadcast proof fn axiom_str_literal_get_char<'a>(s: StrSlice<'a>, i: int)
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
impl String {
    pub spec fn view(&self) -> Seq<char>;

    pub spec fn is_ascii(&self) -> bool;

    #[verifier::external_body]
    pub fn from_str<'a>(s: StrSlice<'a>) -> (ret: String)
        ensures
            s@ == ret@,
            s.is_ascii() == ret.is_ascii(),
    {
        String { inner: s.inner.to_string() }
    }

    #[verifier::external_body]
    pub fn as_str<'a>(&'a self) -> (ret: StrSlice<'a>)
        ensures
            self@ == ret@,
            self.is_ascii() == ret.is_ascii(),
    {
        let inner = self.inner.as_str();
        StrSlice { inner }
    }

    #[verifier::external_body]
    pub fn append<'a, 'b>(&'a mut self, other: StrSlice<'b>)
        ensures
            self@ == old(self)@ + other@,
            self.is_ascii() == old(self).is_ascii() && other.is_ascii(),
    {
        self.inner += other.inner;
    }

    #[verifier::external_body]
    pub fn concat<'b>(self, other: StrSlice<'b>) -> (ret: String)
        ensures
            ret@ == self@ + other@,
            ret.is_ascii() == self.is_ascii() && other.is_ascii(),
    {
        String { inner: self.inner + other.inner }
    }

    #[verifier::external_body]
    pub fn eq(&self, other: &Self) -> (b: bool)
        ensures
            b == (self.view() == other.view()),
    {
        self.inner == other.inner
    }

    #[verifier::external_body]
    pub fn clone(&self) -> (result: String)
        ensures
            result == self,
    {
        String { inner: self.inner.clone() }
    }

    #[verifier::external]
    pub fn from_rust_string(inner: alloc::string::String) -> String {
        String { inner }
    }

    #[verifier::external]
    pub fn into_rust_string(self) -> alloc::string::String {
        self.inner
    }

    #[verifier::external]
    pub fn as_rust_string_ref(&self) -> &alloc::string::String {
        &self.inner
    }
}

} // verus!
