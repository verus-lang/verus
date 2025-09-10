#![feature(rustc_attrs)]
#![allow(unused_imports)]

#[cfg(feature = "alloc")]
use alloc::str::Chars;
#[cfg(feature = "alloc")]
use alloc::string::{self, String, ToString};

#[cfg(feature = "alloc")]
use super::pervasive::{ForLoopGhostIterator, ForLoopGhostIteratorNew};
use super::prelude::*;
use super::seq::Seq;
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

#[cfg(feature = "alloc")]
pub assume_specification[ str::chars ](s: &str) -> (chars: Chars<'_>)
    ensures
        ({
            let (index, c) = chars@;
            &&& index == 0
            &&& c == s@
        }),
;

// The `chars` method of a `str` returns an iterator of type `Chars`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[cfg(feature = "alloc")]
pub struct ExChars<'a>(Chars<'a>);

#[cfg(feature = "alloc")]
impl<'a> View for Chars<'a> {
    type V = (int, Seq<char>);

    uninterp spec fn view(&self) -> (int, Seq<char>);
}

#[cfg(feature = "alloc")]
pub assume_specification<'a>[ Chars::<'a>::next ](chars: &mut Chars<'a>) -> (r: Option<char>)
    ensures
        ({
            let (old_index, old_seq) = old(chars)@;
            match r {
                None => {
                    &&& chars@ == old(chars)@
                    &&& old_index >= old_seq.len()
                },
                Some(k) => {
                    let (new_index, new_seq) = chars@;
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& k == old_seq[old_index]
                },
            }
        }),
;

#[cfg(feature = "alloc")]
pub struct CharsGhostIterator<'a> {
    pub pos: int,
    pub chars: Seq<char>,
    pub phantom: Option<&'a char>,
}

#[cfg(feature = "alloc")]
impl<'a> ForLoopGhostIteratorNew for Chars<'a> {
    type GhostIter = CharsGhostIterator<'a>;

    open spec fn ghost_iter(&self) -> CharsGhostIterator<'a> {
        CharsGhostIterator { pos: self@.0, chars: self@.1, phantom: None }
    }
}

#[cfg(feature = "alloc")]
impl<'a> ForLoopGhostIterator for CharsGhostIterator<'a> {
    type ExecIter = Chars<'a>;

    type Item = char;

    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &Chars<'a>) -> bool {
        &&& self.pos == exec_iter@.0
        &&& self.chars == exec_iter@.1
    }

    open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
        init matches Some(init) ==> {
            &&& init.pos == 0
            &&& init.chars == self.chars
            &&& 0 <= self.pos <= self.chars.len()
        }
    }

    open spec fn ghost_ensures(&self) -> bool {
        self.pos == self.chars.len()
    }

    open spec fn ghost_decrease(&self) -> Option<int> {
        Some(self.chars.len() - self.pos)
    }

    open spec fn ghost_peek_next(&self) -> Option<char> {
        if 0 <= self.pos < self.chars.len() {
            Some(self.chars[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(&self, _exec_iter: &Chars<'a>) -> CharsGhostIterator<'a> {
        Self { pos: self.pos + 1, ..*self }
    }
}

#[cfg(feature = "alloc")]
impl<'a> View for CharsGhostIterator<'a> {
    type V = Seq<char>;

    open spec fn view(&self) -> Seq<char> {
        self.chars.take(self.pos)
    }
}

#[cfg(feature = "alloc")]
impl<'a> DeepView for CharsGhostIterator<'a> {
    type V = Seq<char>;

    open spec fn deep_view(&self) -> Seq<char> {
        self.view()
    }
}

pub use super::view::View;

} // verus!
