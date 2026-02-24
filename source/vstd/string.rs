#![feature(rustc_attrs)]
#![allow(unused_imports)]

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
use alloc::str::Chars;
#[cfg(all(feature = "alloc", not(verus_verify_core)))]
use alloc::string::{self, String, ToString};

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
use super::pervasive::{ForLoopGhostIterator, ForLoopGhostIteratorNew};
use super::prelude::*;
use super::seq::Seq;
use super::slice::*;
use super::utf8::*;
use super::view::*;

verus! {

broadcast use super::seq::group_seq_axioms;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
impl View for str {
    type V = Seq<char>;

    uninterp spec fn view(&self) -> Seq<char>;
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
impl DeepView for str {
    type V = Seq<char>;

    open spec fn deep_view(&self) -> Seq<char> {
        self.view()
    }
}  

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub trait StringSliceAdditionalSpecFns {
    spec fn spec_bytes(&self) -> Seq<u8>;
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
impl StringSliceAdditionalSpecFns for str {
    open spec fn spec_bytes(&self) -> Seq<u8> {
        encode_utf8(self@)
    }
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub open spec fn is_ascii(s: &str) -> bool {
    is_ascii_chars(s@)
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub broadcast proof fn is_ascii_spec_bytes(s: &str)
    ensures
        #[trigger] is_ascii(s) ==> #[trigger] s.spec_bytes() =~= Seq::new(s@.len(), |i| s@.index(i) as u8)
{
    if (is_ascii(s)) {
        is_ascii_chars_encode_utf8(s@);
    }
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub broadcast proof fn is_ascii_concat(s1: &str, s2: &str, s3: &str)
    requires
        s1@ =~= s2@ + s3@,
    ensures
        #![trigger s2@ + s3@, is_ascii(s1), is_ascii(s2), is_ascii(s3)]
        is_ascii(s1) <==> is_ascii(s2) && is_ascii(s3)
{
    broadcast use is_ascii_chars_concat;
    if (is_ascii(s1)) {
        is_ascii_chars_concat(s1@, s2@, s3@);
    }
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
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

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ str::as_bytes ](s: &str) -> (b: &[u8])
    ensures
        b@ == s.spec_bytes(),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ str::len ](s: &str) -> (res: usize)
    ensures
        res == s.spec_bytes().len(),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ str::is_empty ](s: &str) -> (res: bool)
    ensures
        res == (s@.len() == 0),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ str::is_char_boundary ](s: &str, index: usize) -> (res: bool)
    ensures
        res == (is_char_boundary(s.spec_bytes(), index as int)),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ str::split_at ](s: &str, mid: usize) -> (res: (&str, &str))
    requires
        is_char_boundary(s.spec_bytes(), mid as int)
    ensures
        res.0.spec_bytes() =~= s.spec_bytes().subrange(0, mid as int),
        res.1.spec_bytes() =~= s.spec_bytes().subrange(mid as int, s.spec_bytes().len() as int)
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ str::from_utf8_unchecked ](v: &[u8]) -> (res: &str)
    requires
        valid_utf8(v@)
    ensures
        res.spec_bytes() =~= v@
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

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
#[verifier::external]
pub trait StrSliceExecFns {
    fn unicode_len(&self) -> usize;

    fn get_char(&self, i: usize) -> char;

    fn substring_ascii<'a>(&'a self, from: usize, to: usize) -> &'a str;

    fn substring_char<'a>(&'a self, from: usize, to: usize) -> &'a str;

    fn get_ascii(&self, i: usize) -> u8;

    fn as_bytes_vec(&self) -> alloc::vec::Vec<u8>;
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
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
            0 <= i < self@.len(),
        ensures
            self@.index(i as int) == c,
    {
        self.chars().nth(i).unwrap()
    }

    #[verifier::external_body]
    fn substring_ascii<'a>(&'a self, from: usize, to: usize) -> (ret: &'a str)
        requires
            self.is_ascii(),
            from <= to <= self@.len(), // MODIFIED - Range::index panics if from > to
        ensures
            ret@ == self@.subrange(from as int, to as int),
            ret.is_ascii(),
    {
        &self[from..to]
    }

    #[verifier::external_body]
    fn substring_char<'a>(&'a self, from: usize, to: usize) -> (ret: &'a str)
        requires
            from <= to <= self@.len(), // MODIFIED - Range::index panics if from > to
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

    fn get_ascii(&self, i: usize) -> (b: u8)
        requires
            self.is_ascii(),
            0 <= i < self@.len() // NEW - would panic if i is not a valid index
        ensures
            self@.index(i as int) as u8 == b,
    {
        proof {
            is_ascii_spec_bytes(self);
        }
        self.as_bytes()[i]
    }

    // TODO:This should be the as_bytes function after
    // slice support is added
    // pub fn as_bytes<'a>(&'a [u8]) -> (ret: &'a [u8])
    fn as_bytes_vec(&self) -> (ret: alloc::vec::Vec<u8>)
        ensures
            ret@ == self.spec_bytes(),
    {
        proof {
            is_ascii_spec_bytes(self);
        }
        slice_to_vec(self.as_bytes())
    }
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub broadcast axiom fn axiom_str_literal_len<'a>(s: &'a str)
    ensures
        #[trigger] s@.len() == strslice_len(s),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub broadcast axiom fn axiom_str_literal_get_char<'a>(s: &'a str, i: int)
    ensures
        #[trigger] s@.index(i) == strslice_get_char(s, i),
;

#[cfg(all(not(feature = "alloc"), not(verus_verify_core)))]
pub broadcast group group_string_axioms {
    axiom_str_literal_len,
    axiom_str_literal_get_char,
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
            ret == string_is_ascii(self)
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
            self@ == old(self)@ + other@,
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

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
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
#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub struct ExChars<'a>(Chars<'a>);

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
impl<'a> View for Chars<'a> {
    type V = (int, Seq<char>);

    uninterp spec fn view(&self) -> (int, Seq<char>);
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
impl<'a> DeepView for Chars<'a> {
    type V = <Self as View>::V;

    open spec fn deep_view(&self) -> Self::V {
        self@
    }
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
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

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub struct CharsGhostIterator<'a> {
    pub pos: int,
    pub chars: Seq<char>,
    pub phantom: Option<&'a char>,
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
impl<'a> ForLoopGhostIteratorNew for Chars<'a> {
    type GhostIter = CharsGhostIterator<'a>;

    open spec fn ghost_iter(&self) -> CharsGhostIterator<'a> {
        CharsGhostIterator { pos: self@.0, chars: self@.1, phantom: None }
    }
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
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

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
impl<'a> View for CharsGhostIterator<'a> {
    type V = Seq<char>;

    open spec fn view(&self) -> Seq<char> {
        self.chars.take(self.pos)
    }
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
impl<'a> DeepView for CharsGhostIterator<'a> {
    type V = Seq<char>;

    open spec fn deep_view(&self) -> Seq<char> {
        self.view()
    }
}

pub use super::view::View;

} // verus!
