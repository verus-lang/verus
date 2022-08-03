#![feature(rustc_attrs)]

use builtin::*;
use builtin_macros::verus;
use super::seq::Seq;

verus! {

#[verifier(external_body)]
pub struct String {
    inner: std::string::String,
}

#[rustc_diagnostic_item = "pervasive::string::StrSlice"]
#[verifier(external_body)]
pub struct StrSlice<'a> {
    inner: &'a str,
}


#[rustc_diagnostic_item = "pervasive::string::new_strlit"]
#[verifier(external_body)]
pub const fn new_strlit<'a>(s: &'a str, revealable: bool) -> StrSlice<'a> {
    StrSlice { inner: s } 
}

impl<'a> StrSlice<'a> {
    pub spec fn view(&self) -> Seq<u8>;

    pub spec fn is_ascii(&self) -> bool;

    #[rustc_diagnostic_item = "pervasive::string::StrSlice::reveal"]
    #[verifier(external_body)]
    #[spec]
    pub const fn reveal(&self) {}

    #[verifier(external_body)]
    pub fn len(&self) -> (l: usize)
        ensures self.is_ascii() ==> l as nat === self.view().len()
    {
        self.inner.len()
    }
    
    #[verifier(external_body)]
    pub fn get_char(&self, i: usize) -> (c: u8)
        requires i < self.view().len()
        ensures
            self.is_ascii() ==> (
                self.view().index(i) == c &&
                c < 128
            )
    {
        self.inner.as_bytes()[i]
    }

    #[verifier(external_body)]
    pub fn substring(&self, from: usize, to: usize) -> (ret: Self)
        requires
            from < self.view().len(),
            to <= self.view().len(),
        ensures
            ret.view() === self.view().subrange(from, to)
    {
        StrSlice {
            inner: &self.inner[from..to],
        }
    }
}

}
