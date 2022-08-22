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
pub const fn new_strlit<'a>(s: &'a str) -> StrSlice<'a> {
    StrSlice { inner: s }
}

impl<'a> StrSlice<'a> {
    pub spec fn view(&self) -> Seq<u8>;
    
    pub spec fn is_ascii(&self) -> bool;

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
                self.view().index(i as int) == c &&
                c < 128
            )
    {
        self.inner.as_bytes()[i]
    }

    #[verifier(external_body)]
    pub fn substring(&self, from: usize, to: usize) -> (ret: StrSlice<'a>)
        requires
            from < self.view().len(),
            to <= self.view().len(),
        ensures
            ret.view() === self.view().subrange(from as int, to as int)
    {
        StrSlice {
            inner: &self.inner[from..to],
        }
    }

    #[rustc_diagnostic_item = "pervasive::string::StrSlice::to_string"]
    #[verifier(external_body)]
    pub fn to_string(self) -> (ret: String)
        ensures
            self.view() === ret.view()
    {
        String::from_str(self)
    }
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_str_literal_is_ascii<'a>(s: StrSlice<'a>)
    ensures
        #[trigger] s.is_ascii() === builtin::strslice_is_ascii(s),
{ }

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_str_literal_len<'a>(s: StrSlice<'a>)
    ensures
        #[trigger] s.view().len() === builtin::strslice_len(s),
{ }

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_str_literal_get_char<'a>(s: StrSlice<'a>, i: int)
    ensures
        #[trigger] s.view().index(i) === builtin::strslice_get_char(s, i),
{ }

impl String {
    pub spec fn view(&self) -> Seq<u8>;

    pub spec fn is_ascii(&self) -> bool;

    #[verifier(external_body)]
    pub fn from_str<'a>(s: StrSlice<'a>) -> (ret: String)
        ensures
            s.view() === ret.view(),
            s.is_ascii() === ret.is_ascii(),

    {
        String { inner: s.inner.to_string() }
    }

    #[verifier(external_body)]
    pub fn as_str<'a>(&'a self) -> (ret: StrSlice<'a>)
        ensures
            self.view() === ret.view(),
            self.is_ascii() === ret.is_ascii(),
    {
        let inner = self.inner.as_str();
        StrSlice { inner }
    }
}

}
