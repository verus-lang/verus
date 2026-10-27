use crate::contrib::exec_spec::*;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

verus! {

/// We use this special alias to tell the [`exec_spec_verified`] and [`exec_spec_unverified`] macros to
/// compile [`Seq<char>`] to [`String`] instead of [`Vec<char>`].
pub type SpecString = Seq<char>;

/// Impls for shared traits
impl ExecSpecType for SpecString {
    type ExecOwnedType = String;

    type ExecRefType<'a> = &'a str;
}

impl<'a> ToRef<&'a str> for &'a String {
    #[inline(always)]
    fn get_ref(self) -> &'a str {
        self.as_str()
    }
}

impl<'a> ToOwned<String> for &'a str {
    #[verifier::external_body]
    #[inline(always)]
    fn get_owned(self) -> String {
        self.to_string()
    }
}

impl DeepViewClone for String {
    #[inline(always)]
    fn deep_clone(&self) -> Self {
        self.clone()
    }
}

impl<'a> ObeysDeepEq for &'a str {
    proof fn lemma_obeys_deep_eq() {
        reveal(crate::laws_eq::obeys_deep_eq);
    }
}

impl ObeysDeepEq for String {
    proof fn lemma_obeys_deep_eq() {
        reveal(crate::laws_eq::obeys_deep_eq);
    }
}

impl<'a> ExecSpecLen for &'a str {
    #[inline(always)]
    fn exec_len(self) -> (res: usize)
        ensures
            res == self.deep_view().len(),
    {
        self.unicode_len()
    }
}

impl<'a> ExecSpecIndex<'a> for &'a str {
    type Elem = char;

    #[inline(always)]
    fn exec_index(self, index: usize) -> (res: Self::Elem)
        ensures
            res == self.deep_view()[index as int],
    {
        self.get_char(index)
    }
}

} // verus!
