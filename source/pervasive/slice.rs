#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::pervasive::seq::*;

verus!{

pub trait SliceAdditionalSpecFns<T> {
   spec fn view(&self) -> Seq<T>;
   spec fn spec_index(&self, i: int) -> T;
}

impl<T> SliceAdditionalSpecFns<T> for [T] {
    spec fn view(&self) -> Seq<T>;

    #[verifier(inline)]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

#[verifier(external_body)]
pub exec fn slice_index_get<T>(slice: &[T], i: usize) -> (out: &T)
    requires 0 <= (i as int) < slice.view().len(),
    ensures *out === slice@.index(i as int),
{
    &slice[i]
}

}
