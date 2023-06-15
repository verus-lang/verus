#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::seq::*;

verus!{

pub trait ArrayAdditionalSpecFns<T> {
   spec fn view(&self) -> Seq<T>;
   spec fn spec_index(&self, i: int) -> T;
}

impl<T> ArrayAdditionalSpecFns<T> for [T] {
    spec fn view(&self) -> Seq<T>;

    #[verifier(inline)]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

#[verifier(external_body)]
pub exec fn array_index_get<T, const N: usize>(ar: &[T; N], i: usize) -> (out: &T)
    requires 0 <= i < N
    ensures *out == ar@.index(i as int),
{
    &ar[i]
}

}
