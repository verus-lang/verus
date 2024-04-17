#![allow(unused_imports)]
use crate::seq::*;
use crate::view::*;
use builtin::*;
use builtin_macros::*;

#[cfg(verus_keep_ghost)]
#[cfg(feature = "alloc")]
pub use super::std_specs::vec::VecAdditionalSpecFns;

verus! {

pub trait SliceAdditionalSpecFns<T> {
    spec fn view(&self) -> Seq<T>;

    spec fn spec_index(&self, i: int) -> T
        recommends
            0 <= i < self.view().len(),
    ;
}

impl<T> SliceAdditionalSpecFns<T> for [T] {
    spec fn view(&self) -> Seq<T>;

    #[verifier(inline)]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

#[verifier(external_body)]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::slice::slice_index_get")]
pub exec fn slice_index_get<T>(slice: &[T], i: usize) -> (out: &T)
    requires
        0 <= i < slice.view().len(),
    ensures
        *out == slice@.index(i as int),
{
    &slice[i]
}

#[cfg(feature = "alloc")]
#[verifier(external_body)]
pub exec fn slice_to_vec<T: Copy>(slice: &[T]) -> (out: alloc::vec::Vec<T>)
    ensures
        out@ == slice@,
{
    slice.to_vec()
}

#[verifier(external_body)]
pub exec fn slice_subrange<T, 'a>(slice: &'a [T], i: usize, j: usize) -> (out: &'a [T])
    requires
        0 <= i <= j <= slice@.len(),
    ensures
        out@ == slice@.subrange(i as int, j as int),
{
    &slice[i..j]
}

#[verifier(external_fn_specification)]
pub exec fn slice_len<T>(slice: &[T]) -> (length: usize)
    ensures
        length >= 0,
        length == slice@.len(),
{
    slice.len()
}

} // verus!
