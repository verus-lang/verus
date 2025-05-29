#![allow(unused_imports)]
use super::prelude::*;
use super::seq::*;
use super::view::*;

#[cfg(verus_keep_ghost)]
#[cfg(feature = "alloc")]
pub use super::std_specs::vec::VecAdditionalSpecFns;

verus! {

impl<T> View for [T] {
    type V = Seq<T>;

    uninterp spec fn view(&self) -> Seq<T>;
}

impl<T: DeepView> DeepView for [T] {
    type V = Seq<T::V>;

    open spec fn deep_view(&self) -> Seq<T::V> {
        let v = self.view();
        Seq::new(v.len(), |i: int| v[i].deep_view())
    }
}

pub trait SliceAdditionalSpecFns<T>: View<V = Seq<T>> {
    spec fn spec_index(&self, i: int) -> T
        recommends
            0 <= i < self.view().len(),
    ;
}

impl<T> SliceAdditionalSpecFns<T> for [T] {
    #[verifier::inline]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

#[verifier::external]
pub trait SliceAdditionalExecFns<T> {
    fn set(&mut self, idx: usize, t: T);
}

impl<T> SliceAdditionalExecFns<T> for [T] {
    #[verifier::external_body]
    fn set(&mut self, idx: usize, t: T)
        requires
            0 <= idx < old(self)@.len(),
        ensures
            self@ == old(self)@.update(idx as int, t),
    {
        self[idx] = t;
    }
}

#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::slice::slice_index_get")]
pub exec fn slice_index_get<T>(slice: &[T], i: usize) -> (out: &T)
    requires
        0 <= i < slice.view().len(),
    ensures
        *out == slice@.index(i as int),
{
    &slice[i]
}

////// Len (with autospec)
pub uninterp spec fn spec_slice_len<T>(slice: &[T]) -> usize;

// This axiom is slightly better than defining spec_slice_len to just be `slice@.len() as usize`
// (the axiom also shows that slice@.len() is in-bounds for usize)
pub broadcast axiom fn axiom_spec_len<T>(slice: &[T])
    ensures
        #[trigger] spec_slice_len(slice) == slice@.len(),
;

#[verifier::when_used_as_spec(spec_slice_len)]
pub assume_specification<T>[ <[T]>::len ](slice: &[T]) -> (len: usize)
    ensures
        len == spec_slice_len(slice),
;

#[cfg(feature = "alloc")]
#[verifier::external_body]
pub exec fn slice_to_vec<T: Copy>(slice: &[T]) -> (out: alloc::vec::Vec<T>)
    ensures
        out@ == slice@,
{
    slice.to_vec()
}

#[verifier::external_body]
pub exec fn slice_subrange<T, 'a>(slice: &'a [T], i: usize, j: usize) -> (out: &'a [T])
    requires
        0 <= i <= j <= slice@.len(),
    ensures
        out@ == slice@.subrange(i as int, j as int),
{
    &slice[i..j]
}

#[verifier::external_trait_specification]
pub trait ExSliceIndex<T> where T: ?Sized {
    type ExternalTraitSpecificationFor: core::slice::SliceIndex<T>;

    type Output: ?Sized;
}

pub assume_specification<T, I>[ <[T]>::get::<I> ](slice: &[T], i: I) -> (b: Option<
    &<I as core::slice::SliceIndex<[T]>>::Output,
>) where I: core::slice::SliceIndex<[T]>
    returns
        spec_slice_get(slice, i),
;

pub uninterp spec fn spec_slice_get<T: ?Sized, I: core::slice::SliceIndex<T>>(
    val: &T,
    idx: I,
) -> Option<&<I as core::slice::SliceIndex<T>>::Output>;

pub broadcast axiom fn axiom_slice_get_usize<T>(v: &[T], i: usize)
    ensures
        i < v.len() ==> #[trigger] spec_slice_get(v, i) === Some(&v[i as int]),
        i >= v.len() ==> spec_slice_get(v, i).is_none(),
;

pub broadcast group group_slice_axioms {
    axiom_spec_len,
    axiom_slice_get_usize,
}

} // verus!
