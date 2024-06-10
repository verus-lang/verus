#![allow(unused_imports)]
use super::prelude::*;
use super::seq::*;
use super::slice::SliceAdditionalSpecFns;
use super::view::*;

verus! {

/// Construct an array `a` of length `len` where entry `a[i]` is given by `f(i)`.
pub open spec fn spec_array_new<T, const N: usize>(len: nat, f: impl Fn(int) -> T) -> [T; N];

/*
//#[verifier::external_body]
//#[rustc_diagnostic_item = "verus::vstd::array::array_new"]
#[verifier::external_body]
#[verifier::when_used_as_spec(spec_array_new)]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::array::array_new")]
pub fn array_new<T, const N: usize>(len: nat, f: impl Fn(int) -> T) -> (arr: [T; N])
    ensures
       arr@ == Seq::new(len, f), 
{
    panic!("array_new should not be executed");
} 
*/

impl<T, const N: usize> View for [T; N] {
    type V = Seq<T>;

    spec fn view(&self) -> Seq<T>;
}

impl<T: DeepView, const N: usize> DeepView for [T; N] {
    type V = Seq<T::V>;

    open spec fn deep_view(&self) -> Seq<T::V> {
        let v = self.view();
        Seq::new(v.len(), |i: int| v[i].deep_view())
    }
}

pub trait ArrayAdditionalSpecFns<T>: View<V = Seq<T>> {
    spec fn spec_index(&self, i: int) -> T
        recommends
            0 <= i < self.view().len(),
    ;
}

#[verifier::external]
pub trait ArrayAdditionalExecFns<T> {
    fn set(&mut self, idx: usize, t: T);
}

impl<T, const N: usize> ArrayAdditionalSpecFns<T> for [T; N] {
    #[verifier::inline]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

impl<T, const N: usize> ArrayAdditionalExecFns<T> for [T; N] {
    #[verifier::external_body]
    fn set(&mut self, idx: usize, t: T)
        requires
            0 <= idx < N,
        ensures
            self@ == old(self)@.update(idx as int, t),
    {
        self[idx] = t;
    }
}

#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::array::array_index_get")]
pub exec fn array_index_get<T, const N: usize>(ar: &[T; N], i: usize) -> (out: &T)
    requires
        0 <= i < N,
    ensures
        *out == ar@.index(i as int),
{
    &ar[i]
}

pub broadcast proof fn array_len_matches_n<T, const N: usize>(ar: &[T; N])
    ensures
        (#[trigger] ar@.len()) == N,
{
    admit();
}

pub broadcast proof fn axiom_array_new<T, const N: usize>(len: nat, f: impl Fn(int) -> T)
    ensures
       (#[trigger] <[T; N] as View>::view(&array_new(len, f))) == Seq::new(len, f), 
{
    admit();
}

// Referenced by Verus' internal encoding for array literals
#[doc(hidden)]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::array::array_index")]
pub open spec fn array_index<T, const N: usize>(ar: &[T; N], i: int) -> T {
    ar.view().index(i)
}

pub open spec fn spec_array_as_slice<T, const N: usize>(ar: &[T; N]) -> (out: &[T]);

pub broadcast proof fn axiom_spec_array_as_slice<T, const N: usize>(ar: &[T; N])
    ensures
        (#[trigger] spec_array_as_slice(ar))@ == ar@,
{
    admit();
}

// Referenced by Verus' internal encoding for array -> slice coercion
#[doc(hidden)]
#[verifier::external_body]
#[verifier::when_used_as_spec(spec_array_as_slice)]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::array::array_as_slice")]
pub fn array_as_slice<T, const N: usize>(ar: &[T; N]) -> (out: &[T])
    ensures
        ar@ == out@,
{
    ar
}

#[verifier::external_fn_specification]
pub fn ex_array_as_slice<T, const N: usize>(ar: &[T; N]) -> (out: &[T])
    ensures
        ar@ == out@,
{
    ar.as_slice()
}

pub spec fn spec_array_fill_for_copy_type<T: Copy, const N: usize>(t: T) -> (res: [T; N]);

#[verifier::external_body]
pub broadcast proof fn axiom_spec_array_fill_for_copy_type<T: Copy, const N: usize>(t: T)
    ensures
        #![trigger spec_array_fill_for_copy_type::<T, N>(t)]
        forall|i: int|
            0 <= i < N ==> spec_array_fill_for_copy_type::<T, N>(t).view()[i] == t,
{
}

// The 'array fill' [t; N] where t is a Copy type
// (Does not necessarily apply when t is a non-Copy const)
#[doc(hidden)]
#[verifier::external_body]
#[verifier::when_used_as_spec(spec_array_fill_for_copy_type)]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::array::array_fill_for_copy_types")]
pub fn array_fill_for_copy_types<T: Copy, const N: usize>(t: T) -> (res: [T; N])
    ensures
        res == spec_array_fill_for_copy_type::<T, N>(t),
{
    [t;N]
}

#[cfg_attr(verus_keep_ghost, verifier::prune_unless_this_module_is_used)]
pub broadcast group group_array_axioms {
    array_len_matches_n,
    axiom_array_new,
    axiom_spec_array_as_slice,
    axiom_spec_array_fill_for_copy_type,
}

} // verus!
