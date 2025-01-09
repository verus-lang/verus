#![allow(unused_imports)]
use super::prelude::*;
use super::seq::*;
use super::slice::SliceAdditionalSpecFns;
use super::view::*;

verus! {

pub open spec fn array_view<T, const N: usize>(a: [T; N]) -> Seq<T> {
    Seq::new(N as nat, |i: int| array_index(a, i))
}

impl<T, const N: usize> View for [T; N] {
    type V = Seq<T>;

    open spec fn view(&self) -> Seq<T> {
        array_view(*self)
    }
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

// Automatically introduce a[0], ..., a[N - 1] into SMT context
pub broadcast proof fn lemma_array_index<T, const N: usize>(a: [T; N], i: int)
    requires
        0 <= i < N,
    ensures
        #![trigger array_index(a, i)]
        a[i] == array_view(a)[i],
{
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

pub broadcast group group_array_axioms {
    array_len_matches_n,
    lemma_array_index,
    axiom_spec_array_as_slice,
    axiom_spec_array_fill_for_copy_type,
}

} // verus!
