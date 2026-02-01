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

pub broadcast axiom fn array_len_matches_n<T, const N: usize>(ar: &[T; N])
    ensures
        (#[trigger] ar@.len()) == N,
;

pub uninterp spec fn spec_array_as_slice<T, const N: usize>(ar: &[T; N]) -> (out: &[T]);

pub broadcast axiom fn axiom_spec_array_as_slice<T, const N: usize>(ar: &[T; N])
    ensures
        (#[trigger] spec_array_as_slice(ar))@ == ar@,
;

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

pub assume_specification<T, const N: usize>[ <[T; N]>::as_slice ](ar: &[T; N]) -> (out: &[T])
    ensures
        ar@ == out@,
;

pub uninterp spec fn spec_array_fill_for_copy_type<T: Copy, const N: usize>(t: T) -> (res: [T; N]);

pub broadcast axiom fn axiom_spec_array_fill_for_copy_type<T: Copy, const N: usize>(t: T)
    ensures
        #![trigger spec_array_fill_for_copy_type::<T, N>(t)]
        // intentionally triggering on `spec_array_fill_for_copy_type` only
        forall|i: int|
            0 <= i < N ==> spec_array_fill_for_copy_type::<T, N>(t).view()[i] == t,
;

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

pub broadcast axiom fn axiom_array_ext_equal<T, const N: usize>(a1: [T; N], a2: [T; N])
    ensures
        #[trigger] (a1 =~= a2) <==> (forall|i: int| 0 <= i < N ==> a1[i] == a2[i]),
;

#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::array::spec_array_update")]
pub uninterp spec fn spec_array_update<T, const N: usize>(array: [T; N], i: int, t: T) -> [T; N];

pub broadcast axiom fn axiom_spec_array_update<T, const N: usize>(array: [T; N], i: int, t: T)
    ensures
        0 <= i < N ==> (#[trigger] spec_array_update(array, i, t)@) == array@.update(i, t),
;

pub broadcast axiom fn axiom_array_has_resolved<T, const N: usize>(array: [T; N], i: int)
    ensures
        0 <= i < N ==> #[trigger] has_resolved::<[T; N]>(array) ==> has_resolved(
            #[trigger] array@[i],
        ),
;

#[doc(hidden)]
#[verifier::external_body]
#[verifier::ignore_outside_new_mut_ref_experiment]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::array::ref_mut_array_unsizing_coercion")]
pub fn ref_mut_array_unsizing_coercion<T, const N: usize>(r: &mut [T; N]) -> (out: &mut [T])
    ensures
        out.view() === r.view(),
        fin(out).view() === fin(r).view(),
    opens_invariants none
    no_unwind
{
    r
}

pub broadcast group group_array_axioms {
    array_len_matches_n,
    lemma_array_index,
    axiom_spec_array_as_slice,
    axiom_spec_array_fill_for_copy_type,
    axiom_array_ext_equal,
    axiom_spec_array_update,
    axiom_array_has_resolved,
}

} // verus!
