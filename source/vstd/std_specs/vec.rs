use super::super::prelude::*;
use verus_builtin::*;

use super::super::slice::SliceIndexSpec;
use super::core::IndexSpec;
use alloc::collections::TryReserveError;
use alloc::vec::{IntoIter, Vec};
use core::alloc::Allocator;
use core::clone::Clone;
use core::marker::PhantomData;
use core::ops::Index;
use core::option::Option;
use core::option::Option::None;
use core::slice::SliceIndex;

use verus as verus_;
verus_! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExVec<T, A: Allocator>(Vec<T, A>);

pub trait VecAdditionalSpecFns<T>: View<V = Seq<T>> {
    spec fn spec_index(&self, i: int) -> T
        recommends
            0 <= i < self.view().len(),
    ;
}

impl<T, A: Allocator> VecAdditionalSpecFns<T> for Vec<T, A> {
    #[verifier::inline]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExTryReserveError(alloc::collections::TryReserveError);

// We still have a special case for Vec::index on usize.
// The general Vec::index case now goes through the Index trait,
// but this special case is still here because it's more direct and efficient in its SMT encoding,
// and Vec::index on usize is very common.
//
// So this is a bit of a hack, but we just manually redirect
// `vec[i]` to this function here from rust_to_vir_expr.
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::vec::vec_index")]
pub fn vec_index<T, A: Allocator>(vec: &Vec<T, A>, i: usize) -> (element: &T)
    requires
        i < vec.view().len(),
    ensures
        *element == vec.view().index(i as int),
    no_unwind
{
    &vec[i]
}

/// This is a specification for the indexing operator `vec[i]` when it expands to the `IndexMut` trait
#[doc(hidden)]
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::vec::vec_index_mut")]
pub fn vec_index_mut<T, A: Allocator>(vec: &mut Vec<T, A>, i: usize) -> (element: &mut T)
    requires
        i < vec.view().len(),
    ensures
        *element == old(vec)@.index(i as int),
        final(vec)@ == old(vec)@.update(i as int, *final(element)),

        *final(element) == final(vec).view().index(i as int),
    no_unwind
{
    &mut vec[i]
}

////// Len (with autospec)
pub uninterp spec fn spec_vec_len<T, A: Allocator>(v: &Vec<T, A>) -> usize;

// This axiom is slightly better than defining spec_vec_len to just be `v@.len() as usize`
// (the axiom also shows that v@.len() is in-bounds for usize)
pub broadcast proof fn axiom_spec_len<T, A: Allocator>(v: &Vec<T, A>)
    ensures
        #[trigger] spec_vec_len(v) == v@.len(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_vec_len)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::len ](vec: &Vec<T, A>) -> (len: usize)
    ensures
        len == spec_vec_len(vec),
    no_unwind
;

////// Other functions
pub assume_specification<T>[ Vec::<T>::new ]() -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T>[ <Vec<T> as core::default::Default>::default ]() -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::new_in ](alloc: A) -> (v: Vec<T, A>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T>[ Vec::<T>::with_capacity ](capacity: usize) -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::with_capacity_in ](capacity: usize, alloc: A) -> (v: Vec<T, A>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::reserve ](
    vec: &mut Vec<T, A>,
    additional: usize,
)
    ensures
        final(vec)@ == old(vec)@,
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::try_reserve ](
    vec: &mut Vec<T, A>,
    additional: usize,
) -> (result: Result<(), TryReserveError>)
    ensures
        final(vec)@ == old(vec)@,
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::push ](vec: &mut Vec<T, A>, value: T)
    ensures
        final(vec)@ == old(vec)@.push(value),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::pop ](vec: &mut Vec<T, A>) -> (value:
    Option<T>)
    ensures
        old(vec)@.len() > 0 ==> value == Some(old(vec)@[old(vec)@.len() - 1])
            && final(vec)@ == old(vec)@.subrange(0, old(vec)@.len() - 1),
        old(vec)@.len() == 0 ==> value == None::<T> && final(vec)@ == old(vec)@,
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::append ](
    vec: &mut Vec<T, A>,
    other: &mut Vec<T, A>,
)
    ensures
        final(vec)@ == old(vec)@ + old(other)@,
        final(other)@ == Seq::<T>::empty(),
;

pub assume_specification<T: core::clone::Clone, A: Allocator>[ Vec::<T, A>::extend_from_slice ](
    vec: &mut Vec<T, A>,
    other: &[T],
)
    ensures
        final(vec)@.len() == old(vec)@.len() + other@.len(),
        forall|i: int|
            #![trigger final(vec)@[i]]
            0 <= i < final(vec)@.len() ==> if i < old(vec)@.len() {
                final(vec)@[i] == old(vec)@[i]
            } else {
                cloned::<T>(other@[i - old(vec)@.len()], final(vec)@[i])
            },
;

impl<T: Sized, I: SliceIndex<[T]>, A: Allocator> super::core::IndexSpecImpl<I> for Vec<T, A> {
    open spec fn index_req(&self, index: &I) -> bool {
        forall|s: &[T]| #[trigger] s@ == self@ ==> index.index_req(s)
    }
}

pub assume_specification<T, I: SliceIndex<[T]>, A: Allocator>[Vec::<T, A>::index](
    vec: &Vec<T, A>,
    i: I,
) -> (r: &<Vec<T, A> as Index<I>>::Output)
    ensures
        exists|s: &[T]| #[trigger] s@ == vec@ && call_ensures(<I as SliceIndex<[T]>>::index, (i, s), r),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::swap_remove ](
    vec: &mut Vec<T, A>,
    i: usize,
) -> (element: T)
    requires
        i < old(vec).len(),
    ensures
        element == old(vec)[i as int],
        final(vec)@ == old(vec)@.update(i as int, old(vec)@.last()).drop_last(),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::insert ](
    vec: &mut Vec<T, A>,
    i: usize,
    element: T,
)
    requires
        i <= old(vec).len(),
    ensures
        final(vec)@ == old(vec)@.insert(i as int, element),
;

pub assume_specification<T, A: Allocator> [ <Vec<T, A>>::is_empty ](
    v: &Vec<T, A>,
) -> (res: bool)
    ensures res <==> v@.len() == 0,
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::remove ](
    vec: &mut Vec<T, A>,
    i: usize,
) -> (element: T)
    requires
        i < old(vec).len(),
    ensures
        element == old(vec)[i as int],
        final(vec)@ == old(vec)@.remove(i as int),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::clear ](vec: &mut Vec<T, A>)
    ensures
        final(vec).view() == Seq::<T>::empty(),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::as_slice ](vec: &Vec<T, A>) -> (slice: &[T])
    ensures
        slice@ == vec@,
;

#[doc(hidden)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::as_mut_slice ](vec: &mut Vec<T, A>) -> (slice: &mut [T])
    ensures
        slice@ == old(vec)@,
        final(slice)@ == final(vec)@,
;

pub assume_specification<T, A: Allocator>[ <Vec<T, A> as core::ops::Deref>::deref ](
    vec: &Vec<T, A>,
) -> (slice: &[T])
    ensures
        slice@ == vec@,
;

pub assume_specification<T, A: Allocator>[ <Vec<T, A> as core::ops::DerefMut>::deref_mut ](
    vec: &mut Vec<T, A>,
) -> (slice: &mut [T])
    ensures
        slice@ == old(vec)@,
        final(slice)@ == final(vec)@,
;

pub assume_specification<T, A: Allocator + core::clone::Clone>[ Vec::<T, A>::split_off ](
    vec: &mut Vec<T, A>,
    at: usize,
) -> (return_value: Vec<T, A>)
    requires
        at <= old(vec)@.len(),
    ensures
        final(vec)@ == old(vec)@.subrange(0, at as int),
        return_value@ == old(vec)@.subrange(at as int, old(vec)@.len() as int),
;

pub open spec fn vec_clone_trigger<T, A: Allocator>(v1: Vec<T, A>, v2: Vec<T, A>) -> bool {
    true
}

pub assume_specification<T: Clone, A: Allocator + Clone>[ <Vec<T, A> as Clone>::clone ](
    vec: &Vec<T, A>,
) -> (res: Vec<T, A>)
    ensures
        res.len() == vec.len(),
        forall|i| #![all_triggers] 0 <= i < vec.len() ==> cloned::<T>(vec[i], res[i]),
        vec_clone_trigger(*vec, res),
        vec@ =~= res@ ==> vec@ == res@,
;

pub broadcast proof fn vec_clone_deep_view_proof<T: DeepView, A: Allocator>(
    v1: Vec<T, A>,
    v2: Vec<T, A>,
)
    requires
        #[trigger] vec_clone_trigger(v1, v2),
        v1.deep_view() =~= v2.deep_view(),
    ensures
        v1.deep_view() == v2.deep_view(),
{
}

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::truncate ](vec: &mut Vec<T, A>, len: usize)
    ensures
        len <= old(vec).len() ==> final(vec)@ == old(vec)@.subrange(0, len as int),
        len > old(vec).len() ==> final(vec)@ == old(vec)@,
;

pub assume_specification<T: Clone, A: Allocator>[ Vec::<T, A>::resize ](
    vec: &mut Vec<T, A>,
    len: usize,
    value: T,
)
    ensures
        len <= old(vec).len() ==> final(vec)@ == old(vec)@.subrange(0, len as int),
        len > old(vec).len() ==> {
            &&& final(vec)@.len() == len
            &&& final(vec)@.subrange(0, old(vec).len() as int) == old(vec)@
            &&& forall|i| #![all_triggers] old(vec).len() <= i < len ==> cloned::<T>(value, final(vec)@[i])
        },
;

pub broadcast proof fn axiom_vec_index_decreases<A>(v: Vec<A>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        #[trigger] (decreases_to!(v => v[i])),
{
    admit();
}

impl<T, A: Allocator> super::core::TrustedSpecSealed for Vec<T, A> {

}

impl<T, A: Allocator> super::core::IndexSetTrustedSpec<usize> for Vec<T, A> {
    open spec fn spec_index_set_requires(&self, index: usize) -> bool {
        0 <= index < self.len()
    }

    open spec fn spec_index_set_ensures(&self, new_container: &Self, index: usize, val: T) -> bool {
        new_container@ === self@.update(index as int, val)
    }
}

pub assume_specification<T: PartialEq<U>, U, A1: Allocator, A2: Allocator>[ <Vec<T, A1> as PartialEq<Vec<U, A2>>>::eq ](
    x: &Vec<T, A1>,
    y: &Vec<U, A2>,
) -> bool
;

impl<T: super::cmp::PartialEqSpec<U>, U, A1: Allocator, A2: Allocator> super::cmp::PartialEqSpecImpl<Vec<U, A2>> for Vec<T, A1> {
    open spec fn obeys_eq_spec() -> bool {
        T::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &Vec<U, A2>) -> bool {
        &&& self.len() == other.len()
        &&& forall|i: int| #![auto] 0 <= i < self.len() ==> self[i].eq_spec(&other[i])
    }
}

// The `into_iter` method of a `Vec` returns an iterator of type `IntoIter`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExIntoIter<T, A: Allocator>(IntoIter<T, A>);

impl<T, A: Allocator> View for IntoIter<T, A> {
    type V = (int, Seq<T>);

    uninterp spec fn view(self: &IntoIter<T, A>) -> (int, Seq<T>);
}

pub assume_specification<T, A: Allocator>[ IntoIter::<T, A>::next ](
    elements: &mut IntoIter<T, A>,
) -> (r: Option<T>)
    ensures
        ({
            let (old_index, old_seq) = old(elements)@;
            match r {
                None => {
                    &&& final(elements)@ == old(elements)@
                    &&& old_index >= old_seq.len()
                },
                Some(element) => {
                    let (new_index, new_seq) = final(elements)@;
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& element == old_seq[old_index]
                },
            }
        }),
;

pub struct IntoIterGhostIterator<T, A: Allocator> {
    pub pos: int,
    pub elements: Seq<T>,
    pub _marker: PhantomData<A>,
}

impl<T, A: Allocator> super::super::pervasive::ForLoopGhostIteratorNew for IntoIter<T, A> {
    type GhostIter = IntoIterGhostIterator<T, A>;

    open spec fn ghost_iter(&self) -> IntoIterGhostIterator<T, A> {
        IntoIterGhostIterator { pos: self@.0, elements: self@.1, _marker: PhantomData }
    }
}

// This is used by `vec![x; n]`
pub assume_specification<T: Clone>[ alloc::vec::from_elem ](elem: T, n: usize) -> (v: Vec<T>)
    ensures
        v.len() == n,
        forall |i| 0 <= i < n ==> cloned(elem, #[trigger] v@[i]);

impl<T, A: Allocator> super::super::pervasive::ForLoopGhostIterator for IntoIterGhostIterator<
    T,
    A,
> {
    type ExecIter = IntoIter<T, A>;

    type Item = T;

    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &IntoIter<T, A>) -> bool {
        &&& self.pos == exec_iter@.0
        &&& self.elements == exec_iter@.1
    }

    open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
        init matches Some(init) ==> {
            &&& init.pos == 0
            &&& init.elements == self.elements
            &&& 0 <= self.pos <= self.elements.len()
        }
    }

    open spec fn ghost_ensures(&self) -> bool {
        self.pos == self.elements.len()
    }

    open spec fn ghost_decrease(&self) -> Option<int> {
        Some(self.elements.len() - self.pos)
    }

    open spec fn ghost_peek_next(&self) -> Option<T> {
        if 0 <= self.pos < self.elements.len() {
            Some(self.elements[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(&self, _exec_iter: &IntoIter<T, A>) -> IntoIterGhostIterator<T, A> {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<T, A: Allocator> View for IntoIterGhostIterator<T, A> {
    type V = Seq<T>;

    open spec fn view(&self) -> Seq<T> {
        self.elements.take(self.pos)
    }
}

// To allow reasoning about the ghost iterator when the executable
// function `into_iter()` is invoked in a `for` loop header (e.g., in
// `for x in it: v.into_iter() { ... }`), we need to specify the behavior of
// the iterator in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_into_iter)` to the specification for
// the executable `into_iter` method and define that spec function here.
pub uninterp spec fn spec_into_iter<T, A: Allocator>(v: Vec<T, A>) -> (iter: <Vec<
    T,
    A,
> as core::iter::IntoIterator>::IntoIter);

pub broadcast proof fn axiom_spec_into_iter<T, A: Allocator>(v: Vec<T, A>)
    ensures
        (#[trigger] spec_into_iter(v))@ == (0int, v@),
{
    admit();
}

#[verifier::when_used_as_spec(spec_into_iter)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::into_iter ](vec: Vec<T, A>) -> (iter: <Vec<
    T,
    A,
> as core::iter::IntoIterator>::IntoIter)
    ensures
        iter@ == (0int, vec@),
;

pub broadcast proof fn lemma_vec_obeys_eq_spec<T: PartialEq>()
    requires
        super::super::laws_eq::obeys_eq::<T>(),
    ensures
        #[trigger] super::super::laws_eq::obeys_eq::<Vec<T>>(),
{
    broadcast use {axiom_spec_len, super::super::seq::group_seq_axioms};
    reveal(super::super::laws_eq::obeys_eq_spec_properties);
}

pub broadcast proof fn lemma_vec_obeys_view_eq<T: PartialEq + View>()
    requires
        super::super::laws_eq::obeys_concrete_eq::<T>(),
    ensures
        #[trigger] super::super::laws_eq::obeys_view_eq::<Vec<T>>(),
{
    use super::cmp::PartialEqSpec;
    broadcast use {axiom_spec_len, super::super::seq::group_seq_axioms};
    reveal(super::super::laws_eq::obeys_eq_spec_properties);
    reveal(super::super::laws_eq::obeys_concrete_eq);
    reveal(super::super::laws_eq::obeys_view_eq);
    assert(forall|x: Vec<T>, y: Vec<T>| x.eq_spec(&y) ==> x@ == y@);
}

pub broadcast proof fn lemma_vec_obeys_deep_eq<T: PartialEq + DeepView>()
    requires
        super::super::laws_eq::obeys_deep_eq::<T>(),
    ensures
        #[trigger] super::super::laws_eq::obeys_deep_eq::<Vec<T>>(),
{
    use super::cmp::PartialEqSpec;
    broadcast use {axiom_spec_len, super::super::seq::group_seq_axioms};
    reveal(super::super::laws_eq::obeys_eq_spec_properties);
    reveal(super::super::laws_eq::obeys_deep_eq);
    assert(forall|x: Vec<T>, y: Vec<T>| x.eq_spec(&y) ==> x.deep_view() == y.deep_view());
    assert forall|x: Vec<T>, y: Vec<T>| x.deep_view() == y.deep_view() implies x.eq_spec(&y) by {
        assert(x.deep_view().len() == y.deep_view().len());
        assert forall|i: int| #![auto] 0 <= i < x.len() implies x[i].eq_spec(&y[i]) by {
            assert(x.deep_view()[i] == y.deep_view()[i]);
        }
    }
}

pub broadcast axiom fn axiom_vec_has_resolved<T>(vec: Vec<T>, i: int)
    ensures
        0 <= i < vec.len() ==> #[trigger] has_resolved::<Vec<T>>(vec) ==> has_resolved(
            #[trigger] vec@[i],
        ),
;

pub broadcast axiom fn axiom_vec_decreases_to_view<T>(v: Vec<T>)
    ensures
        #[trigger] (decreases_to!(v => v@));

pub broadcast group group_vec_axioms {
    axiom_spec_len,
    axiom_vec_index_decreases,
    vec_clone_deep_view_proof,
    axiom_spec_into_iter,
    axiom_vec_has_resolved,
    axiom_vec_decreases_to_view,
}

} // verus!
