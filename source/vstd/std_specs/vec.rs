use super::super::prelude::*;
use builtin::*;

use alloc::vec::Vec;
use core::alloc::Allocator;
use core::clone::Clone;
use core::option::Option;
use core::option::Option::None;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExVec<T, A: Allocator>(Vec<T, A>);

// this is a bit of a hack; verus treats Global specially already,
// but putting this here helps Verus pick up all the trait impls for Global
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExGlobal(alloc::alloc::Global);

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

// TODO this should really be an 'assume_specification' function
// but it's difficult to handle vec.index right now because
// it uses more trait polymorphism than we can handle right now.
//
// So this is a bit of a hack, but I'm just manually redirecting
// `vec[i]` to this function here from rust_to_vir_expr.
//
// It's not ideal, but I think it's better than the alternative, which would
// be to have users call some function with a nonstandard name to perform indexing.
/// This is a specification for the indexing operator `vec[i]`
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::vec::vec_index")]
pub fn vec_index<T, A: Allocator>(vec: &Vec<T, A>, i: usize) -> (element: &T)
    requires
        i < vec.view().len(),
    ensures
        *element == vec.view().index(i as int),
{
    &vec[i]
}

////// Len (with autospec)
pub spec fn spec_vec_len<T, A: Allocator>(v: &Vec<T, A>) -> usize;

// This axiom is slightly better than defining spec_vec_len to just be `v@.len() as usize`
// (the axiom also shows that v@.len() is in-bounds for usize)
pub broadcast proof fn axiom_spec_len<A>(v: &Vec<A>)
    ensures
        #[trigger] spec_vec_len(v) == v@.len(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_vec_len)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::len ](vec: &Vec<T, A>) -> (len: usize)
    ensures
        len == spec_vec_len(vec),
;

////// Other functions
pub assume_specification<T>[ Vec::<T>::new ]() -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T>[ Vec::<T>::with_capacity ](capacity: usize) -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::reserve ](
    vec: &mut Vec<T, A>,
    additional: usize,
)
    ensures
        vec@ == old(vec)@,
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::push ](vec: &mut Vec<T, A>, value: T)
    ensures
        vec@ == old(vec)@.push(value),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::pop ](vec: &mut Vec<T, A>) -> (value:
    Option<T>)
    ensures
        old(vec)@.len() > 0 ==> value == Some(old(vec)@[old(vec)@.len() - 1]) && vec@ == old(
            vec,
        )@.subrange(0, old(vec)@.len() - 1),
        old(vec)@.len() == 0 ==> value == None::<T> && vec@ == old(vec)@,
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::append ](
    vec: &mut Vec<T, A>,
    other: &mut Vec<T, A>,
)
    ensures
        vec@ == old(vec)@ + old(other)@,
        other@ == Seq::<T>::empty(),
;

pub assume_specification<T: core::clone::Clone, A: Allocator>[ Vec::<T, A>::extend_from_slice ](
    vec: &mut Vec<T, A>,
    other: &[T],
)
    ensures
        vec@.len() == old(vec)@.len() + other@.len(),
        forall|i: int|
            #![trigger vec@[i]]
            0 <= i < vec@.len() ==> if i < old(vec)@.len() {
                vec@[i] == old(vec)@[i]
            } else {
                cloned::<T>(other@[i - old(vec)@.len()], vec@[i])
            },
;

/*
// TODO find a way to support this
// This is difficult because of the SliceIndex trait
use std::ops::Index;

pub assume_specification<T, A: Allocator>[Vec::<T,A>::index](vec: &Vec<T>, i: usize) -> (r: &T)
    requires
        i < vec.len(),
    ensures
        *r == vec[i as int];
*/

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::insert ](
    vec: &mut Vec<T, A>,
    i: usize,
    element: T,
)
    requires
        i <= old(vec).len(),
    ensures
        vec@ == old(vec)@.insert(i as int, element),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::remove ](
    vec: &mut Vec<T, A>,
    i: usize,
) -> (element: T)
    requires
        i < old(vec).len(),
    ensures
        element == old(vec)[i as int],
        vec@ == old(vec)@.remove(i as int),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::clear ](vec: &mut Vec<T, A>)
    ensures
        vec.view() == Seq::<T>::empty(),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::as_slice ](vec: &Vec<T, A>) -> (slice: &[T])
    ensures
        slice@ == vec@,
;

pub assume_specification<T, A: Allocator + core::clone::Clone>[ Vec::<T, A>::split_off ](
    vec: &mut Vec<T, A>,
    at: usize,
) -> (return_value: Vec<T, A>)
    requires
        at <= old(vec)@.len(),
    ensures
        vec@ == old(vec)@.subrange(0, at as int),
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
        len <= old(vec).len() ==> vec@ == old(vec)@.subrange(0, len as int),
        len > old(vec).len() ==> vec@ == old(vec)@,
;

pub assume_specification<T: Clone, A: Allocator>[ Vec::<T, A>::resize ](
    vec: &mut Vec<T, A>,
    len: usize,
    value: T,
)
    ensures
        len <= old(vec).len() ==> vec@ == old(vec)@.subrange(0, len as int),
        len > old(vec).len() ==> {
            &&& vec@.len() == len
            &&& vec@.subrange(0, old(vec).len() as int) == old(vec)@
            &&& forall|i| #![all_triggers] old(vec).len() <= i < len ==> cloned::<T>(value, vec@[i])
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

pub broadcast group group_vec_axioms {
    axiom_spec_len,
    axiom_vec_index_decreases,
    vec_clone_deep_view_proof,
}

} // verus!
