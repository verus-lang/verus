use crate::prelude::*;
use builtin::*;

use alloc::vec::Vec;
use core::option::Option;
use core::option::Option::Some;
use core::option::Option::None;
use core::alloc::Allocator;

verus!{

#[verifier(external_type_specification)]
#[verifier(external_body)]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExVec<T, A: Allocator>(Vec<T, A>);

#[verifier(external_type_specification)]
#[verifier(external_body)]
pub struct ExGlobal(alloc::alloc::Global);

////// Declare 'view' function

pub trait VecAdditionalSpecFns<T> {
    spec fn spec_index(&self, i: int) -> T;
}

impl<T, A: Allocator> View for Vec<T, A> {
    type V = Seq<T>;
    spec fn view(&self) -> Seq<T>;
}

impl<T, A: Allocator> VecAdditionalSpecFns<T> for Vec<T, A> {
    #[verifier(inline)]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

// TODO this should really be a 'external_fn_specification' function
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
pub fn vec_index<T, A: Allocator>(vec: &Vec<T, A>, i: usize) -> (element: &T)
    requires i < vec.view().len(),
    ensures *element == vec.view().index(i as int)
{
    &vec[i]
}

////// Len (with autospec)

pub open spec fn spec_vec_len<T, A: Allocator>(v: &Vec<T, A>) -> usize;

// This axiom is slightly better than defining spec_vec_len to just be `v@.len() as usize`
// (the axiom also shows that v@.len() is in-bounds for usize)

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_spec_len<A>(v: &Vec<A>)
    ensures
        #[trigger] spec_vec_len(v) == v@.len()
{
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(spec_vec_len)]
pub fn ex_vec_len<T, A: Allocator>(vec: &Vec<T, A>) -> (len: usize)
    ensures
        len == spec_vec_len(vec)
{
    vec.len()
}

////// Other functions

#[verifier::external_fn_specification]
pub fn ex_vec_new<T>() -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
{
    Vec::<T>::new()
}

#[verifier::external_fn_specification]
pub fn ex_vec_with_capacity<T>(capacity: usize) -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
{
    Vec::<T>::with_capacity(capacity)
}

#[verifier::external_fn_specification]
pub fn ex_vec_reserve<T, A: Allocator>(vec: &mut Vec<T, A>, additional: usize)
    ensures
        vec@ == old(vec)@,
{
    vec.reserve(additional)
}

#[verifier::external_fn_specification]
pub fn ex_vec_push<T, A: Allocator>(vec: &mut Vec<T, A>, value: T)
    ensures
        vec@ == old(vec)@.push(value),
{
    vec.push(value)
}

#[verifier::external_fn_specification]
pub fn ex_vec_pop<T, A: Allocator>(vec: &mut Vec<T, A>) -> (value: Option<T>)
    ensures
        old(vec)@.len() > 0 ==>
            value == Some(old(vec)@[old(vec)@.len() - 1])
            && vec@ == old(vec)@.subrange(0, old(vec)@.len() - 1),
        old(vec)@.len() == 0 ==>
            value == None::<T>
            && vec@ == old(vec)@
{
    vec.pop()
}

#[verifier::external_fn_specification]
pub fn ex_vec_append<T, A: Allocator>(vec: &mut Vec<T, A>, other: &mut Vec<T, A>)
    ensures
        vec@ == old(vec)@ + old(other)@,
{
    vec.append(other)
}

/*
// TODO find a way to support this
// This is difficult because of the SliceIndex trait
use std::ops::Index;

#[verifier::external_fn_specification]
pub fn index<T, A: Allocator>(vec: &Vec<T>, i: usize) -> (r: &T)
    requires
        i < vec.len(),
    ensures
        *r == vec[i as int],
{

    vec.index(i)
}
*/


#[verifier::external_fn_specification]
pub fn ex_vec_insert<T, A: Allocator>(vec: &mut Vec<T, A>, i: usize, element: T)
    requires
        i <= old(vec).len(),
    ensures
        vec@ == old(vec)@.insert(i as int, element),
{
    vec.insert(i, element)
}

#[verifier::external_fn_specification]
pub fn ex_vec_remove<T, A: Allocator>(vec: &mut Vec<T, A>, i: usize) -> (element: T)
    requires
        i < old(vec).len(),
    ensures
        element == old(vec)[i as int],
        vec@ == old(vec)@.remove(i as int),
{
    vec.remove(i)
}

#[verifier::external_fn_specification]
pub fn ex_vec_clear<T, A: Allocator>(vec: &mut Vec<T, A>)
    ensures vec.view() == Seq::<T>::empty(),
{
    vec.clear()
}

#[verifier::external_fn_specification]
pub fn ex_vec_as_slice<T, A: Allocator>(vec: &Vec<T, A>) -> (slice: &[T])
    ensures slice@ == vec@
{
    vec.as_slice()
}

#[verifier::external_fn_specification]
pub fn ex_vec_split_off<T, A: Allocator+ core::clone::Clone>(vec: &mut Vec<T, A>, at: usize) -> (return_value: Vec<T, A>)
    ensures
        vec@ == old(vec)@.subrange(0,at as int),
        return_value@ == old(vec)@.subrange(at as int, old(vec)@.len() as int),
{
    vec.split_off(at)
}

#[verifier::external_fn_specification]
pub fn ex_vec_truncate<T, A: Allocator>(vec: &mut Vec<T, A>, len: usize)
    ensures
        len <= vec.len() ==> vec@ == old(vec)@.subrange(0,len as int),
        len > vec.len() ==> vec@ == old(vec)@,
{
    vec.truncate(len)
}

}
