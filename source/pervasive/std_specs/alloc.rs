use crate::prelude::*;
use builtin::*;
extern crate alloc;

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
    spec fn view(&self) -> Seq<T>;
    spec fn spec_index(&self, i: int) -> T;
}

impl<T, A: Allocator> VecAdditionalSpecFns<T> for Vec<T, A> {
    spec fn view(&self) -> Seq<T>;

    #[verifier(inline)]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
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

/*
#[verifier::external_fn_specification]
pub fn index<T, A: Allocator>(vec: &Vec<T>, i: usize) -> (r: &A)
    requires
        i < vec.len(),
    ensures
        *r == vec[i as int],
{
    vec.index(i)
}
*/


}
