use super::super::prelude::*;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::alloc::Allocator;

verus! {

#[verifier::external_fn_specification]
pub fn box_into_vec<T, A: Allocator>(b: Box<[T], A>) -> (v: Vec<T, A>)
    ensures
        v@ == b@,
{
    b.into_vec()
}

#[verifier::external_fn_specification]
pub fn box_new<T>(t: T) -> (v: Box<T>)
    ensures
        v == t,
{
    Box::new(t)
}

#[verifier::external_fn_specification]
pub fn rc_new<T>(t: T) -> (v: Rc<T>)
    ensures
        v == t,
{
    Rc::new(t)
}

#[verifier::external_fn_specification]
pub fn arc_new<T>(t: T) -> (v: Arc<T>)
    ensures
        v == t,
{
    Arc::new(t)
}

} // verus!
