use super::super::prelude::*;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::alloc::Allocator;

verus! {

// TODO
pub assume_specification<T, A: Allocator>[ <[T]>::into_vec ](b: Box<[T], A>) -> (v: Vec<T, A>)
    ensures
        v@ == b@,
;

pub assume_specification<T>[ Box::<T>::new ](t: T) -> (v: Box<T>)
    ensures
        v == t,
;

pub assume_specification<T>[ Rc::<T>::new ](t: T) -> (v: Rc<T>)
    ensures
        v == t,
;

pub assume_specification<T>[ Arc::<T>::new ](t: T) -> (v: Arc<T>)
    ensures
        v == t,
;

pub assume_specification<T: Clone, A: Allocator + Clone>[ <Box<T, A> as Clone>::clone ](
    b: &Box<T, A>,
) -> (res: Box<T, A>)
    ensures
        cloned::<T>(**b, *res),
;

pub assume_specification<T, A: Allocator>[ Rc::<T, A>::try_unwrap ](v: Rc<T, A>) -> (result: Result<
    T,
    Rc<T, A>,
>)
    ensures
        match result {
            Ok(t) => t == v,
            Err(e) => e == v,
        },
;

pub assume_specification<T, A: Allocator>[ Rc::<T, A>::into_inner ](v: Rc<T, A>) -> (result: Option<
    T,
>)
    ensures
        result matches Some(t) ==> t == v,
;

} // verus!
