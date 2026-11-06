use super::super::prelude::*;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::alloc::{Allocator, AllocatorClone};

verus! {

// TODO
pub assume_specification<T, A: Allocator>[ <[T]>::into_vec ](b: Box<[T], A>) -> (v: Vec<T, A>)
    ensures
        v@ == b@,
;

pub assume_specification<T>[ Box::<T>::new ](t: T) -> (v: Box<T>)
    ensures
        *v == t,
;

pub assume_specification<T: core::default::Default>[ <Box<
    T,
> as core::default::Default>::default ]() -> (res: Box<T>)
    ensures
        T::default.ensures((), *res),
;

pub assume_specification<T>[ Rc::<T>::new ](t: T) -> (v: Rc<T>)
    ensures
        *v == t,
;

pub assume_specification<T: core::default::Default>[ <Rc<
    T,
> as core::default::Default>::default ]() -> (res: Rc<T>)
    ensures
        T::default.ensures((), *res),
;

pub assume_specification<T>[ Arc::<T>::new ](t: T) -> (v: Arc<T>)
    ensures
        *v == t,
;

pub assume_specification<T: core::default::Default>[ <Arc<
    T,
> as core::default::Default>::default ]() -> (res: Arc<T>)
    ensures
        T::default.ensures((), *res),
;

// Rc/Arc clones share the source's allocation, and Verus models them by their
// pointee (the allocator contributes only its type), so the clone equals the source.
pub assume_specification<T: ?Sized, A: AllocatorClone>[ <Rc<T, A> as Clone>::clone ](
    source: &Rc<T, A>,
) -> (res: Rc<T, A>)
    ensures
        res == source,
;

pub assume_specification<T: ?Sized, A: AllocatorClone>[ <Arc<T, A> as Clone>::clone ](
    source: &Arc<T, A>,
) -> (res: Arc<T, A>)
    ensures
        res == source,
;

pub assume_specification<T: Clone, A: Allocator + Clone>[ <Box<T, A> as Clone>::clone ](
    b: &Box<T, A>,
) -> (res: Box<T, A>)
    ensures
        cloned::<T>(**b, *res),
;

// Box::clone_from delegates to the pointee's clone_from.
pub assume_specification<T: Clone, A: Allocator + Clone>[ <Box<T, A> as Clone>::clone_from ](
    dest: &mut Box<T, A>,
    source: &Box<T, A>,
)
    ensures
        strictly_cloned_from(**source, **old(dest), **final(dest)),
;

pub assume_specification<T, A: Allocator>[ Rc::<T, A>::try_unwrap ](v: Rc<T, A>) -> (result: Result<
    T,
    Rc<T, A>,
>)
    ensures
        match result {
            Ok(t) => t == *v,
            Err(e) => e == v,
        },
;

pub assume_specification<T, A: Allocator>[ Rc::<T, A>::into_inner ](v: Rc<T, A>) -> (result: Option<
    T,
>)
    ensures
        result matches Some(t) ==> t == *v,
;

} // verus!
