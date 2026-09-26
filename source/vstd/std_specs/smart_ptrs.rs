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

// `Arc` dereferences to its contents. Without this, anything reached through
// an `Arc` -- `arc_of_slice.iter()`, `arc_of_slice.len()` -- goes through an
// unspecified `deref` and nothing about the result is known, which breaks the
// chain at its first step rather than at the method being called.
//
// The bounds must match std's `impl<T: ?Sized, A: Allocator> Deref for
// Arc<T, A>` exactly, so no `View` bound can be added here and the result
// cannot be described by `@` directly. Stated the way `ManuallyDrop`'s deref
// is: an uninterpreted contents function, plus a broadcast axiom relating it
// to the view for the types that have one.
pub uninterp spec fn arc_contents<T: ?Sized, A: Allocator>(a: &Arc<T, A>) -> &T;

pub assume_specification<T: ?Sized, A: Allocator>[ <Arc<T, A> as core::ops::Deref>::deref ](
    a: &Arc<T, A>,
) -> (res: &T)
    returns
        arc_contents(a),
;

// `AsRef` is the same borrow of the contents as `Deref`.
pub assume_specification<T: ?Sized, A: Allocator>[ <Arc<T, A> as core::convert::AsRef<T>>::as_ref ](
    a: &Arc<T, A>,
) -> (res: &T)
    returns
        arc_contents(a),
;

pub broadcast axiom fn axiom_arc_contents_view<T: View + ?Sized, A: Allocator>(a: &Arc<T, A>)
    ensures
        (#[trigger] arc_contents(a))@ == a@,
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
