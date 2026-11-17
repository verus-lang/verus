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

// Verus already special-cases `*` for `Arc` internally, so this is
// mostly for generic code that reaches `deref()` through a `Deref` bound
// rather than the built-in sugar. (This special-casing is why we can write
// `&**a` in the `returns` clause rather than needing to use a view-based spec.)
pub assume_specification<T: ?Sized, A: Allocator>[ <Arc<T, A> as core::ops::Deref>::deref ](
    a: &Arc<T, A>,
) -> (res: &T)
    returns
        &**a,
;

// `AsRef` is the same borrow of the contents as `Deref`.
pub assume_specification<T: ?Sized, A: Allocator>[ <Arc<T, A> as core::convert::AsRef<T>>::as_ref ](
    a: &Arc<T, A>,
) -> (res: &T)
    returns
        &**a,
;

pub assume_specification<T>[ Arc::<T>::new ](t: T) -> (v: Arc<T>)
    ensures
        *v == t,
;

// `Arc<[T]>` from a slice clones each element into the new allocation.
pub assume_specification<'a, T: Clone>[ <Arc<[T]> as core::convert::From<&'a [T]>>::from ](
    s: &[T],
) -> (r: Arc<[T]>)
    ensures
        r@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> cloned::<T>(s@[i], #[trigger] r@[i]),
;

// `Arc<[T]>` from a `Vec` moves the elements, in order.
pub assume_specification<T, A: Allocator + Clone>[ <Arc<[T], A> as core::convert::From<
    Vec<T, A>,
>>::from ](v: Vec<T, A>) -> (r: Arc<[T], A>)
    ensures
        (*r)@ == v@,
;

pub assume_specification<T: core::default::Default>[ <Arc<
    T,
> as core::default::Default>::default ]() -> (res: Arc<T>)
    ensures
        T::default.ensures((), *res),
;

// `Rc` mirrors `Arc`'s Deref/AsRef/From feature set (see above for why `&**a`
// needs no separate axiom).
pub assume_specification<T: ?Sized, A: Allocator>[ <Rc<T, A> as core::ops::Deref>::deref ](
    a: &Rc<T, A>,
) -> (res: &T)
    returns
        &**a,
;

pub assume_specification<T: ?Sized, A: Allocator>[ <Rc<T, A> as core::convert::AsRef<T>>::as_ref ](
    a: &Rc<T, A>,
) -> (res: &T)
    returns
        &**a,
;

// `Rc<[T]>` from a slice clones each element into the new allocation.
pub assume_specification<'a, T: Clone>[ <Rc<[T]> as core::convert::From<&'a [T]>>::from ](
    s: &[T],
) -> (r: Rc<[T]>)
    ensures
        r@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> cloned::<T>(s@[i], #[trigger] r@[i]),
;

// `Rc<[T]>` from a `Vec` moves the elements, in order. Unlike `Arc`'s
// equivalent, std does not require `A: Clone` here.
pub assume_specification<T, A: Allocator>[ <Rc<[T], A> as core::convert::From<Vec<T, A>>>::from ](
    v: Vec<T, A>,
) -> (r: Rc<[T], A>)
    ensures
        (*r)@ == v@,
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
