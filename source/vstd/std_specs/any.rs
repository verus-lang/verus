#![allow(unused_imports)]

use super::super::prelude::*;
use core::any::TypeId;

verus! {

pub assume_specification<T: ?Sized + 'static>[ TypeId::of::<T> ]() -> (r: TypeId)
    ensures
        r == type_id::<T>(),
;

pub assume_specification[ <TypeId as PartialEq<TypeId>>::eq ](x: &TypeId, y: &TypeId) -> (r: bool)
    ensures
        r == (*x == *y),
;

} // verus!
