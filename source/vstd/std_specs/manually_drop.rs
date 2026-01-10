#![allow(unused_imports)]

use super::super::prelude::*;
use core::mem::ManuallyDrop;
use core::ops::Deref;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(V)]
pub struct ExManuallyDrop<V: ?Sized>(ManuallyDrop<V>);

pub trait ManuallyDropAdditionalFns<T: ?Sized> {
    spec fn view_ref(&self) -> &T;
}

impl<T: ?Sized> ManuallyDropAdditionalFns<T> for ManuallyDrop<T> {
    uninterp spec fn view_ref(&self) -> &T;
}

impl<T> View for ManuallyDrop<T> {
    type V = T;

    open spec fn view(&self) -> Self::V {
        *self.view_ref()
    }
}

pub assume_specification<T>[ ManuallyDrop::<T>::new ](value: T) -> (res: ManuallyDrop<T>)
    ensures
        res@ === value,
;

pub assume_specification<T>[ ManuallyDrop::<T>::into_inner ](m: ManuallyDrop<T>) -> T
    returns
        m@,
;

pub assume_specification<T: Clone + ?Sized>[ <ManuallyDrop<T> as Clone>::clone ](
    m: &ManuallyDrop<T>,
) -> (res: ManuallyDrop<T>)
    ensures
        cloned(m@, res@),
;

pub assume_specification<T: ?Sized>[ <ManuallyDrop<T> as Deref>::deref ](
    m: &ManuallyDrop<T>,
) -> (res: &T)
    returns
        m.view_ref(),
;

pub broadcast axiom fn axiom_manually_drop_has_resolved<T: ?Sized>(m: &ManuallyDrop<T>)
    ensures
        #[trigger] has_resolved_unsized::<ManuallyDrop<T>>(m) ==> has_resolved_unsized::<T>(
            m.view_ref(),
        ),
;

pub broadcast group group_manually_drop_axioms {
    axiom_manually_drop_has_resolved,
}

} // verus!
