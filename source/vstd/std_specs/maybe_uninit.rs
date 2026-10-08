use super::super::prelude::*;
use super::super::points_to_permissions::TypedValue;
use core::mem::MaybeUninit;

use verus as verus_;
verus_! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExMaybeUninit<T>(MaybeUninit<T>);

pub trait MaybeUninitAdditionalSpecFns<T> {
    spec fn mem_contents(self) -> TypedValue<T>;
    spec fn as_option(self) -> Option<T>;
}

impl<T> MaybeUninitAdditionalSpecFns<T> for MaybeUninit<T> {
    uninterp spec fn mem_contents(self) -> TypedValue<T>;

    open spec fn as_option(self) -> Option<T> {
        match self.mem_contents() {
            TypedValue::Valid(v) => Some(*v),
            TypedValue::Empty => None,
        }
    }
}

pub assume_specification<T>[ MaybeUninit::<T>::new ](val: T) -> (res: MaybeUninit<T>)
    ensures res.mem_contents() == TypedValue::Valid(Box::new(val)),
    opens_invariants none
    no_unwind;

pub assume_specification<T>[ MaybeUninit::<T>::uninit ]() -> (res: MaybeUninit<T>)
    ensures res.mem_contents() == TypedValue::Empty,
    opens_invariants none
    no_unwind;

pub assume_specification<T>[ MaybeUninit::<T>::assume_init ](m: MaybeUninit<T>) -> T
    requires m.mem_contents().is_valid(),
    returns m.mem_contents().value(),
    opens_invariants none
    no_unwind;

pub assume_specification<T>[ MaybeUninit::<T>::assume_init_ref ](m: &MaybeUninit<T>) -> (ret: &T)
    requires m.mem_contents().is_valid(),
    ensures ret == m.mem_contents().value(),
    opens_invariants none
    no_unwind;

pub assume_specification<T>[ MaybeUninit::<T>::assume_init_mut ](m: &mut MaybeUninit<T>) -> (ret: &mut T)
    requires m.mem_contents().is_valid(),
    ensures *ret == old(m).mem_contents().value(),
        final(m).mem_contents().is_valid(),
        final(m).mem_contents().value() == *final(ret),
    opens_invariants none
    no_unwind;

}
