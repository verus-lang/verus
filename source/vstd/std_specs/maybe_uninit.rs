use super::super::prelude::*;
use super::super::raw_ptr::MemContents;
use core::mem::MaybeUninit;

use verus as verus_;
verus_! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExMaybeUninit<T>(MaybeUninit<T>);

pub trait MaybeUninitAdditionalSpecFns<T> {
    spec fn mem_contents(self) -> MemContents<T>;
    spec fn as_option(self) -> Option<T>;
}

impl<T> MaybeUninitAdditionalSpecFns<T> for MaybeUninit<T> {
    uninterp spec fn mem_contents(self) -> MemContents<T>;

    open spec fn as_option(self) -> Option<T> {
        match self.mem_contents() {
            MemContents::Init(v) => Some(v),
            MemContents::Uninit => None,
        }
    }
}

pub assume_specification<T>[ MaybeUninit::<T>::new ](val: T) -> (res: MaybeUninit<T>)
    ensures res.mem_contents() == MemContents::Init(val),
    opens_invariants none
    no_unwind;

pub assume_specification<T>[ MaybeUninit::<T>::uninit ]() -> (res: MaybeUninit<T>)
    ensures res.mem_contents() === MemContents::Uninit,
    opens_invariants none
    no_unwind;

pub assume_specification<T>[ MaybeUninit::<T>::assume_init ](m: MaybeUninit<T>) -> T
    requires m.mem_contents().is_init(),
    returns m.mem_contents().value(),
    opens_invariants none
    no_unwind;

pub assume_specification<T>[ MaybeUninit::<T>::assume_init_ref ](m: &MaybeUninit<T>) -> (ret: &T)
    requires m.mem_contents().is_init(),
    ensures ret == m.mem_contents().value(),
    opens_invariants none
    no_unwind;

}
