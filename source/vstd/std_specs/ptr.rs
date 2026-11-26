use super::super::prelude::*;
use core::ptr::NonNull;

use verus as verus_skip_verusfmt;
verus_skip_verusfmt! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExNonNull<T: core::marker::PointeeSized>(NonNull<T>);

pub uninterp spec fn spec_nonnull_as_ptr<T: core::marker::PointeeSized>(p: NonNull<T>) -> *mut T;

/// The wrapped pointer "must always be non-null, even if the pointer is never dereferenced"
/// ([Reference](https://doc.rust-lang.org/std/ptr/struct.NonNull.html)).
pub broadcast axiom fn axiom_nonnull_addr_nonzero<T: core::marker::PointeeSized>(p: NonNull<T>)
    ensures (#[trigger] spec_nonnull_as_ptr(p))@.addr != 0;

#[verifier::when_used_as_spec(spec_nonnull_as_ptr)]
pub assume_specification<T: core::marker::PointeeSized>[ NonNull::<T>::as_ptr ](p: NonNull<T>) -> (ret: *mut T)
    ensures ret == spec_nonnull_as_ptr(p),
    opens_invariants none
    no_unwind;

pub assume_specification<T: core::marker::PointeeSized>[ NonNull::<T>::new_unchecked ](ptr: *mut T) -> (ret: NonNull<T>)
    requires ptr@.addr != 0,
    ensures spec_nonnull_as_ptr(ret) == ptr,
    opens_invariants none
    no_unwind;

pub assume_specification<T: core::marker::PointeeSized>[ NonNull::<T>::new ](ptr: *mut T) -> (ret: Option<NonNull<T>>)
    ensures match ret {
        Some(nn) => spec_nonnull_as_ptr(nn) == ptr && ptr@.addr != 0,
        None => ptr@.addr == 0,
    },
    opens_invariants none
    no_unwind;

} // verus!
