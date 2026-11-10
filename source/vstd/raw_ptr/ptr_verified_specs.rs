//! The `PointsTo` versions of the trusted permission functions in `ptr_specs` and `shared_reference`,
//! verified from their versions over the permission's parts
//! and the shared-reference functions (`ptr_shr_ref`, `ref_from_parts`,
//! `ref_to_parts`, `mut_ref_as_shr_ref`).
#![allow(unused_imports)]

use super::super::prelude::*;
use super::points_to_model::*;
use super::points_to_ops::*;
use super::points_to_structs::*;
use super::ptr_model;
use super::ptr_model::*;
use super::ptr_specs::*;

verus! {

broadcast use ptr_model::group_raw_ptr_axioms;

/// Borrows the parts of a well-formed `PointsTo<T>` for `ptr` as one permission.
proof fn points_to_from_parts_ref<'a, T>(
    ptr: *mut T,
    tracked pt_untyped: &'a PointsToUntyped,
    tracked typed_value: &'a TypedValue<T>,
) -> (tracked pt: &'a PointsTo<T>)
    requires
        pt_parts_wf(ptr@, *pt_untyped, *typed_value),
    ensures
        pt.ptr() == ptr,
        pt.typed_value() == *typed_value,
        pt.wf(),
{
    let tracked pt_unaligned = PointsToUnaligned::<T>::from_raw_parts_ref(
        pt_untyped,
        typed_value,
        (),
    );
    let tracked pt = PointsTo::<T>::from_raw_parts_ref(pt_unaligned);
    PointsTo::<T>::lemma_pt_parts_wf(*pt);
    pt
}

/// Borrows the parts of a well-formed `PointsTo<[T]>` for `ptr` as one permission.
proof fn points_to_from_parts_ref_slice<'a, T>(
    ptr: *mut [T],
    tracked pt_untyped: &'a PointsToUntyped,
    tracked typed_value: &'a TypedValue<[T]>,
) -> (tracked pt: &'a PointsTo<[T]>)
    requires
        pt_parts_wf_slice(ptr@, *pt_untyped, *typed_value),
    ensures
        pt.ptr() == ptr,
        pt.typed_value() == *typed_value,
        pt.wf(),
{
    let tracked pt_unaligned = PointsToUnaligned::<[T]>::from_raw_parts_ref(
        pt_untyped,
        typed_value,
        ptr@.metadata,
    );
    let tracked pt = PointsTo::<[T]>::from_raw_parts_ref(pt_unaligned);
    PointsTo::<[T]>::lemma_pt_parts_wf(*pt);
    pt
}

/// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[cfg(not(verus_verify_core))]
#[inline(always)]
#[verifier::shadow_data]
pub const fn ptr_ref<T>(ptr: *const T, Tracked(perm): Tracked<&PointsTo<T>>) -> (v: &T)
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v == perm.value(),
    opens_invariants none
    no_unwind
{
    ptr_shr_ref(ptr, Tracked(perm.borrow_ref()))
}

/// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[cfg(not(verus_verify_core))]
#[inline(always)]
#[verifier::shadow_data]
pub const fn ptr_ref_slice<T>(ptr: *const [T], Tracked(perm): Tracked<&PointsTo<[T]>>) -> (v: &[T])
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v@ == perm.value(),
    opens_invariants none
    no_unwind
{
    ptr_shr_ref(ptr, Tracked(perm.borrow_ref()))
}

/// Equivalent to `&mut *ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[cfg(not(verus_verify_core))]
#[inline(always)]
pub const fn ptr_mut_ref<T>(ptr: *mut T, Tracked(perm): Tracked<&mut PointsTo<T>>) -> (v: &mut T)
    requires
        old(perm).ptr() == ptr,
        old(perm).is_valid(),
        old(perm).wf(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_valid(),
        // The final bytes decode to the final value.
        final(perm).wf(),
        old(perm).value() == *v,
        final(perm).value() == *final(v),
    opens_invariants none
    no_unwind
{
    let tracked val = perm.borrow_mut();
    ptr_mut_ref_join(ptr, Tracked(val))
}

/// Equivalent to `&mut *ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[cfg(not(verus_verify_core))]
#[inline(always)]
pub const fn ptr_mut_ref_slice<T>(ptr: *mut [T], Tracked(perm): Tracked<&mut PointsTo<[T]>>) -> (v:
    &mut [T])
    requires
        old(perm).ptr() == ptr,
        old(perm).is_valid(),
        old(perm).wf(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_valid(),
        // The final bytes decode to the final value.
        final(perm).wf(),
        old(perm).value() == v@,
        final(perm).value() == final(v)@,
    opens_invariants none
    no_unwind
{
    let tracked val = perm.borrow_mut();
    ptr_mut_ref_join(ptr, Tracked(val))
}

/// A shared reference gives a shared, valid permission for its memory, at its pointer.
#[verifier::shadow_data]
pub proof fn shr_ref_points_to<'a, T>(tracked r: &'a T) -> (tracked pt: &'a PointsTo<T>)
    ensures
        pt.ptr() == shared_ref_ptr(shadow_data(r)),
        pt.is_valid(),
        pt.typed_value().value_ref() == r,
        pt.wf(),
{
    let tracked (pt_untyped, typed_value) = ref_to_parts(r);
    points_to_from_parts_ref(shared_ref_ptr(shadow_data(r)) as *mut T, pt_untyped, typed_value)
}

/// A shared slice reference gives a shared, valid permission for its memory, at its pointer.
#[verifier::shadow_data]
pub proof fn shr_ref_points_to_slice<'a, T>(tracked r: &'a [T]) -> (tracked pt: &'a PointsTo<[T]>)
    ensures
        pt.ptr() == shared_ref_ptr(shadow_data(r)),
        pt.is_valid(),
        pt.typed_value().value_ref() == r,
        pt.wf(),
{
    let tracked (pt_untyped, typed_value) = ref_to_parts_slice(r);
    points_to_from_parts_ref_slice(shared_ref_ptr(shadow_data(r)) as *mut [T], pt_untyped, typed_value)
}

/// The length of a `&[T]` matches the metadata of its pointer.
#[verifier::shadow_data]
pub proof fn shr_ref_slice_len<T>(tracked r: &[T])
    ensures
        shared_ref_ptr(shadow_data(r))@.metadata == r@.len(),
{
    let tracked (pt_untyped, typed_value) = ref_to_parts_slice(r);
}

/// The length of a `&mut [T]` should always match the metadata of its corresponding pointer.
#[verifier::shadow_data]
pub proof fn mut_ref_slice_len<T>(tracked b: &&mut [T])
    ensures
        mut_ref_ptr(*b)@.metadata == old(*b)@.len(),
{
    let tracked r = mut_ref_as_shr_ref(b);
    shr_ref_slice_len(r);
}

/// Convert from a shared reference to a `&'a mut T` to a `&'a PointsTo<T>`.
#[cfg(not(verus_verify_core))]
#[verifier::shadow_data]
pub proof fn mut_ref_to_shr_points_to<'a, T>(tracked mut_ref: &'a &'a mut T) -> (tracked pt:
    &'a PointsTo<T>)
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_valid(),
        pt.value() == *old(*mut_ref),
        pt.wf(),
        *final(*mut_ref) == *old(*mut_ref),
{
    let tracked r = mut_ref_as_shr_ref(mut_ref);
    let tracked (pt_untyped, typed_value) = ref_to_parts(r);
    points_to_from_parts_ref(mut_ref_ptr(*mut_ref), pt_untyped, typed_value)
}

/// Convert from a shared reference to a `&'a mut [T]` to a `&'a PointsTo<[T]>`.
#[cfg(not(verus_verify_core))]
#[verifier::shadow_data]
pub proof fn mut_ref_to_shr_points_to_slice<'a, T>(tracked mut_ref: &'a &'a mut [T]) -> (tracked pt:
    &'a PointsTo<[T]>)
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_valid(),
        pt.value() == (*old(*mut_ref))@,
        pt.wf(),
        &*final(*mut_ref) == &*old(*mut_ref),
{
    let tracked r = mut_ref_as_shr_ref(mut_ref);
    let tracked (pt_untyped, typed_value) = ref_to_parts_slice(r);
    points_to_from_parts_ref_slice(mut_ref_ptr(*mut_ref), pt_untyped, typed_value)
}

} // verus!
