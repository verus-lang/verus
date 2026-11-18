//! The `PointsTo` versions of the trusted permission functions in `ptr_specs` and `shared_reference`,
//! verified from their versions over the permission's parts
//! and the shared-reference functions (`ptr_shr_ref`, `ref_from_parts`,
//! `ref_to_parts`, `mut_ref_as_shr_ref`).
#![allow(unused_imports)]

use super::super::prelude::*;
use super::abstract_bytes::*;
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

/// Calls [`core::ptr::write`] to write the value `v` to the memory location pointed to by `ptr`,
/// using the permission `perm`.
///
/// This does _not_ drop the contents. If the memory is already initialized,
/// this could leak allocations or resources, so care should be taken to not overwrite an object that should be dropped.
/// This is appropriate for initializing uninitialized memory, or overwriting memory that has previously been [read](ptr_mut_read) from.
#[cfg(not(verus_verify_core))]
#[inline(always)]
pub fn ptr_mut_write<T>(ptr: *mut T, Tracked(perm): Tracked<&mut PointsTo<T>>, v: T)
    requires
        old(perm).ptr() == ptr,
        old(perm).wf(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_valid(),
        final(perm).value() == v,
        final(perm).wf(),
    opens_invariants none
    no_unwind
{
    // Drop the old value from the permission, then write the bytes.
    proof {
        perm.leak_contents();
    }
    let ghost empty = *perm;
    proof {
        PointsTo::<T>::lemma_pt_parts_wf(empty);
    }
    let tracked (pt_untyped, _) = perm.as_raw_parts_mut().as_raw_parts_mut();
    let Tracked(val) = unsafe { ptr_write_untyped(ptr, v, Tracked(pt_untyped)) };
    proof {
        PointsTo::<T>::lemma_pt_parts_wf(*perm);
        encode_decode_inverse(&val);
        perm.put(val);
    }
}

/// Calls [`core::ptr::read`] to read from the memory pointed to by `ptr`,
/// using the permission `perm`.
///
/// This leaves the data as "unitialized", i.e., performs a move.
///
/// TODO: This needs to be made more general (i.e., should be able to read a Copy type
/// without destroying it; should be able to leave the bytes intact without uninitializing them).
#[cfg(not(verus_verify_core))]
#[inline(always)]
pub const fn ptr_mut_read<T>(ptr: *const T, Tracked(perm): Tracked<&mut PointsTo<T>>) -> (v: T)
    requires
        old(perm).ptr() == ptr,
        old(perm).is_valid(),
        old(perm).wf(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).bytes() == old(perm).bytes(),
        final(perm).is_empty(),
        final(perm).wf(),
        v == old(perm).value(),
    opens_invariants none
    no_unwind
{
    // Move the value out of the permission, then read it from the bytes.
    proof {
        PointsTo::<T>::lemma_pt_parts_wf(*perm);
    }
    let tracked val = perm.take();
    proof {
        PointsTo::<T>::lemma_pt_parts_wf(*perm);
    }
    let tracked pt_untyped = perm.tracked_pt_unaligned().tracked_pt_untyped();
    unsafe { ptr_read_untyped(ptr, Tracked(pt_untyped), Tracked(val)) }
}

/// A shared reference at a real pointer gives a shared, valid permission for its memory, at its pointer.
#[verifier::shadow_data]
pub proof fn shr_ref_points_to<'a, T>(tracked r: &'a T) -> (tracked pt: &'a PointsTo<T>)
    requires
        shared_ref_ptr(shadow_data(r))@.is_real,
    ensures
        pt.ptr() == shared_ref_ptr(shadow_data(r)),
        pt.is_valid(),
        pt.typed_value().value_ref() == r,
        pt.wf(),
{
    let tracked (pt_untyped, typed_value) = ref_to_parts(r);
    points_to_from_parts_ref(shared_ref_ptr(shadow_data(r)) as *mut T, pt_untyped, typed_value)
}

/// A shared slice reference at a real pointer gives a shared, valid permission for its memory,
/// at its pointer.
#[verifier::shadow_data]
pub proof fn shr_ref_points_to_slice<'a, T>(tracked r: &'a [T]) -> (tracked pt: &'a PointsTo<[T]>)
    requires
        shared_ref_ptr(shadow_data(r))@.is_real,
    ensures
        pt.ptr() == shared_ref_ptr(shadow_data(r)),
        pt.is_valid(),
        pt.typed_value().value_ref() == r,
        pt.wf(),
{
    let tracked (pt_untyped, typed_value) = ref_to_parts_slice(r);
    points_to_from_parts_ref_slice(
        shared_ref_ptr(shadow_data(r)) as *mut [T],
        pt_untyped,
        typed_value,
    )
}

/// The length of a `&[T]` at a real pointer matches the metadata of its pointer.
#[verifier::shadow_data]
pub proof fn shr_ref_slice_len<T>(tracked r: &[T])
    requires
        shared_ref_ptr(shadow_data(r))@.is_real,
    ensures
        shared_ref_ptr(shadow_data(r))@.metadata == r@.len(),
{
    let tracked (pt_untyped, typed_value) = ref_to_parts_slice(r);
}

/// The length of a `&mut [T]` at a real pointer should always match the metadata of its corresponding pointer.
#[verifier::shadow_data]
pub proof fn mut_ref_slice_len<T>(tracked b: &&mut [T])
    requires
        mut_ref_ptr(*b)@.is_real,
    ensures
        mut_ref_ptr(*b)@.metadata == old(*b)@.len(),
{
    let tracked r = mut_ref_as_shr_ref(b);
    shr_ref_slice_len(r);
}

/// Convert from a shared reference to a `&'a mut T` at a real pointer to a `&'a PointsTo<T>`.
#[cfg(not(verus_verify_core))]
#[verifier::shadow_data]
pub proof fn mut_ref_to_shr_points_to<'a, T>(tracked mut_ref: &'a &'a mut T) -> (tracked pt:
    &'a PointsTo<T>)
    requires
        mut_ref_ptr(*mut_ref)@.is_real,
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

/// Convert from a shared reference to a `&'a mut [T]` at a real pointer to a `&'a PointsTo<[T]>`.
#[cfg(not(verus_verify_core))]
#[verifier::shadow_data]
pub proof fn mut_ref_to_shr_points_to_slice<'a, T>(tracked mut_ref: &'a &'a mut [T]) -> (tracked pt:
    &'a PointsTo<[T]>)
    requires
        mut_ref_ptr(*mut_ref)@.is_real,
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
