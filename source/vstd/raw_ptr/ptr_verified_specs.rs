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
use super::shared_reference::*;

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
    proof {
        PointsTo::<T>::lemma_pt_parts_wf(*perm);
    }
    let tracked pt_unaligned = perm.tracked_pt_unaligned();
    let tracked r = ref_from_parts(
        ptr,
        pt_unaligned.tracked_pt_untyped(),
        pt_unaligned.tracked_typed_value(),
    );
    ptr_shr_ref(ptr, Tracked(r))
}

/// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
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
    proof {
        PointsTo::<[T]>::lemma_pt_parts_wf(*perm);
    }
    let tracked pt_unaligned = perm.tracked_pt_unaligned();
    let tracked r = ref_from_parts_slice(
        ptr,
        pt_unaligned.tracked_pt_untyped(),
        pt_unaligned.tracked_typed_value(),
    );
    ptr_shr_ref(ptr, Tracked(r))
}

/// Equivalent to `&mut *ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
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

/// Like [`ptr_ref`] but returns a `SharedReference` so it keeps track of the relationship
/// between the pointers.
/// Note the resulting reference's pointers does NOT have the same provenance.
/// This is because in Rust models like Stacked Borrows / Tree Borrows, the pointer
/// gets a new tag.
#[inline(always)]
pub fn ptr_ref2<'a, T>(ptr: *const T, Tracked(perm): Tracked<&PointsTo<T>>) -> (v: SharedReference<
    'a,
    T,
>)
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v.value() == perm.value(),
        ptr_eq_up_to_tag(v.ptr(), ptr),
    opens_invariants none
    no_unwind
{
    proof {
        PointsTo::<T>::lemma_pt_parts_wf(*perm);
    }
    let tracked pt_unaligned = perm.tracked_pt_unaligned();
    ptr_ref2_untyped_with_typed_value(
        ptr,
        Tracked(pt_unaligned.tracked_pt_untyped()),
        Tracked(pt_unaligned.tracked_typed_value()),
    )
}

/// Same as [`ptr_ref2`], but operates on ghost values.
/// Because this doesn't constitute a retag, the returned value's pointer has the same provenance as the original pointer.
pub proof fn ptr_ref2_ghost<'a, T>(ptr: *const T, tracked perm: &PointsTo<T>) -> (tracked v:
    SharedReference<'a, T>)
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v.value() == perm.value(),
        v.ptr() == ptr,
{
    PointsTo::<T>::lemma_pt_parts_wf(*perm);
    let tracked pt_unaligned = perm.tracked_pt_unaligned();
    ptr_ref2_ghost_untyped_with_typed_value(
        ptr,
        pt_unaligned.tracked_pt_untyped(),
        pt_unaligned.tracked_typed_value(),
    )
}

/// The ghost version of `ptr_ref2` for slices.
/// Because this doesn't constitute a retag,
/// the returned value's pointer has the same provenance as the original pointer.
pub proof fn ptr_ref2_slice_ghost<'a, T>(
    ptr: *const [T],
    tracked perm: &PointsTo<[T]>,
) -> (tracked v: SharedReference<'a, [T]>)
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v.value()@ == perm.value(),
        v.ptr() == ptr,
{
    PointsTo::<[T]>::lemma_pt_parts_wf(*perm);
    let tracked pt_unaligned = perm.tracked_pt_unaligned();
    ptr_ref2_slice_ghost_untyped_with_typed_value(
        ptr,
        pt_unaligned.tracked_pt_untyped(),
        pt_unaligned.tracked_typed_value(),
    )
}

impl<'a, T> SharedReference<'a, T> {
    // NOTE: there does not exist a points_to_unaligned function because SharedReference
    // by definition gives you an _aligned_ PointsTo.
    // https://doc.rust-lang.org/std/primitive.reference.html
    pub proof fn points_to(tracked self) -> (tracked pt: &'a PointsTo<T>)
        ensures
            pt.ptr() == self.ptr(),
            pt.is_valid(),
            pt.value() == self.value(),
            pt.wf(),
    {
        let ghost ptr = self.ptr();
        let tracked (pt_untyped, typed_value) = self.pt_untyped_and_typed_value();
        points_to_from_parts_ref(ptr as *mut T, pt_untyped, typed_value)
    }
}

impl<'a, T> SharedReference<'a, [T]> {
    /// A shared slice reference gives a shared, valid slice permission.
    pub proof fn points_to(tracked self) -> (tracked pt: &'a PointsTo<[T]>)
        ensures
            pt.ptr() == self.ptr(),
            pt.is_valid(),
            pt.value() == self.value()@,
            pt.wf(),
    {
        let ghost ptr = self.ptr();
        let tracked (pt_untyped, typed_value) = self.pt_untyped_and_typed_value();
        points_to_from_parts_ref_slice(ptr as *mut [T], pt_untyped, typed_value)
    }
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

/// Convert from a shared reference to a `&'a mut T` to a `&'a PointsTo<T>`.
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
