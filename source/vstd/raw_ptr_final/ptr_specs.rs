#![allow(unused_imports)]

use super::points_to_model::*;
use super::ptr_model::*;
use super::super::layout::*;
use super::super::prelude::*;

verus! {

//////////////////////////////////////
// Pointer comparison functions
//////////////////////////////////////
/// Compares the address and metadata of two pointers.
///
/// Note that this does NOT compare provenance, which does not exist in the runtime
/// pointer representation (i.e., it only exists in the Rust abstract machine).
#[cfg(verus_keep_ghost)]
pub assume_specification<T: core::marker::PointeeSized>[ <*mut T as PartialEq<*mut T>>::eq ](
    x: &*mut T,
    y: &*mut T,
) -> (res: bool)
    ensures
        res <==> (x@.addr == y@.addr) && (x@.metadata == y@.metadata),
;

/// Compares the address and metadata of two pointers.
///
/// Note that this does NOT compare provenance, which does not exist in the runtime
/// pointer representation (i.e., it only exists in the Rust abstract machine).
#[cfg(verus_keep_ghost)]
pub assume_specification<T: core::marker::PointeeSized>[ <*const T as PartialEq<*const T>>::eq ](
    x: &*const T,
    y: &*const T,
) -> (res: bool)
    ensures
        res <==> (x@.addr == y@.addr) && (x@.metadata == y@.metadata),
;

//////////////////////////////////////
// Specifications for null pointers
//////////////////////////////////////
/// Constructs a null pointer.
/// NOTE: Trait aliases are not yet supported,
/// so we use `Pointee<Metadata = ()>` instead of `core::ptr::Thin` here
#[verifier::inline]
pub open spec fn ptr_null<
    T: ::core::marker::PointeeSized + core::ptr::Pointee<Metadata = ()>,
>() -> *const T {
    ptr_from_data(PtrData::<T> { addr: 0, provenance: Provenance::None, metadata: () })
}

#[cfg(verus_keep_ghost)]
#[verifier::when_used_as_spec(ptr_null)]
pub assume_specification<
    T: core::marker::PointeeSized + core::ptr::Pointee<Metadata = ()>,
>[ core::ptr::null ]() -> (res: *const T)
    ensures
        res == ptr_null::<T>(),
    opens_invariants none
    no_unwind
;

/// Constructs a mutable null pointer.
/// NOTE: Trait aliases are not yet supported,
/// so we use `Pointee<Metadata = ()>` instead of `core::ptr::Thin` here
#[verifier::inline]
pub open spec fn ptr_null_mut<
    T: core::marker::PointeeSized + core::ptr::Pointee<Metadata = ()>,
>() -> *mut T {
    ptr_mut_from_data(PtrData::<T> { addr: 0, provenance: Provenance::None, metadata: () })
}

#[cfg(verus_keep_ghost)]
#[verifier::when_used_as_spec(ptr_null_mut)]
pub assume_specification<
    T: core::marker::PointeeSized + core::ptr::Pointee<Metadata = ()>,
>[ core::ptr::null_mut ]() -> (res: *mut T)
    ensures
        res == ptr_null_mut::<T>(),
    opens_invariants none
    no_unwind
;

/////////////////////////////////////////////////////////////////////////////////////
// Casting: as-casts and implicit casts are translated internally to these functions
/////////////////////////////////////////////////////////////////////////////////////
// (including casts that involve *const ptrs)
/// Cast a pointer to a thin pointer. Address and provenance are preserved; metadata is now thin.
pub open spec fn spec_cast_ptr_to_thin_ptr<T: ?Sized, U: Sized>(ptr: *mut T) -> *mut U {
    ptr_mut_from_data(PtrData::<U> { addr: ptr@.addr, provenance: ptr@.provenance, metadata: () })
}

/// Cast a pointer to a thin pointer. Address and provenance are preserved; metadata is now thin.
///
/// Don't call this directly; use an `as`-cast instead.
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::raw_ptr::cast_ptr_to_thin_ptr")]
#[verifier::when_used_as_spec(spec_cast_ptr_to_thin_ptr)]
pub fn cast_ptr_to_thin_ptr<T: ?Sized, U: Sized>(ptr: *mut T) -> (result: *mut U)
    ensures
        result == spec_cast_ptr_to_thin_ptr::<T, U>(ptr),
    opens_invariants none
    no_unwind
{
    ptr as *mut U
}

/// Cast a pointer to an array of length `N` to a slice pointer.
/// Address and provenance are preserved; metadata has length `N`.
pub open spec fn spec_cast_array_ptr_to_slice_ptr<T, const N: usize>(ptr: *mut [T; N]) -> *mut [T] {
    ptr_mut_from_data(PtrData::<[T]> { addr: ptr@.addr, provenance: ptr@.provenance, metadata: N })
}

/// Cast a pointer to an array of length `N` to a slice pointer.
/// Address and provenance are preserved; metadata has length `N`.
///
/// Don't call this directly; use an `as`-cast instead.
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::raw_ptr::cast_array_ptr_to_slice_ptr")]
#[verifier::when_used_as_spec(spec_cast_array_ptr_to_slice_ptr)]
pub fn cast_array_ptr_to_slice_ptr<T, const N: usize>(ptr: *mut [T; N]) -> (result: *mut [T])
    ensures
        result == spec_cast_array_ptr_to_slice_ptr(ptr),
    opens_invariants none
    no_unwind
{
    ptr as *mut [T]
}

/// Cast a slice pointer to another slice pointer.
/// Length is preserved even if the size of the elements changes.
/// <https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.pointer.unsized.unchanged>
pub open spec fn spec_cast_slice_ptr_to_slice_ptr<T, U>(ptr: *mut [T]) -> *mut [U] {
    ptr_mut_from_data(
        PtrData::<[U]> { addr: ptr@.addr, provenance: ptr@.provenance, metadata: ptr@.metadata },
    )
}

/// Cast a slice pointer to another slice pointer.
/// Length is preserved even if the size of the elements changes.
/// <https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.pointer.unsized.unchanged>
///
/// Don't call this directly; use an `as`-cast instead.
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::raw_ptr::cast_slice_ptr_to_slice_ptr")]
#[verifier::when_used_as_spec(spec_cast_slice_ptr_to_slice_ptr)]
pub fn cast_slice_ptr_to_slice_ptr<T, U>(ptr: *mut [T]) -> (result: *mut [U])
    ensures
        result == spec_cast_slice_ptr_to_slice_ptr::<T, U>(ptr),
    opens_invariants none
    no_unwind
{
    ptr as *mut [U]
}

/// Cast a slice pointer to a `str` pointer.
/// Length is preserved even if the size of the elements changes.
/// <https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.pointer.unsized.unchanged>
pub open spec fn spec_cast_slice_ptr_to_str_ptr<T>(ptr: *mut [T]) -> *mut str {
    ptr_mut_from_data(
        PtrData::<str> { addr: ptr@.addr, provenance: ptr@.provenance, metadata: ptr@.metadata },
    )
}

/// Cast a slice pointer to a `str` pointer.
/// Length is preserved even if the size of the elements changes.
/// <https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.pointer.unsized.unchanged>
///
/// Don't call this directly; use an `as`-cast instead.
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::raw_ptr::cast_slice_ptr_to_str_ptr")]
#[verifier::when_used_as_spec(spec_cast_slice_ptr_to_str_ptr)]
pub fn cast_slice_ptr_to_str_ptr<T>(ptr: *mut [T]) -> (result: *mut str)
    ensures
        result == spec_cast_slice_ptr_to_str_ptr::<T>(ptr),
    opens_invariants none
    no_unwind
{
    ptr as *mut str
}

/// Cast a `str` pointer to a slice pointer.
/// Length is preserved even if the size of the elements changes.
/// <https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.pointer.unsized.unchanged>
pub open spec fn spec_cast_str_ptr_to_slice_ptr<T>(ptr: *mut str) -> *mut [T] {
    ptr_mut_from_data(
        PtrData::<[T]> { addr: ptr@.addr, provenance: ptr@.provenance, metadata: ptr@.metadata },
    )
}

/// Cast a `str` pointer to a slice pointer.
/// Length is preserved even if the size of the elements changes.
/// <https://doc.rust-lang.org/reference/expressions/operator-expr.html#r-expr.as.pointer.unsized.unchanged>
///
/// Don't call this directly; use an `as`-cast instead.
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::raw_ptr::cast_str_ptr_to_slice_ptr")]
#[verifier::when_used_as_spec(spec_cast_str_ptr_to_slice_ptr)]
pub fn cast_str_ptr_to_slice_ptr<T>(ptr: *mut str) -> (result: *mut [T])
    ensures
        result == spec_cast_str_ptr_to_slice_ptr::<T>(ptr),
    opens_invariants none
    no_unwind
{
    ptr as *mut [T]
}

/// Cast a pointer to a `usize` by extracting just the address.
pub open spec fn spec_cast_ptr_to_usize<T: Sized>(ptr: *mut T) -> usize {
    ptr@.addr
}

/// Return the address of a pointer.
// TODO: remove once Travis's fix is in for diagnostic item conflict
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::raw_ptr::spec_ptr_addr")]
#[verifier::inline]
pub open spec fn spec_ptr_addr<T: Sized>(ptr: *mut T) -> usize {
    spec_cast_ptr_to_usize(ptr)
}

/// Cast the address of a pointer to a `usize`.
///
/// Don't call this directly; use an `as`-cast instead.
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::raw_ptr::cast_ptr_to_usize")]
#[verifier::when_used_as_spec(spec_cast_ptr_to_usize)]
pub fn cast_ptr_to_usize<T: Sized>(ptr: *mut T) -> (result: usize)
    ensures
        result == spec_cast_ptr_to_usize(ptr),
    opens_invariants none
    no_unwind
{
    ptr as usize
}

////////////////////////////////////////////////
// Pointer reference and dereference operations
////////////////////////////////////////////////
/// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
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
    unsafe { &*ptr }
}

// /// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
// /// The memory pointed to by `ptr` must be initialized.
// TODO: move to rustlib
// #[inline(always)]
// #[verifier::external_body]
// pub const fn ptr_ref_str(ptr: *const str, Tracked(perm): Tracked<&PointsTo<str>>) -> (v: &str)
//     requires
//         perm.ptr() == ptr,
//         perm.is_valid(),
//     ensures
//         v == perm.value(),
//     opens_invariants none
//     no_unwind
// {
//     unsafe { &*ptr }
// }
/// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_ref_slice<T>(ptr: *const [T], Tracked(perm): Tracked<&PointsTo<[T]>>) -> (v: &[T])
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v@ == perm.typed_value().value_ref()@,
    opens_invariants none
    no_unwind
{
    unsafe { &*ptr }
}

/// Equivalent to `&mut *ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
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
    unsafe { &mut *ptr }
}

/// Equivalent to `&mut *ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_mut_ref_slice<T>(ptr: *mut [T], Tracked(perm): Tracked<&mut PointsTo<[T]>>) -> (v: &mut [T])
    requires
        old(perm).ptr() == ptr,
        old(perm).is_valid(),
        old(perm).wf(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_valid(),
        // The final bytes decode to the final value.
        final(perm).wf(),
        old(perm).typed_value().value_ref()@ == v@,
        final(perm).typed_value().value_ref()@ == final(v)@,
    opens_invariants none
    no_unwind
{
    unsafe { &mut *ptr }
}

// /// Equivalent to `&mut *ptr`, passing in a permission `perm` to ensure safety.
// /// The memory pointed to by `ptr` must be initialized.
// TODO: move to rustlib
// #[inline(always)]
// #[verifier::external_body]
// pub const fn ptr_mut_ref_str(ptr: *mut str, Tracked(perm): Tracked<&mut PointsTo<str>>) -> (v:
//     &mut str)
//     requires
//         old(perm).ptr() == ptr,
//         old(perm).is_valid(),
//     ensures
//         final(perm).ptr() == ptr,
//         final(perm).is_valid(),
//         old(perm).value() == &*v,
//         final(perm).value() == &*final(v),
//     opens_invariants none
//     no_unwind
// {
//     unsafe { &mut *ptr }
// }
//////////////////////////////////////////////////////
// Specifications for `ptr::addr` and `ptr::with_addr`
//////////////////////////////////////////////////////
macro_rules! pointer_specs {
    ($mod_ident:ident, $ptr_from_data:ident, $mu:tt) => {
        #[cfg(verus_keep_ghost)]
        mod $mod_ident {
            use super::*;

            verus!{

            /// Returns the address of a pointer.
            #[verifier::inline]
            pub open spec fn spec_addr<T: ::core::marker::PointeeSized>(p: *$mu T) -> usize { p@.addr }

            #[verifier::when_used_as_spec(spec_addr)]
            #[cfg(verus_keep_ghost)]
            pub assume_specification<T: ::core::marker::PointeeSized>[<*$mu T>::addr](p: *$mu T) -> (addr: usize)
                ensures addr == spec_addr(p)
                opens_invariants none
                no_unwind;

            /// Returns a pointer with the specified address and the same provenance and metadata of the input pointer.
            pub open spec fn spec_with_addr<T: ::core::marker::PointeeSized>(p: *$mu T, addr: usize) -> *$mu T {
                $ptr_from_data(PtrData::<T> { addr: addr, .. p@ })
            }

            #[verifier::when_used_as_spec(spec_with_addr)]
            #[cfg(verus_keep_ghost)]
            pub assume_specification<T: ::core::marker::PointeeSized>[<*$mu T>::with_addr](p: *$mu T, addr: usize) -> (q: *$mu T)
                ensures q == spec_with_addr(p, addr)
                opens_invariants none
                no_unwind;

            }
        }
    };
}

pointer_specs!(ptr_mut_specs, ptr_mut_from_data, mut);

pointer_specs!(ptr_const_specs, ptr_from_data, const);

////////////////////////////////////////
// Shared and mutable reference specs
////////////////////////////////////////
/// Extracts the pointer from the shadow data of a shared reference.
pub uninterp spec fn shared_ref_ptr<T: ?Sized>(s: ShadowData<&T>) -> *const T;

/// The length of a `&mut [T]` should always match the metadata of its corresponding pointer.
// TODO: define the equivalent shared ref version, using shadow data?
pub axiom fn mut_ref_slice_len<T>(tracked b: &&mut [T])
    ensures
        mut_ref_ptr(*b)@.metadata == old(*b)@.len(),
;

////////////////////////////////////////
// Mutable reference conversions
///////////////////////////////////////
/// Combine a pointer and a tracked `&mut T` to get an executable `&mut T`
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_mut_ref_join<T: ?Sized>(ptr: *mut T, Tracked(perm): Tracked<&mut T>) -> (v: &mut T)
    requires
        mut_ref_ptr(perm) == ptr,
    ensures
        &*v == &*old(perm),
        &*final(v) == &*final(perm),
        ptr_eq_up_to_tag(ptr, mut_ref_ptr(v)),
    opens_invariants none
    no_unwind
{
    unsafe { &mut *ptr }
}

/// Convert from a shared reference to a `&'a mut T` to a `&'a PointsTo<T>`.
pub axiom fn mut_ref_to_shr_points_to<'a, T>(tracked mut_ref: &'a &'a mut T) -> (tracked pt:
    &'a PointsTo<T>)
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_valid(),
        pt.value() == *old(*mut_ref),
        pt.wf(),
        *final(*mut_ref) == *old(*mut_ref),
;

/// Convert from a shared reference to a `&'a mut [T]` to a `&'a PointsTo<[T]>`.
pub axiom fn mut_ref_to_shr_points_to_slice<'a, T>(tracked mut_ref: &'a &'a mut [T])
    -> (tracked pt: &'a PointsTo<[T]>)
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_valid(),
        pt.typed_value().value_ref()@ == (*old(*mut_ref))@,
        pt.wf(),
        &*final(*mut_ref) == &*old(*mut_ref),
;

// TODO: move to rustlib
// /// Convert from a shared reference to a `&'a mut str` to a `&'a PointsTo<str>`.
// pub axiom fn mut_ref_to_shr_points_to_str<'a>(tracked mut_ref: &'a &'a mut str) -> (tracked pt:
//     &'a PointsTo<str>)
//     ensures
//         pt.ptr() == mut_ref_ptr(*mut_ref),
//         pt.is_valid(),
//         &pt.value() == &(*old(*mut_ref)),
//         &*final(*mut_ref) == &*old(*mut_ref),
// ;
/// Take a `&mut [T]` subrange of a `&mut [T]`.
pub axiom fn tracked_mut_ref_slice_subrange<T>(
    tracked mut_ref: &mut [T],
    i: int,
    j: int,
) -> (tracked sub_mut_ref: &mut [T])
    requires
        0 <= i <= j <= mut_ref@.len(),
    ensures
        mut_ref_ptr(sub_mut_ref)@.provenance == mut_ref_ptr(mut_ref)@.provenance,
        mut_ref_ptr(sub_mut_ref)@.metadata == j - i,
        mut_ref_ptr(sub_mut_ref).addr() == mut_ref_ptr(mut_ref).addr() + i * size_of::<T>(),
        sub_mut_ref@.len() == final(sub_mut_ref)@.len() == j - i,
        sub_mut_ref@ == (*old(mut_ref))@.subrange(i, j),
        (*final(mut_ref))@ == (*old(mut_ref))@.subrange(0, i) + (*final(sub_mut_ref))@ + (*old(
            mut_ref,
        ))@.subrange(j, old(mut_ref)@.len() as int),
;

/// Index into a `&mut [T]`, returning a `&mut T`.
pub axiom fn tracked_mut_ref_slice_idx<T>(
    tracked mut_ref: &mut [T],
    i: int,
) -> (tracked sub_mut_ref: &mut T)
    requires
        0 <= i < mut_ref@.len(),
    ensures
        mut_ref_ptr(sub_mut_ref)@.provenance == mut_ref_ptr(mut_ref)@.provenance,
        mut_ref_ptr(sub_mut_ref)@.metadata == (),
        mut_ref_ptr(sub_mut_ref).addr() == mut_ref_ptr(mut_ref).addr() + i * size_of::<T>(),
        *sub_mut_ref == (*old(mut_ref))@[i],
        (*final(mut_ref))@ == (*old(mut_ref))@.update(i, *final(sub_mut_ref)),
;

/// Conceptually, turning a mut ref into a ptr is just splitting it into exec and tracked components.
/// Ideally, we wouldn't need a dedicated function for doing both of these things; we would just
/// model the exec operation turning a mut ref into a pointer, and then getting the tracked mut ref
/// by mode coercion.
///
/// However, the actual operation still requires a (nondeterministic) retag, so we need one function
/// that produces both the raw pointer and the permission and ties the fresh pointer values together.
// TODO: add spatial provenance comparison
pub open spec fn ptr_eq_up_to_tag<T: ?Sized>(p: *mut T, q: *mut T) -> bool {
    p.addr() == q.addr() && p@.metadata
        == q@.metadata
    // should also compare the spatial elements of provenance, i.e., the non-tag
    // part of provenance

}

/// Convert a mutable reference into a raw pointer and accompanying `PointsTo` permission.
#[verifier::external_body]
pub const fn cast_mut_ref_to_ptr<T>(mut_ref: &mut T) -> ((ptr, perm): (*mut T, Tracked<&mut T>))
    ensures
        ptr_eq_up_to_tag(ptr, mut_ref_ptr(mut_ref)),
        mut_ref_ptr(perm@) == ptr,
        &**perm == &*old(mut_ref),
        &*final(perm@) == &*final(mut_ref),
{
    (mut_ref as *mut T, Tracked::assume_new())
}

/// Convert a mutable reference to a slice into a raw pointer and accompanying `PointsTo` permission.
#[verifier::external_body]
pub const fn cast_mut_ref_slice_to_ptr<T>(mut_ref: &mut [T]) -> ((ptr, perm): (
    *mut [T],
    Tracked<&mut [T]>,
))
    ensures
        ptr_eq_up_to_tag(ptr, mut_ref_ptr(mut_ref)),
        mut_ref_ptr(perm@) == ptr,
        &**perm == &*old(mut_ref),
        &*final(perm@) == &*final(mut_ref),
{
    (mut_ref as *mut [T], Tracked::assume_new())
}

/// Convert a mutable reference to a `str` into a raw pointer and accompanying `PointsTo` permission.
#[verifier::external_body]
pub const fn cast_mut_ref_str_to_ptr(mut_ref: &mut str) -> ((ptr, perm): (
    *mut str,
    Tracked<&mut str>,
))
    ensures
        ptr_eq_up_to_tag(ptr, mut_ref_ptr(mut_ref)),
        mut_ref_ptr(perm@) == ptr,
        &**perm == &*old(mut_ref),
        &*final(perm@) == &*final(mut_ref),
{
    (mut_ref as *mut str, Tracked::assume_new())
}

////////////////////////////////////////
// Allocation
////////////////////////////////////////
/// Allocate with the global allocator.
/// The precondition should be consistent with the
/// [documented safety conditions on `alloc`](https://doc.rust-lang.org/alloc/alloc/trait.GlobalAlloc.html#tymethod.alloc).
/// Returns a pointer with a corresponding [`PointsToUntyped`] permission.
/// The byte contents are arbitrary (uninitialized).
///
/// Here we allocate exactly the size of memory requested
/// (shown by having both the `Provenance` `orig_size` and `alloc_len` be the provided `size`).
/// This is a stronger guarantee than `Allocator::allocate`, which may allocate a larger block of memory.
#[cfg(feature = "std")]
#[verifier::external_body]
pub fn allocate(size: usize, align: usize) -> ((ptr, perm): (*mut u8, Tracked<PointsToUntyped>))
    requires
        valid_layout(size, align),
        size != 0,
    ensures
        perm@.ptr() == ptr_mut_from_data::<[u8]>(
            PtrData { addr: ptr@.addr, provenance: ptr@.provenance, metadata: size },
        ),
        perm@.wf(),
        ptr@.provenance is Some,
        ptr@.addr == ptr@.provenance.unwrap().start_addr(),
        ptr@.provenance.unwrap().alloc_len() == size,
        ptr@.provenance.unwrap().orig_size() == size,
        ptr@.provenance.unwrap().alignment() == align,
        ptr@.provenance.unwrap().alloc_id() == global_alloc_id(),
        // ptr@.addr % align == 0 and ptr@.addr + size <= usize::MAX follow from provenance_properties.
    opens_invariants none
{
    // SAFETY: valid_layout is a precondition
    let layout = unsafe { alloc::alloc::Layout::from_size_align_unchecked(size, align) };
    // SAFETY: size != 0
    let ptr = unsafe { ::alloc::alloc::alloc(layout) };
    if ptr == core::ptr::null_mut() {
        std::process::abort();
    }
    (ptr, Tracked::assume_new())
}

/// Deallocate with the global allocator.
///
/// The provenance ensures that the
/// [documented safety conditions on `dealloc`](https://doc.rust-lang.org/1.82.0/core/alloc/trait.GlobalAlloc.html#tymethod.dealloc)
/// are satisfied; by also giving up the [`PointsToUntyped`] permission for the whole allocation,
/// we ensure there can be no use-after-free bug as a result of this deallocation.
/// In order to do so, the parameters of the provenance and the [`PointsToUntyped`] permission
/// must match the parameters of the deallocation.
///
/// We have two different ways to track size within the provenance:
/// `orig_size`, the original requested size, and `alloc_len`, the size of memory actually allocated.
/// According to the `Allocator` documentation, it's possible to have `orig_size <= alloc_len`.
/// Here, we restrict them to be the same.
#[cfg(feature = "alloc")]
#[verifier::external_body]
pub fn deallocate(ptr: *mut u8, size: usize, align: usize, Tracked(perm): Tracked<PointsToUntyped>)
    requires
        perm.wf(),
        ptr@.provenance == perm.ptr()@.provenance,
        ptr@.addr == perm.ptr()@.addr,
        ptr@.provenance is Some,
        ptr@.provenance.unwrap().alloc_id() == global_alloc_id(),
        ptr@.addr == ptr@.provenance.unwrap().start_addr(),
        perm.len() == ptr@.provenance.unwrap().alloc_len(),
        size == ptr@.provenance.unwrap().orig_size(),
        align == ptr@.provenance.unwrap().alignment(),
    opens_invariants none
{
    // SAFETY: ensured by the provenance and the PointsToUntyped
    let layout = unsafe { alloc::alloc::Layout::from_size_align_unchecked(size, align) };
    unsafe {
        ::alloc::alloc::dealloc(ptr, layout);
    }
}

} // verus!
