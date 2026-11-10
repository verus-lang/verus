#![allow(unused_imports)]

use super::super::layout::*;
use super::super::prelude::*;
use super::points_to_model::*;
use super::ptr_model::*;

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
#[cfg(not(verus_verify_core))]
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
#[cfg(not(verus_verify_core))]
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
/// Equivalent to `&*ptr`, given a tracked shared reference `r` with the pointer `ptr`.
#[inline(always)]
#[verifier::shadow_data]
#[verifier::external_body]
pub const fn ptr_shr_ref<'a, T: ?Sized>(ptr: *const T, Tracked(r): Tracked<&'a T>) -> (v: &'a T)
    requires
        shared_ref_ptr(shadow_data(r)) == ptr,
    ensures
        v == r,
        ptr_eq_up_to_tag(ptr, shared_ref_ptr(shadow_data(v))),
    opens_invariants none
    no_unwind
{
    unsafe { &*ptr }
}

/// A shared reference gives the parts of a shared permission for its memory, at its pointer.
#[verifier::shadow_data]
pub axiom fn ref_to_parts<'a, T>(tracked r: &'a T) -> (tracked (pt_untyped, typed_value): (
    &'a PointsToUntyped,
    &'a TypedValue<T>,
))
    ensures
        pt_parts_wf(shared_ref_ptr(shadow_data(r))@, *pt_untyped, *typed_value),
        typed_value.is_valid(),
        typed_value.value_ref() == r,
;

/// A shared slice reference gives the parts of a shared permission for its memory, at its pointer.
#[verifier::shadow_data]
pub axiom fn ref_to_parts_slice<'a, T>(tracked r: &'a [T]) -> (tracked (pt_untyped, typed_value): (
    &'a PointsToUntyped,
    &'a TypedValue<[T]>,
))
    ensures
        pt_parts_wf_slice(shared_ref_ptr(shadow_data(r))@, *pt_untyped, *typed_value),
        typed_value.is_valid(),
        typed_value.value_ref() == r,
;

/// The valid value of a permission's parts, borrowed as a `&T` at `ptr`.
#[verifier::shadow_data]
pub axiom fn ref_from_parts<'a, T>(
    ptr: *const T,
    tracked pt_untyped: &'a PointsToUntyped,
    tracked typed_value: &'a TypedValue<T>,
) -> (tracked r: &'a T)
    requires
        pt_parts_wf(ptr@, *pt_untyped, *typed_value),
        typed_value.is_valid(),
    ensures
        r == typed_value.value_ref(),
        shared_ref_ptr(shadow_data(r)) == ptr,
;

/// The valid value of a slice permission's parts, borrowed as a `&[T]` at `ptr`.
#[verifier::shadow_data]
pub axiom fn ref_from_parts_slice<'a, T>(
    ptr: *const [T],
    tracked pt_untyped: &'a PointsToUntyped,
    tracked typed_value: &'a TypedValue<[T]>,
) -> (tracked r: &'a [T])
    requires
        pt_parts_wf_slice(ptr@, *pt_untyped, *typed_value),
        typed_value.is_valid(),
    ensures
        r == typed_value.value_ref(),
        shared_ref_ptr(shadow_data(r)) == ptr,
;

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
            #[cfg(not(verus_verify_core))]
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
pub uninterp spec fn shared_ref_ptr<T: core::marker::PointeeSized>(s: ShadowData<&T>) -> *const T;

////////////////////////////////////////
// Shadow data of compound values
////////////////////////////////////////
/// The shadow data of `Tracked(x)`, given the shadow data of `x`.
pub uninterp spec fn tracked_shadow<T>(s: ShadowData<T>) -> ShadowData<Tracked<T>>;

/// The shadow data of `t@`, given the shadow data of `t`.
pub uninterp spec fn untracked_shadow<T>(s: ShadowData<Tracked<T>>) -> ShadowData<T>;

/// The shadow data of `(a, b)`, given the shadow data of `a` and of `b`.
pub uninterp spec fn pair_shadow<A, B>(a: ShadowData<A>, b: ShadowData<B>) -> ShadowData<(A, B)>;

/// The shadow data of `p.0`, given the shadow data of `p`.
pub uninterp spec fn pair_shadow_0<A, B>(s: ShadowData<(A, B)>) -> ShadowData<A>;

/// The shadow data of `p.1`, given the shadow data of `p`.
pub uninterp spec fn pair_shadow_1<A, B>(s: ShadowData<(A, B)>) -> ShadowData<B>;

pub broadcast axiom fn axiom_untracked_shadow<T>(s: ShadowData<T>)
    ensures
        #[trigger] untracked_shadow(tracked_shadow(s)) == s,
;

pub broadcast axiom fn axiom_pair_shadow_0<A, B>(a: ShadowData<A>, b: ShadowData<B>)
    ensures
        #[trigger] pair_shadow_0(pair_shadow(a, b)) == a,
;

pub broadcast axiom fn axiom_pair_shadow_1<A, B>(a: ShadowData<A>, b: ShadowData<B>)
    ensures
        #[trigger] pair_shadow_1(pair_shadow(a, b)) == b,
;

pub broadcast group group_shadow_data_axioms {
    axiom_untracked_shadow,
    axiom_pair_shadow_0,
    axiom_pair_shadow_1,
}

/// Wraps `x` in `Tracked`, keeping its shadow data.
#[verifier::shadow_data]
#[verifier::external_body]
pub const fn tracked_with_shadow<T>(x: T) -> (t: Tracked<T>)
    ensures
        t@ == x,
        shadow_data(t) == tracked_shadow(shadow_data(x)),
{
    core::mem::forget(x);
    Tracked::assume_new()
}

/// Unwraps `t`, keeping its shadow data.
#[verifier::shadow_data]
#[verifier::external_body]
pub proof fn untracked_with_shadow<T>(tracked t: Tracked<T>) -> (tracked x: T)
    ensures
        x == t@,
        shadow_data(x) == untracked_shadow(shadow_data(t)),
{
    t.get()
}

/// Builds the pair `(a, b)`, keeping the shadow data of `a` and `b`.
#[verifier::shadow_data]
#[verifier::external_body]
pub const fn pair_with_shadow<A, B>(a: A, b: B) -> (p: (A, B))
    ensures
        p == (a, b),
        shadow_data(p) == pair_shadow(shadow_data(a), shadow_data(b)),
{
    (a, b)
}

/// Gets `p.0`, keeping its shadow data.
#[verifier::shadow_data]
#[verifier::external_body]
pub const fn pair_0_with_shadow<A: Copy, B: Copy>(p: (A, B)) -> (a: A)
    ensures
        a == p.0,
        shadow_data(a) == pair_shadow_0(shadow_data(p)),
{
    p.0
}

/// Gets `p.1`, keeping its shadow data.
#[verifier::shadow_data]
#[verifier::external_body]
pub const fn pair_1_with_shadow<A: Copy, B: Copy>(p: (A, B)) -> (b: B)
    ensures
        b == p.1,
        shadow_data(b) == pair_shadow_1(shadow_data(p)),
{
    p.1
}

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
        ptr_mut_eq_up_to_tag(ptr, mut_ref_ptr(v)),
    opens_invariants none
    no_unwind
{
    unsafe { &mut *ptr }
}

/// Borrows a `&'a mut T` as a `&'a T` at the same pointer.
#[verifier::shadow_data]
pub axiom fn mut_ref_as_shr_ref<'a, T: ?Sized>(tracked mut_ref: &'a &'a mut T) -> (tracked r: &'a T)
    ensures
        r == &*old(*mut_ref),
        &*final(*mut_ref) == &*old(*mut_ref),
        shared_ref_ptr(shadow_data(r)) == mut_ref_ptr(*mut_ref),
;

/// This takes a mutable borrow of the `T` at `ptr`
/// from mutable borrows of the parts of a `PointsTo<T>` (`pt_untyped` and `typed_value`).
///
/// Writing through the reference updates both the value and the underlying bytes,
/// so the final parts are well-formed with bytes that decode to the final value.
// This is an axiom because the bytes live in separate ghost state from the `TypedValue<T>`,
// so they can't be updated through a borrow of the value alone.
pub axiom fn mut_ref_from_parts<'a, T>(
    ptr: *mut T,
    tracked pt_untyped: &'a mut PointsToUntyped,
    tracked typed_value: &'a mut TypedValue<T>,
) -> (tracked val: &'a mut T)
    requires
        pt_parts_wf(ptr@, *old(pt_untyped), *old(typed_value)),
        old(typed_value).is_valid(),
    ensures
        &*val == old(typed_value).value_ref(),
        mut_ref_ptr(val) == ptr,
        final(pt_untyped).ptr() == old(pt_untyped).ptr(),
        final(typed_value).is_valid(),
        final(typed_value).value_ref() == &*final(val),
        pt_parts_wf(ptr@, *final(pt_untyped), *final(typed_value)),
;

/// This takes a mutable borrow of the `[T]` at `ptr`
/// from mutable borrows of the parts of a `PointsTo<[T]>` (`pt_untyped` and `typed_value`).
///
/// Writing through the reference updates both the elements and the underlying bytes,
/// so the final parts are well-formed with bytes that decode to the final elements.
// This is an axiom because the bytes live in separate ghost state from the `TypedValue<[T]>`,
// so they can't be updated through a borrow of the value alone.
// TODO: merge with `mut_ref_from_parts` into one generic axiom over `T: ?Sized`
// (with a generic `pt_parts_wf` and the final wf under `additional_validity_constraints`, for `str`)
// once Verus knows that a `&mut [T]`'s final length equals its current length.
pub axiom fn mut_ref_from_parts_slice<'a, T>(
    ptr: *mut [T],
    tracked pt_untyped: &'a mut PointsToUntyped,
    tracked typed_value: &'a mut TypedValue<[T]>,
) -> (tracked val: &'a mut [T])
    requires
        pt_parts_wf_slice(ptr@, *old(pt_untyped), *old(typed_value)),
        old(typed_value).is_valid(),
    ensures
        &*val == old(typed_value).value_ref(),
        mut_ref_ptr(val) == ptr,
        final(pt_untyped).ptr() == old(pt_untyped).ptr(),
        final(typed_value).is_valid(),
        final(typed_value).value_ref() == &*final(val),
        pt_parts_wf_slice(ptr@, *final(pt_untyped), *final(typed_value)),
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

/// Two pointers are equal up to their tags:
/// they have the same address, metadata, and provenance apart from the tag.
pub open spec fn ptr_mut_eq_up_to_tag<T: ?Sized>(p: *mut T, q: *mut T) -> bool {
    &&& p.addr() == q.addr()
    &&& provenance_eq_up_to_tag(p@.provenance, q@.provenance)
    &&& p@.metadata == q@.metadata
}

/// Two `*const` pointers are equal up to their tags.
/// Since `*mut T` and `*const T` are [semantically the same](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/index.html#pointer-model),
/// we can define this operation in terms of the operation on `*mut T`.
#[verifier::inline]
pub open spec fn ptr_eq_up_to_tag<T: ?Sized>(p: *const T, q: *const T) -> bool {
    ptr_mut_eq_up_to_tag(p as *mut T, q as *mut T)
}

/// Convert a mutable reference into a raw pointer and
/// an accompanying tracked mutable reference at that pointer.
///
/// Conceptually, turning a mut ref into a ptr is just splitting it into exec and tracked components.
/// Ideally, we wouldn't need a dedicated function for doing both of these things; we would just
/// model the exec operation turning a mut ref into a pointer, and then getting the tracked mut ref
/// by mode coercion.
///
/// However, the actual operation still requires a (nondeterministic) retag, so we need one function
/// that produces both the raw pointer and the permission and ties the fresh pointer values together.
#[verifier::external_body]
pub const fn cast_mut_ref_to_ptr<T>(mut_ref: &mut T) -> ((ptr, perm): (*mut T, Tracked<&mut T>))
    ensures
        ptr_mut_eq_up_to_tag(ptr, mut_ref_ptr(mut_ref)),
        mut_ref_ptr(perm@) == ptr,
        &**perm == &*old(mut_ref),
        &*final(perm@) == &*final(mut_ref),
{
    (mut_ref as *mut T, Tracked::assume_new())
}

/// Convert a mutable reference to a slice into a raw pointer and
/// an accompanying tracked mutable reference at that pointer.
#[verifier::external_body]
pub const fn cast_mut_ref_slice_to_ptr<T>(mut_ref: &mut [T]) -> ((ptr, perm): (
    *mut [T],
    Tracked<&mut [T]>,
))
    ensures
        ptr_mut_eq_up_to_tag(ptr, mut_ref_ptr(mut_ref)),
        mut_ref_ptr(perm@) == ptr,
        &**perm == &*old(mut_ref),
        &*final(perm@) == &*final(mut_ref),
{
    (mut_ref as *mut [T], Tracked::assume_new())
}

/// Convert a mutable reference to a `str` into a raw pointer and
/// an accompanying tracked mutable reference at that pointer.
#[verifier::external_body]
pub const fn cast_mut_ref_str_to_ptr(mut_ref: &mut str) -> ((ptr, perm): (
    *mut str,
    Tracked<&mut str>,
))
    ensures
        ptr_mut_eq_up_to_tag(ptr, mut_ref_ptr(mut_ref)),
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
        ptr@.provenance.unwrap().alloc_id()
            == global_alloc_id(),
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
