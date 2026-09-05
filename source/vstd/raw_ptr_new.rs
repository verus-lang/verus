//! Tools and reasoning principles for [raw pointers](https://doc.rust-lang.org/std/primitive.pointer.html).
//! The tools here are meant to address "real Rust pointers, including all their subtleties on the Rust Abstract Machine,
//! to the largest extent that is reasonable."
//!
//! For a gentler introduction to some of the concepts here, see [`PPtr`](crate::simple_pptr), which uses a much-simplified pointer model.
//!
//! ### Pointer model
//!
//! A pointer consists of an address (`ptr.addr()` or `ptr as usize`), a provenance `ptr@.provenance`,
//! and metadata `ptr@.metadata` (which is trivial except for pointers to non-sized types).
//! Note that in spec code, pointer equality requires *all 3* to be equal, whereas runtime equality (eq)
//! only compares addresses and metadata.
//!
//! `*mut T` vs. `*const T` do not have any semantic difference and Verus treats them as the same;
//! they can be seamlessly cast to and fro.
#![allow(unused_imports)]

#[cfg(verus_keep_ghost)]
use super::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use super::arithmetic::mul::*;
#[cfg(verus_keep_ghost)]
use super::arithmetic::power::pow;
use super::calc_macro::*;
use super::layout;
use super::layout::*;
use super::prelude::*;
use super::set::group_set_axioms;
#[cfg(verus_keep_ghost)]
use super::transmute::{group_transmute_axioms, transmute_post, transmute_pre_points_to};
#[cfg(verus_keep_ghost)]
use super::type_representation::*;
use crate::vstd::endian::*;
use crate::vstd::group_vstd_default;
use crate::vstd::seq::*;
use crate::vstd::slice::*;
use core::ops::Index;
use core::slice::SliceIndex;

verus! {

//////////////////////////////////////
// Define a model of Ptrs and PointsTo
// Notes on mutability:
//
//  - Unique vs shared ownership in Verus is always determined
//    via the PointsTo ghost tracked object.
//
//  - Thus, there is effectively no difference between *mut T and *const T,
//    so we encode both of these in the same way.
//    (In VIR, we distinguish these via a decoration.)
//    Thus we can cast freely between them both in spec and exec code.
//
//  - This is consistent with Rust's operational semantics;
//    casting between *mut T and *const T has no operational meaning.
//
//  - When creating a pointer from a reference, the mutability
//    of the pointer *does* have an effect because it determines
//    what kind of "tag" the pointer gets, i.e., whether that
//    tag is readonly or not. In our model here, this tag is folded
//    into the provenance.
//
/// Provenance
///
/// A full model of provenance is given by formalisms such as "Stacked Borrows"
/// or "Tree Borrows."
///
/// None of these models are finalized, nor has Rust committed to them.
/// Rust's recent [RFC on provenance](https://rust-lang.github.io/rfcs/3559-rust-has-provenance.html)
/// simply details that there *is* some concept of provenance.
///
/// Our model here, likewise, simply declares `Provenance` as an
/// abstract type.
///
/// MiniRust currently declares a pointer has an `Option<Provenance>`;
/// the model here gives provenance a special "null" value instead
/// of using an option.
///
/// More reading for reference:
/// * [https://doc.rust-lang.org/std/ptr/](https://doc.rust-lang.org/std/ptr/)
/// * [https://github.com/minirust/minirust/tree/master](https://github.com/minirust/minirust/tree/master)
pub type AllocId = int;

#[verifier::external_body]
pub ghost struct ProvenanceData {}

impl ProvenanceData {
    /// The starting address of the pointer's allocation.
    pub uninterp spec fn start_addr(&self) -> usize;

    /// The length of the pointer's allocation in bytes.
    pub uninterp spec fn alloc_len(&self) -> nat;

    /// The alignment of the pointer's allocation. Must be a power of 2 bounded by `isize::MAX + 1`.
    pub uninterp spec fn alignment(&self) -> nat;

    /// The ID of the `Allocator` instance used to allocate this memory.
    pub uninterp spec fn alloc_id(&self) -> AllocId;

    /// The originally requested allocation size.
    pub uninterp spec fn orig_size(&self) -> nat;
}

pub type Provenance = Option<ProvenanceData>;
// pub ghost enum Provenance {
//     /// Represents no memory allocation.
//     None,
//     /// Represents a memory allocation with the given `ProvenanceData`.
//     Some(ProvenanceData),
// }

// impl Provenance {
//     pub open spec fn is_none(self) -> bool {
//         self is None
//     }

//     pub open spec fn is_some(self) -> bool {
//         self is Some
//     }

//     pub closed spec fn data(self) -> ProvenanceData
//         recommends
//             self is Some,
//     {
//         self->0
//     }
// }

/// Allocations do not "wrap around" the address space.
/// From: <https://doc.rust-lang.org/std/ptr/index.html#allocation>:
/// For any allocation with `base` address and size `size`, the following are guaranteed:
/// - `base + size <= usize::MAX`
/// - `size <= isize::MAX`
pub broadcast axiom fn alloc_bound(p: ProvenanceData)
    ensures
        #![trigger p.start_addr()]
        #![trigger p.alloc_len()]
        p.start_addr() + p.alloc_len() <= usize::MAX,
        p.alloc_len() <= isize::MAX,
;

/// Since `self.alignment()` returns a `int`, `Alignment` invariants do not follow directly from the type.
/// We bring them in as an axiom, instead.
#[verusfmt::skip]
pub broadcast axiom fn prov_alignment(p: ProvenanceData)
    ensures
    // Weaker version: is_power_2_exists(self.alignment())
    // Taken directly from `alignment_properties`
    #![trigger p.alignment()]
    exists|i: nat|
        pow(2, i) == p.alignment() as int && i < isize::BITS && 0 < p.alignment() <= isize::MAX
            + 1,
;

/// The start address of an allocation should be aligned to the allocation's alignment,
/// as per the postcondition of `Allocator::allocate`.
pub broadcast axiom fn start_addr_aligned(p: ProvenanceData)
    ensures
        #[trigger] p.start_addr() as nat % #[trigger] p.alignment() == 0,
;

/// Allocations should always start with a non-null address, even zero-sized allocations.
/// `Allocator::allocate` returns a `NonNull` pointer, and documentation here
/// (<https://doc.rust-lang.org/1.88.0/core/alloc/trait.Allocator.html>)
/// implies that returning a null pointer should not happen.
/// Additionally, MiniRust's allocate cannot return a null address.
/// <https://github.com/minirust/minirust/blob/master/spec/mem/basic.md>
pub broadcast axiom fn is_nonnull(p: ProvenanceData)
    ensures
        #[trigger] p.start_addr() != 0,
;

pub broadcast axiom fn orig_size_bound(p: ProvenanceData)
    ensures
        p.orig_size() <= p.alloc_len(),
;

pub broadcast group group_provenance_properties {
    prov_alignment,
    alloc_bound,
    start_addr_aligned,
    is_nonnull,
    orig_size_bound,
}

/// Metadata
///
/// For thin pointers (i.e., when T: Sized), the metadata is `()`.
/// For slices (`[T]`) and `str`, the metadata is `usize`.
/// For `dyn` types (not supported by Verus at the time of writing), this type is also nontrivial.
///
/// See: <https://doc.rust-lang.org/std/ptr/trait.Pointee.html>
#[cfg(verus_keep_ghost)]
pub type Metadata<T> = <T as core::ptr::Pointee>::Metadata;

#[cfg(not(verus_keep_ghost))]
pub struct FakeMetadata<T: ?Sized> {
    t: *mut T,
}

#[cfg(not(verus_keep_ghost))]
pub type Metadata<T> = FakeMetadata<T>;

/// Model of a pointer `*mut T` or `*const T` in Rust's abstract machine.
/// In addition to the address, each pointer has its corresponding provenance and metadata.
#[cfg(verus_keep_ghost)]
pub ghost struct PtrData<T: core::marker::PointeeSized> {
    pub addr: usize,
    pub provenance: Provenance,
    pub metadata: Metadata<T>,
}

#[cfg(verus_keep_ghost)]
impl<T: core::marker::PointeeSized> View for *mut T {
    type V = PtrData<T>;

    uninterp spec fn view(&self) -> Self::V;
}

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

#[cfg(verus_keep_ghost)]
impl<T: core::marker::PointeeSized> View for *const T {
    type V = PtrData<T>;

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        (*self as *mut T).view()
    }
}

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
// Inverse functions:
// Pointers are equivalent to their model
/// Constructs a pointer from its underlying model.
pub uninterp spec fn ptr_mut_from_data<T: core::marker::PointeeSized>(data: PtrData<T>) -> *mut T;

/// Constructs a tracked pointer from the underlying data. This is safe because the pointer itself does contain store any tracked data.
pub axiom fn tracked_ptr_mut_from_data<T: ?Sized>(data: PtrData<T>) -> (tracked out: *mut T)
    ensures
        out == ptr_mut_from_data::<T>(data),
;

/// Constructs a pointer from its underlying model.
/// Since `*mut T` and `*const T` are [semantically the same](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/index.html#pointer-model),
/// we can define this operation in terms of the operation on `*mut T`.
#[verifier::inline]
pub open spec fn ptr_from_data<T: core::marker::PointeeSized>(data: PtrData<T>) -> *const T {
    ptr_mut_from_data(data) as *const T
}

/// The view of a pointer constructed from `data: PtrData` should be exactly that data.
pub broadcast axiom fn axiom_ptr_mut_from_data<T: ?Sized>(data: PtrData<T>)
    ensures
        (#[trigger] ptr_mut_from_data::<T>(data))@ == data,
;

// Equiv to ptr_mut_from_data, but named differently to avoid trigger issues
// Only use for ptrs_mut_eq
#[doc(hidden)]
pub uninterp spec fn view_reverse_for_eq<T: ?Sized>(data: PtrData<T>) -> *mut T;

/// Implies that `a@ == b@ ==> a == b`.
pub broadcast axiom fn ptrs_mut_eq<T: ?Sized>(a: *mut T)
    ensures
        view_reverse_for_eq::<T>(#[trigger] a@) == a,
;

// We do the same trick again, but specialized for Sized types. This improves automation.
// Specifically, this makes it easier to prove `a == b` without having to explicitly write
// `a@.metadata == b@.metadata`, since this condition is trivial; both values are always unit.
// (See the test_extensionality_sized test case.)
#[doc(hidden)]
pub closed spec fn view_reverse_for_eq_sized<T>(addr: usize, provenance: Provenance) -> *mut T {
    view_reverse_for_eq(PtrData { addr: addr, provenance: provenance, metadata: () })
}

pub broadcast proof fn ptrs_mut_eq_sized<T>(a: *mut T)
    ensures
        view_reverse_for_eq_sized::<T>((#[trigger] a@).addr, a@.provenance) == a,
{
    assert(a@.metadata == ());
    ptrs_mut_eq(a);
}

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

//////////////////////////////////////
// Casting
// as-casts and implicit casts are translated internally to these functions
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
pub open spec fn spec_cast_slice_ptr_to_slice_ptr<T, U>(ptr: *mut [T]) -> *mut [U] {
    ptr_mut_from_data(
        PtrData::<[U]> { addr: ptr@.addr, provenance: ptr@.provenance, metadata: ptr@.metadata },
    )
}

/// Cast a slice pointer to another slice pointer.
/// Length is preserved even if the size of the elements changes.
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
pub open spec fn spec_cast_str_ptr_to_slice_ptr<T>(ptr: *mut str) -> *mut [T] {
    ptr_mut_from_data(
        PtrData::<[T]> { addr: ptr@.addr, provenance: ptr@.provenance, metadata: ptr@.metadata },
    )
}

/// Cast a `str` pointer to a slice pointer.
/// Length is preserved even if the size of the elements changes.
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

//////////////////////////////////////
/// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_ref<T>(ptr: *const T, Tracked(perm): Tracked<&PointsTo<T>>) -> (v: &T)
    requires
        perm.ptr() == ptr,
        perm.is_init(),
    ensures
        v == perm.value(),
    opens_invariants none
    no_unwind
{
    unsafe { &*ptr }
}

/// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_ref_str(ptr: *const str, Tracked(perm): Tracked<&PointsTo<str>>) -> (v: &str)
    requires
        perm.ptr() == ptr,
        perm.is_init(),
    ensures
        v == perm.value(),
    opens_invariants none
    no_unwind
{
    unsafe { &*ptr }
}

/// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_ref_slice<T>(ptr: *const [T], Tracked(perm): Tracked<&PointsTo<[T]>>) -> (v: &[T])
    requires
        perm.ptr() == ptr,
        perm.is_init(),
    ensures
        v@ == perm.value(),
    opens_invariants none
    no_unwind
{
    unsafe { &*ptr }
}

/// Equivalent to `&mut *X`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_mut_ref<T>(ptr: *mut T, Tracked(perm): Tracked<&mut PointsTo<T>>) -> (v: &mut T)
    requires
        old(perm).ptr() == ptr,
        old(perm).is_init(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_init(),
        old(perm).value() == *v,
        final(perm).value() == *final(v),
    opens_invariants none
    no_unwind
{
    unsafe { &mut *ptr }
}

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

pub axiom fn mut_ref_slice_len<T>(tracked b: &&mut [T])
    ensures
        mut_ref_ptr(*b)@.metadata == old(*b)@.len(),
;

/// Equivalent to `&mut *X`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_mut_ref_slice<T>(ptr: *mut [T], Tracked(perm): Tracked<&mut PointsTo<[T]>>) -> (v:
    &mut [T])
    requires
        old(perm).ptr() == ptr,
        old(perm).is_init(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_init(),
        old(perm).value() == v@,
        final(perm).value() == final(v)@,
    opens_invariants none
    no_unwind
{
    unsafe { &mut *ptr }
}

/// Equivalent to `&mut *X`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_mut_ref_str(ptr: *mut str, Tracked(perm): Tracked<&mut PointsTo<str>>) -> (v:
    &mut str)
    requires
        old(perm).ptr() == ptr,
        old(perm).is_init(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_init(),
        old(perm).value() == &*v,
        final(perm).value() == &*final(v),
    opens_invariants none
    no_unwind
{
    unsafe { &mut *ptr }
}

macro_rules! pointer_specs {
    ($mod_ident:ident, $ptr_from_data:ident, $mu:tt) => {
        #[cfg(verus_keep_ghost)]
        mod $mod_ident {
            use super::*;

            verus!{

            #[verifier::inline]
            pub open spec fn spec_addr<T: ::core::marker::PointeeSized>(p: *$mu T) -> usize { p@.addr }

            #[verifier::when_used_as_spec(spec_addr)]
            #[cfg(verus_keep_ghost)]
            pub assume_specification<T: ::core::marker::PointeeSized>[<*$mu T>::addr](p: *$mu T) -> (addr: usize)
                ensures addr == spec_addr(p)
                opens_invariants none
                no_unwind;

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

pub broadcast group group_raw_ptr_axioms {
    axiom_ptr_mut_from_data,
    ptrs_mut_eq,
    ptrs_mut_eq_sized,
    axiom_pt_slice_len,
    axiom_pt_slice_unaligned_len,
    group_provenance_properties,
}

pub axiom fn mut_ref_to_shr_points_to<'a, T>(tracked mut_ref: &'a &'a mut T) -> (tracked pt:
    &'a PointsTo<T>)
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_init(),
        pt.value() == *old(*mut_ref),
        *final(*mut_ref) == *old(*mut_ref),
;

pub axiom fn mut_ref_to_shr_points_to_slice<'a, T>(tracked mut_ref: &'a &'a mut [T]) -> (tracked pt:
    &'a PointsTo<[T]>)
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_init(),
        pt.value() == (*old(*mut_ref))@,
        &*final(*mut_ref) == &*old(*mut_ref),
;

pub axiom fn mut_ref_to_shr_points_to_str<'a>(tracked mut_ref: &'a &'a mut str) -> (tracked pt:
    &'a PointsTo<str>)
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_init(),
        &pt.value() == &(*old(*mut_ref)),
        &*final(*mut_ref) == &*old(*mut_ref),
;

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

// Conceptually, turning a mut ref into a ptr is just splitting it into exec and tracked components.
// Ideally, we wouldn't need a dedicated function for doing both of these things; we would just
// model the exec operation turning a mut ref into a pointer, and then getting the tracked mut ref
// by mode coercion.
//
// However, the actual operation still requires a (nondeterministic) retag, so we need one function
// that produces both the raw pointer and the permission and ties the fresh pointer values together.
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

/// Convert a mutable reference into a raw pointer and accompanying `PointsTo` permission.
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

/// Convert a mutable reference into a raw pointer and accompanying `PointsTo` permission.
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

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::raw_ptr::spec_ptr_addr")]
#[verifier::inline]
pub open spec fn spec_ptr_addr<T: Sized>(ptr: *mut T) -> usize {
    spec_cast_ptr_to_usize(ptr)
}

} // verus!
