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
use super::points_to::*;
use super::points_to_permissions::*;

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
//////////////////////////////////////
/// The identifier of the `Allocator` instance used to allocate memory.
pub type AllocId = int;

/// An allocation has a start address, length, and alignment. 
/// Since the `Allocator` trait permits allocations that are larger than the originally-requested size,
/// we also keep track of this. 
/// Similarly, we track an `Allocator` instance identifier to ensure that allocations
/// are deallocated with the same instance used to allocate them,
/// as per the `Allocator::deallocate` spec.
#[verifier::external_body]
pub ghost struct ProvenanceData {}

impl ProvenanceData {
    /// The starting address of the pointer's allocation.
    pub uninterp spec fn start_addr(&self) -> usize;

    /// The length of the pointer's allocation in bytes.
    pub uninterp spec fn alloc_len(&self) -> nat;

    /// The alignment of the pointer's allocation. Must be a power of 2 bounded by `isize::MAX + 1`.
    pub uninterp spec fn alignment(&self) -> nat;

    /// The originally requested allocation size.
    pub uninterp spec fn orig_size(&self) -> nat;

    /// The ID of the `Allocator` instance used to allocate this memory.
    pub uninterp spec fn alloc_id(&self) -> AllocId;
}

/// Provenance
///
/// A full model of provenance is given by formalisms such as "Stacked Borrows"
/// or "Tree Borrows."
///
/// None of these models are finalized, nor has Rust committed to them.
/// Rust's recent [RFC on provenance](https://rust-lang.github.io/rfcs/3559-rust-has-provenance.html)
/// simply details that there *is* some concept of provenance. 
/// MiniRust currently declares a pointer has an `Option<Provenance>`
/// 
/// Likewise, our model here defines `Provenance` as an `Option<ProvenanceData>`,
/// which is `Some` if there is an actual allocation, and `None` otherwise.
/// If it is `Some`, it has all of the elements defined in `ProvenanceData`,
/// and the properties in `provenace_properties` will hold. 
/// 
/// This is axiomatized at the Verus level and proven to be upheld by trusted specs and axioms
/// (e.g., they are guaranteed by the allocate spec and upheld by various transformations).
///
/// More reading for reference:
/// * [https://doc.rust-lang.org/std/ptr/](https://doc.rust-lang.org/std/ptr/)
/// * [https://github.com/minirust/minirust/tree/master](https://github.com/minirust/minirust/tree/master)
pub type Provenance = Option<ProvenanceData>;

/// Defines properties of an allocation:
/// - Allocations do not "wrap around" the address space.
///   From: <https://doc.rust-lang.org/std/ptr/index.html#allocation>:
///   For any allocation with `base` address and size `size`, it is guaranteed that
///   `base + size <= usize::MAX` and `size <= isize::MAX`.
/// - `Alignment` invariants hold of `p.alignment()` (since here we have a `nat`).
/// - The start address of an allocation should be aligned to the allocation's alignment,
///    as per the postcondition of `Allocator::allocate`.
/// - Allocations should always start with a non-null address, even zero-sized allocations.
///   `Allocator::allocate` returns a `NonNull` pointer, and documentation here
///   (<https://doc.rust-lang.org/1.88.0/core/alloc/trait.Allocator.html>)
///   implies that returning a null pointer should not happen.
///   Additionally, MiniRust's allocate cannot return a null address.
///   <https://github.com/minirust/minirust/blob/master/spec/mem/basic.md>
/// - The actual size of the allocation is at least as big as the originally requested size
///   (from the documentation for the `Allocator` trait).
pub broadcast axiom fn provenance_properties(p: ProvenanceData)
    ensures
        #![trigger p.start_addr()]
        #![trigger p.alloc_len()]
        #![trigger p.alignment()]
        #![trigger p.orig_size()]
        p.start_addr() + p.alloc_len() <= usize::MAX,
        p.alloc_len() <= isize::MAX,
        exists|i: nat|
        pow(2, i) == p.alignment() as int && i < isize::BITS && 0 < p.alignment() <= isize::MAX
            + 1,
        p.start_addr() as nat % p.alignment() == 0,
        p.start_addr() != 0,
        p.orig_size() <= p.alloc_len(),
;

/// Specifies that the pointer's address is within the bounds of its provenance.
pub open spec fn ptr_addr_in_bounds<T: ?Sized>(ptr: *mut T) -> bool {
    ptr@.provenance.is_some() ==> {
        &&& ptr@.addr as int >= ptr@.provenance.unwrap().start_addr()
        &&& ptr@.addr <= ptr@.provenance.unwrap().start_addr() + ptr@.provenance.unwrap().alloc_len()
    }
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

#[cfg(verus_keep_ghost)]
impl<T: core::marker::PointeeSized> View for *const T {
    type V = PtrData<T>;

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        (*self as *mut T).view()
    }
}

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

/////////////////////////////////////////////////////////////
// Inverse functions: Pointers are equivalent to their model
/////////////////////////////////////////////////////////////
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

/// Implies that `a@ == b@ ==> a == b` for `Sized` types.
pub broadcast proof fn ptrs_mut_eq_sized<T>(a: *mut T)
    ensures
        view_reverse_for_eq_sized::<T>((#[trigger] a@).addr, a@.provenance) == a,
{
    assert(a@.metadata == ());
    ptrs_mut_eq(a);
}

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
// TODO: ask Travis if this function is necessary - what purpose does it serve? We also have spec_cast_ptr_to_usize and spec_addr
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

// /// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
// /// The memory pointed to by `ptr` must be initialized.
// TODO: add back in
// #[inline(always)]
// #[verifier::external_body]
// pub const fn ptr_ref_slice<T>(ptr: *const [T], Tracked(perm): Tracked<&PointsTo<[T]>>) -> (v: &[T])
//     requires
//         perm.ptr() == ptr,
//         perm.is_valid(),
//     ensures
//         v@ == perm.value(),
//     opens_invariants none
//     no_unwind
// {
//     unsafe { &*ptr }
// }

/// Equivalent to `&mut *X`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_mut_ref<T>(ptr: *mut T, Tracked(perm): Tracked<&mut PointsTo<T>>) -> (v: &mut T)
    requires
        old(perm).ptr() == ptr,
        old(perm).is_valid(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_valid(),
        old(perm).value() == *v,
        final(perm).value() == *final(v),
    opens_invariants none
    no_unwind
{
    unsafe { &mut *ptr }
}

// /// Equivalent to `&mut *X`, passing in a permission `perm` to ensure safety.
// /// The memory pointed to by `ptr` must be initialized.
// TODO: move to rustlib
// #[inline(always)]
// #[verifier::external_body]
// pub const fn ptr_mut_ref_slice<T>(ptr: *mut [T], Tracked(perm): Tracked<&mut PointsTo<[T]>>) -> (v:
//     &mut [T])
//     requires
//         old(perm).ptr() == ptr,
//         old(perm).is_valid(),
//     ensures
//         final(perm).ptr() == ptr,
//         final(perm).is_valid(),
//         old(perm).value() == v@,
//         final(perm).value() == final(v)@,
//     opens_invariants none
//     no_unwind
// {
//     unsafe { &mut *ptr }
// }

// /// Equivalent to `&mut *X`, passing in a permission `perm` to ensure safety.
// /// The memory pointed to by `ptr` must be initialized.
// TODO: add back in
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
// TODO: ask Travis if this has to be axiomatized
// TODO: define the equivalent shared ref version, using shadow data?
pub axiom fn mut_ref_slice_len<T>(tracked b: &&mut [T])
    ensures
        mut_ref_ptr(*b)@.metadata == old(*b)@.len(),
;

////////////////////////////////////////
// Mutable reference conversions
// TODO: ask Travis - do these have to be axiomatized?
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
        *final(*mut_ref) == *old(*mut_ref),
;

// TODO: move to rustlib
// /// Convert from a shared reference to a `&'a mut str` to a `&'a PointsTo<str>`.
// pub axiom fn mut_ref_to_shr_points_to_slice<'a, T>(tracked mut_ref: &'a &'a mut [T]) -> (tracked pt:
//     &'a PointsTo<[T]>)
//     ensures
//         pt.ptr() == mut_ref_ptr(*mut_ref),
//         pt.is_valid(),
//         pt.value() == (*old(*mut_ref))@,
//         &*final(*mut_ref) == &*old(*mut_ref),
// ;

// /// Convert from a shared reference to a `&'a mut [T]` to a `&'a PointsTo<[T]>`.
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
// TODO: ask Travis if this function is done
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

pub broadcast group group_raw_ptr_axioms {
    axiom_ptr_mut_from_data,
    ptrs_mut_eq,
    ptrs_mut_eq_sized,
    provenance_properties,
}

} // verus!
