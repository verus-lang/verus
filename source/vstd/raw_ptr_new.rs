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

pub broadcast group group_provenance_properties {
    prov_alignment,
    alloc_bound,
    start_addr_aligned,
    is_nonnull,
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

// #[cfg(verus_keep_ghost)]
// impl<T: core::marker::PointeeSized> View for *mut T {
//     type V = PtrData<T>;

//     uninterp spec fn view(&self) -> Self::V;
// }

// /// Compares the address and metadata of two pointers.
// ///
// /// Note that this does NOT compare provenance, which does not exist in the runtime
// /// pointer representation (i.e., it only exists in the Rust abstract machine).
// #[cfg(verus_keep_ghost)]
// pub assume_specification<T: core::marker::PointeeSized>[ <*mut T as PartialEq<*mut T>>::eq ](
//     x: &*mut T,
//     y: &*mut T,
// ) -> (res: bool)
//     ensures
//         res <==> (x@.addr == y@.addr) && (x@.metadata == y@.metadata),
// ;

// #[cfg(verus_keep_ghost)]
// impl<T: core::marker::PointeeSized> View for *const T {
//     type V = PtrData<T>;

//     #[verifier::inline]
//     open spec fn view(&self) -> Self::V {
//         (*self as *mut T).view()
//     }
// }

// /// Compares the address and metadata of two pointers.
// ///
// /// Note that this does NOT compare provenance, which does not exist in the runtime
// /// pointer representation (i.e., it only exists in the Rust abstract machine).
// #[cfg(verus_keep_ghost)]
// pub assume_specification<T: core::marker::PointeeSized>[ <*const T as PartialEq<*const T>>::eq ](
//     x: &*const T,
//     y: &*const T,
// ) -> (res: bool)
//     ensures
//         res <==> (x@.addr == y@.addr) && (x@.metadata == y@.metadata),
// ;

} // verus!
