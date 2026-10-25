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
use super::super::arithmetic::power::pow;
use super::super::prelude::*;

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

/// The `AllocId` of allocations made by the global allocator.
pub uninterp spec fn global_alloc_id() -> AllocId;

/// An allocation has a start address, length, and alignment.
/// Since the `Allocator` trait permits allocations that are larger than the originally-requested size,
/// we also keep track of this.
/// Similarly, we track an `Allocator` instance identifier to ensure that allocations
/// are deallocated with the same instance used to allocate them,
/// as per the `Allocator::deallocate` spec.
#[verifier::external_body]
pub ghost struct ProvenanceData {}

impl ProvenanceData {
    // Add tag fn to opaque Tag type and provenance equality fn
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
        &&& ptr@.addr <= ptr@.provenance.unwrap().start_addr()
            + ptr@.provenance.unwrap().alloc_len()
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

pub broadcast group group_raw_ptr_axioms {
    axiom_ptr_mut_from_data,
    ptrs_mut_eq,
    ptrs_mut_eq_sized,
    provenance_properties,
}

} // verus!
