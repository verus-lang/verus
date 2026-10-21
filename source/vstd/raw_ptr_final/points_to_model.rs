#![allow(unused_imports)]

use super::ptr_model;
use super::ptr_model::*;
use super::super::group_vstd_default;
use super::super::layout::{self, *};
use super::super::prelude::*;
#[cfg(verus_keep_ghost)]
use super::super::type_representation::*;

pub mod points_to_ops;

verus! {

broadcast use {
    ptr_model::group_raw_ptr_axioms,
    layout::group_layout_axioms,
    super::super::seq::group_seq_axioms,
};

// A private seal trait to prevent `PTPhys` from being implemented outside of vstd.
pub(crate) trait PTPhysSealed {}

/// Defines the physical memory region that a `PointsTo` permission covers,
/// by specifying the pointer to memory and the size of the pointed-to region.
#[allow(private_bounds)]
pub trait PTPhys: Sized + PTPhysSealed {
    type A: ?Sized;

    /// The pointer that this permission is associated with.
    spec fn ptr(self) -> *mut Self::A;

    /// The size, in bytes, of the memory region tracked by a permission
    /// whose pointer has the given metadata.
    /// A permission `p` tracks `Self::size(p.ptr()@.metadata)` bytes.
    spec fn size(self) -> nat;

    /// Define basic well-formedness conditions on the permission's pointer
    /// which are necessary to ensure all of the `PTProperties` requirements.
    /// `PTTypedValue::wf` builds on this to add conditions on the bytes and typed value,
    /// as well as adding pointer conditions specific to a given permission type.
    spec fn wf_basic(self) -> bool;
}

/// Restricts `PTPhys` to permissions whose pointed-to size is determined by the type alone.
/// This lets code which is generic over some `PTPhys`
/// rely on all instances of that type reporting the same `size()`
/// (for example, `SeqPointsTo` requires that every permission in the sequence must track the same size of memory).
pub trait FixedSize: PTPhys {
    /// The (constant) size of the memory region that this permission tracks,
    /// which is the same for every `PointsTo` permission satisfying this trait bound.
    spec fn const_size() -> nat;

    /// Ensures that the `PTPhys` size is always the same as the constant size defined here.
    proof fn size_eq_const_size(tracked &self)
        ensures
            self.size() == Self::const_size(),
    ;
}

/// Defines properties which should hold of any `PointsTo` permission.
pub trait PTProperties: PTPhys {
    /// Guarantee that the pointer is non-null.
    ///
    /// See <https://doc.rust-lang.org/std/ptr/#safety>
    proof fn is_nonnull(tracked &self)
        requires
            self.wf_basic(),
        ensures
            self.ptr()@.addr != 0,
    ;

    /// The memory associated with a pointer should always be within bounds of its spatial provenance.
    proof fn ptr_bounds(tracked &self)
        requires
            self.ptr()@.provenance.is_some(),
            self.wf_basic(),
        ensures
            self.ptr()@.addr as int >= self.ptr()@.provenance.unwrap().start_addr(),
            self.ptr()@.addr + self.size() <= self.ptr()@.provenance.unwrap().start_addr()
                + self.ptr()@.provenance.unwrap().alloc_len(),
    ;

    /// If the size of the pointed-to region is nonzero,
    /// then the pointer's provenance is non-null.
    proof fn provenance_not_none(tracked &self)
        requires
            self.size() != 0,
            self.wf_basic(),
        ensures
            self.ptr()@.provenance != Provenance::None,
    ;

    /// Guarantees that the memory ranges associated with two distinct, non-ZST permissions will not overlap,
    /// since you cannot have two permissions to the same memory.
    /// (`self` is an &mut reference to enforce distinctness,
    /// so you cannot pass the same PointsTo as both arguments.)
    /// Since both memory regions are non-zero-sized, this implies the pointers have distinct addresses.
    ///
    /// Note: If either memory region is zero-sized, we get disjointness "for free" without having to call this axiom,
    /// since the empty memory range corresponding to a ZST cannot possibly intersect with any other memory.
    /// However, note that if one type is a ZST and the other is a non-ZST,
    /// the disjointness definition as stated here does not hold,
    /// since the ZST pointer could be in the middle of the non-ZST's range.
    ///
    /// Both permissions must be `wf_basic`, since that is what ties `size` to the memory actually held.
    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    )
        requires
            self.size() != 0,
            other.size() != 0,
            self.wf_basic(),
            other.wf_basic(),
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + final(self).size() <= other.ptr() as int
                || other.ptr() as int + other.size() <= final(self).ptr() as int,
    ;

    /// Specifies necessary conditions for ensuring that `new` and `old` are permissions
    /// to the same region of memory and that `wf_basic` carries over from `old`:
    /// `new` must keep `old`'s pointers and length.
    /// Each implementation defines what this means for its permission type.
    spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool;

    /// If `old` satisfies `wf_basic` and `new` satisfies `ptrs_len_same` with respect to it,
    /// then `new` satisfies `wf_basic`.
    proof fn stays_wf_basic(old: Self, new: Self)
        requires
            old.wf_basic(),
            Self::ptrs_len_same_valid(old, new),
        ensures
            new.wf_basic(),
    ;
}

/// Permission to access a byte of memory.
#[verifier::external_body]
pub tracked struct PointsToByte {
    no_copy: NoCopy,
}

impl PTPhysSealed for PointsToByte {}

impl PTPhys for PointsToByte {
    type A = u8;

    /// This permission points to a single byte of memory.
    uninterp spec fn ptr(self) -> *mut u8;

    /// This permission tracks a single byte of memory.
    open spec fn size(self) -> nat {
        size_of::<u8>()
    }

    /// A `PointsToByte` is always well-formed.
    open spec fn wf_basic(self) -> bool {
        true
    }
}

impl PTProperties for PointsToByte {
    /// Guarantee that the `PointsToByte` points to a non-null address.
    ///
    /// See <https://doc.rust-lang.org/std/ptr/#safety>.
    axiom fn is_nonnull(tracked &self);

    /// The memory associated with a pointer should always be within bounds of its spatial provenance.
    axiom fn ptr_bounds(tracked &self);

    /// Since `u8` is not a ZST, the pointer's provenance is non-null.
    /// <https://doc.rust-lang.org/std/ptr/index.html#provenance>
    axiom fn provenance_not_none(tracked &self);

    /// Guarantees that the memory ranges associated with two distinct, non-ZST permissions will not overlap,
    /// since you cannot have two permissions to the same memory.
    /// (`self` is an &mut reference to enforce distinctness,
    /// so you cannot pass the same PointsTo as both arguments.)
    /// Since `u8` is not a ZST, this implies the pointers have distinct addresses.
    axiom fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    );

    /// If the pointer stays the same, `old` and `new` are permissions to the same memory.
    open spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool {
        new.ptr() == old.ptr()
    }

    /// Trivial, since a `PointsToByte` is always well-formed.
    proof fn stays_wf_basic(old: Self, new: Self) {
    }
}

impl FixedSize for PointsToByte {
    /// A `PointsToByte` always tracks a single byte of memory.
    open spec fn const_size() -> nat {
        size_of::<u8>()
    }

    proof fn size_eq_const_size(tracked &self) {
    }
}

impl PointsToByte {
    /// The byte that this permission tracks.
    pub uninterp spec fn byte(self) -> AbstractByte;

    /// Specializes `is_disjoint` to the case when the other permission is a `PointsToByte`.
    pub proof fn is_disjoint_byte(tracked &mut self, tracked other: &Self)
        requires
            self.wf_basic(),
            other.wf_basic(),
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + size_of::<u8>() <= other.ptr() as int || other.ptr() as int
                + size_of::<u8>() <= final(self).ptr() as int,
    {
        broadcast use group_vstd_default;

        self.is_disjoint(other);
    }
}

/// The interface for a `PointsToByte` permission,
/// which represents permission to access a single byte in memory.
/// We track the pointer to that memory as well as
/// the abstract byte corresponding to Rust's abstract machine.
#[cfg(verus_keep_ghost)]
pub ghost struct PointsToByteData {
    pub ptr: *mut u8,
    pub byte: AbstractByte,
}

#[cfg(verus_keep_ghost)]
impl View for PointsToByte {
    type V = PointsToByteData;

    open spec fn view(&self) -> Self::V {
        PointsToByteData { ptr: self.ptr(), byte: self.byte() }
    }
}

/// Permission to access a contiguous sequence of values of type `T` in memory.
/// Internally represented as a sequence of permissions `P`,
/// along with a `*mut [T]` pointer to the whole region.
// We expect the associated type `A` from `PTProperties` to be the same as `T`,
// but `A = T` is bound on the impls
// so that recursive types like `struct Tree { children: Vec<Tree> }` are allowed.
pub tracked struct SeqPointsTo<T: ?Sized, P: PTProperties + FixedSize> {
    seq_pt: Seq<P>,
    ptr: Ghost<*mut T>,
}

impl<T: ?Sized, P: PTProperties + FixedSize> PTPhysSealed for SeqPointsTo<T, P> {}

impl<T: ?Sized, P: PTProperties + FixedSize> PTPhys for SeqPointsTo<T, P> {
    type A = T;

    /// The pointer to the whole region; its metadata is the number of elements.
    closed spec fn ptr(self) -> *mut T {
        self.ptr@
    }

    /// The size of the pointed-to region is given by the length of the sequence (the pointer's metadata)
    /// times the size of the permission type in the sequence.
    ///
    /// Note that since this impl block restricts `P` to permissions satisfying `PTProperties`
    /// with the associated type set to `T` (which is implicitly `Sized`),
    /// `P` is a permission whose pointer has `()` metadata.
    open spec fn size(self) -> nat {
        self.seq_pt().len() * P::const_size()
    }

    open spec fn wf_basic(self) -> bool {
        // Defining the provenance and address for the individual permissions
        &&& forall|i|
            #![trigger self[i].ptr()@.provenance]
            #![trigger self[i].ptr()@.addr]
            #![trigger self[i].wf_basic()]
            0 <= i < self.len() ==> {
                &&& self[i].ptr()@.provenance == self.ptr()@.provenance
                &&& self[i].ptr()@.addr == self.ptr()@.addr + i * P::const_size()
                &&& self[i].wf_basic()
            }
        // The ptr is non-null
        &&& self.ptr()@.addr != 0
        // If ptr's provenance is Some, the address is in bounds of the provenance
        &&& self.ptr()@.provenance.is_some() ==> {
            &&& self.ptr()@.provenance.unwrap().start_addr() <= self.ptr()@.addr
            &&& self.ptr()@.addr <= self.ptr()@.provenance.unwrap().start_addr()
                + self.ptr()@.provenance.unwrap().alloc_len()
        }
    }
}

impl<T: ?Sized, P: PTProperties + FixedSize> SeqPointsTo<T, P> {
    /// The sequence of permissions that the `SeqPointsTo` contains.
    pub closed spec fn seq_pt(self) -> Seq<P> {
        self.seq_pt
    }

    /// The length of the sequence of `P` permissions.
    #[verifier::inline]
    pub open spec fn len(self) -> nat {
        self.seq_pt().len()
    }

    /// `[]` operator, synonymous with `index`.
    #[verifier::inline]
    pub open spec fn spec_index(self, index: int) -> P
        recommends
            0 <= index < self.len(),
    {
        self.seq_pt()[index]
    }
}

/// Permission to access an (untyped) contiguous sequence of bytes in memory.
/// Internally represented as a sequence of `PointsToByte` permissions,
/// along with a `*mut [u8]` pointer to the region of bytes.
pub type PointsToUntyped = SeqPointsTo<[u8], PointsToByte>;

/// The interface for a `PointsToUntyped` permission,
/// which represents permission to access an (untyped) contiguous sequence of bytes in memory.
/// We track the pointer to that memory as well as
/// the abstract bytes corresponding to Rust's abstract machine.
#[cfg(verus_keep_ghost)]
pub ghost struct PointsToUntypedData {
    pub ptr: *mut [u8],
    pub bytes: Seq<AbstractByte>,
}

#[cfg(verus_keep_ghost)]
impl View for PointsToUntyped {
    type V = PointsToUntypedData;

    open spec fn view(&self) -> Self::V {
        PointsToUntypedData { ptr: self.ptr(), bytes: self.bytes() }
    }
}

impl PointsToUntyped {
    /// The contiguous sequence of bytes that this permission tracks.
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        self.seq_pt().map(|i: int, pt_byte: PointsToByte| pt_byte.byte())
    }

    /// The well-formed-ness properties which must hold of every `SeqPointsTo` (`wf_basic`),
    /// which include that the `*mut [u8]` pointer's metadata matches the number of `PointsToByte` permissions.
    pub open spec fn wf(self) -> bool {
        self.wf_basic() && self.ptr()@.metadata == self.len()
    }

    /// Joins shared borrows of two `PointsToUntyped` permissions into a shared borrow of a
    /// single `PointsToUntyped`, under the same conditions as `join`.
    ///
    /// This is the shared-borrow analogue of `join`. It's an axiom because the joined permission
    /// isn't stored anywhere that could be borrowed.
    pub axiom fn join_ref<'a>(tracked &'a self, tracked other: &'a Self) -> (tracked joined: &'a Self)
        requires
            self.wf(),
            other.wf(),
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len(),
        ensures
            joined.seq_pt() == self.seq_pt() + other.seq_pt(),
            joined.bytes() == self.bytes() + other.bytes(),
            joined.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() + other.len()) as usize,
                },
            ),
            joined.wf(),
    ;

    /// Joins mutable borrows of two `PointsToUntyped` permissions into a mutable borrow of a
    /// single `PointsToUntyped`, under the same conditions as `join`.
    ///
    /// If the joined permission keeps its pointers and length, then so do `self` and `other`, and
    /// their final byte permissions concatenate to the joined permission's final ones.
    ///
    /// This is the mutable-borrow analogue of `join`. It's an axiom because the joined permission
    /// isn't stored anywhere that could be borrowed.
    pub axiom fn join_mut<'a>(tracked &'a mut self, tracked other: &'a mut Self) -> (tracked joined:
        &'a mut Self)
        requires
            self.wf(),
            other.wf(),
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len(),
        ensures
            joined.seq_pt() == old(self).seq_pt() + old(other).seq_pt(),
            joined.bytes() == old(self).bytes() + old(other).bytes(),
            joined.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: old(self).ptr()@.addr,
                    provenance: old(self).ptr()@.provenance,
                    metadata: (old(self).len() + old(other).len()) as usize,
                },
            ),
            joined.wf(),
            Self::ptrs_len_same_valid(*joined, *final(joined)) ==> {
                &&& final(self).ptr() == old(self).ptr()
                &&& final(other).ptr() == old(other).ptr()
                &&& final(self).wf()
                &&& final(other).wf()
                &&& final(joined).seq_pt() == final(self).seq_pt() + final(other).seq_pt()
                &&& final(joined).bytes() == final(self).bytes() + final(other).bytes()
            },
    ;
}

/// Represents (typed) contents of memory.
// Don't use std Option here in order to avoid circular dependency issues
// with verifying the standard library.
// (Also, using our own enum here lets us have more meaningful
// variant names like Empty/Valid.)
#[verifier::accept_recursive_types(T)]
pub tracked enum TypedValue<T: ?Sized> {
    /// Represents uninitialized memory.
    Empty,
    /// Represents initialized memory with the given value of type `T`.
    Valid(Tracked<T>),
}

impl<T: ?Sized> TypedValue<T> {
    /// Returns `true` if it is a [`TypedValue::Valid`] value.
    #[verifier::inline]
    pub open spec fn is_valid(&self) -> bool {
        self is Valid
    }

    /// Returns `true` if it is a [`TypedValue::Empty`] value.
    #[verifier::inline]
    pub open spec fn is_empty(&self) -> bool {
        self is Empty
    }
}

impl<T> TypedValue<T> {
    /// If it is a [`TypedValue::Valid`] value, returns the value.
    /// Otherwise, the return value is meaningless.
    #[verifier::inline]
    pub open spec fn value(&self) -> T
        recommends
            self is Valid,
    {
        *self->0
    }

    /// Copies a `TypedValue<T>` out of a shared reference, given that `T` is `Copy`.
    pub proof fn tracked_copy(tracked &self) -> (tracked out: TypedValue<T>) where T: Copy
        ensures
            out == *self,
    {
        match self {
            TypedValue::Valid(b) => TypedValue::Valid(Tracked(**b)),
            TypedValue::Empty => TypedValue::Empty,
        }
    }
}

impl<T> TypedValue<[T]> {
    /// If it is a [`TypedValue::Valid`] value, returns the value.
    /// Otherwise, the return value is meaningless.
    #[verifier::inline]
    pub open spec fn value(&self) -> &[T]
        recommends
            self is Valid,
    {
        &*self->0
    }
}

/// Permission to access memory which may decode to a valid value of type `T`;
/// this memory is not guaranteed to be aligned to `T`.
/// Internally represented as a possibly-valid value of type `T`,
/// along with a `PointsToUntyped` permission to the underlying bytes,
/// and the (ghost) metadata of the `*mut T` pointer.
pub tracked struct PointsToUnaligned<T: ?Sized> {
    val: TypedValue<T>,
    pt_untyped: PointsToUntyped,
    metadata: Ghost<Metadata<T>>,
}

/// The interface for a `PointsToUnaligned` or `PointsTo` permission,
/// which represents permission to access memory
/// whose bytes may decode to a valid value of type `T`.
/// We track the pointer to that memory,
/// the (possibly-valid) typed value, and its abstract bytes.
///
/// If `value` is `Valid(v)`, this signifies that `ptr` points to initialized memory,
/// and `v` is consistent with the bytes `ptr` points to.
/// We also have all the ghost state associated with type `T`.
///
/// If `value` is `Empty`, then we have no knowledge about what's in memory,
/// and we assume `ptr` points to uninitialized memory.
/// (To be pedantic, the bytes might be initialized in Rust's abstract machine,
///  but we don't know, so we have to pretend they're uninitialized.)
#[cfg(verus_keep_ghost)]
pub ghost struct PointsToData<T: ?Sized> {
    pub ptr: *mut T,
    pub value: TypedValue<T>,
    pub bytes: Seq<AbstractByte>,
}

#[cfg(verus_keep_ghost)]
impl<T> View for PointsToUnaligned<T> {
    type V = PointsToData<T>;

    open spec fn view(&self) -> Self::V {
        PointsToData { ptr: self.ptr(), value: self.typed_value(), bytes: self.bytes() }
    }
}

impl<T: ?Sized> PointsToUnaligned<T> {
    /// The (possibly-valid) typed value that this permission tracks.
    pub closed spec fn typed_value(self) -> TypedValue<T> {
        self.val
    }

    /// The underlying `PointsToUntyped` permission to the pointed-to bytes.
    pub closed spec fn pt_untyped(self) -> PointsToUntyped {
        self.pt_untyped
    }

    /// The metadata of the `*mut T` pointer this permission is for.
    pub closed spec fn metadata(self) -> Metadata<T> {
        self.metadata@
    }

    /// The contiguous sequence of bytes that this permission tracks.
    #[verifier::inline]
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        self.pt_untyped().bytes()
    }

    /// Returns `true` if the permission's associated memory is valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_valid(&self) -> bool {
        self.typed_value().is_valid()
    }

    /// Returns `true` if the permission's associated memory is not valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_empty(&self) -> bool {
        self.typed_value().is_empty()
    }

    /// Returns a tracked reference to the underlying `PointsToUntyped` permission.
    ///
    /// This has no `wf()` requires/ensures,
    /// which gives flexibility for getting the underlying `PointsToUntyped`
    /// when the permission is not well-formed.
    /// However, the `wf()` conditions on `self` should imply that `pt_untyped` is `wf()`.
    // This is implemented by making `PTTypedValue::wf` on `self` include `wf_basic_unaligned`,
    // which includes `self.pt_untyped().wf()`.
    pub proof fn tracked_pt_untyped(tracked &self) -> tracked &PointsToUntyped
        returns
            self.pt_untyped(),
    {
        &self.pt_untyped
    }
}

impl<T: ?Sized> PTPhysSealed for PointsToUnaligned<T> {}

impl<T> PTPhys for PointsToUnaligned<T> {
    type A = T;

    /// Builds the `*mut T` from the underlying untyped pointer's address and provenance
    /// and the stored metadata.
    closed spec fn ptr(self) -> *mut T {
        self.pt_untyped().ptr() as *mut T
    }

    /// The size of the pointed-to region is the size of `T`.
    open spec fn size(self) -> nat {
        size_of::<T>()
    }

    /// A `PointsToUnaligned` is well-formed at the pointer level
    /// if its memory region is `size_of::<T>()` bytes,
    /// and the underlying `PointsToUntyped` is well-formed.
    open spec fn wf_basic(self) -> bool {
        &&& self.bytes().len() == size_of::<T>()
        &&& self.is_valid() ==> #[trigger] abs_decode::<T>(self.bytes(), &self.value())
        &&& self.pt_untyped().wf()
        &&& self.metadata() == self.ptr()@.metadata
    }
}

impl<T> FixedSize for PointsToUnaligned<T> {
    /// A `PointsToUnaligned<T>` always tracks `size_of::<T>()` bytes of memory.
    open spec fn const_size() -> nat {
        size_of::<T>()
    }

    proof fn size_eq_const_size(tracked &self) {
    }
}

impl<T> PointsToUnaligned<T> {
    /// If the permission's associated memory is valid,
    /// returns the value that the pointer points to.
    /// Otherwise, the result is meaningless.
    #[verifier::inline]
    pub open spec fn value(&self) -> T
        recommends
            self.is_valid(),
    {
        self.typed_value().value()
    }

    /// Well-formedness is defined in the `PTProperties` trait function `wf_basic`.
    pub open spec fn wf(&self) -> bool {
        self.wf_basic()
    }
}

#[cfg(verus_keep_ghost)]
impl<T> View for PointsToUnaligned<[T]> {
    type V = PointsToData<[T]>;

    open spec fn view(&self) -> Self::V {
        PointsToData { ptr: self.ptr(), value: self.typed_value(), bytes: self.bytes() }
    }
}

impl<T> PTPhys for PointsToUnaligned<[T]> {
    type A = [T];

    /// Builds the `*mut [T]` from the underlying untyped pointer's address and provenance
    /// and the stored metadata.
    closed spec fn ptr(self) -> *mut [T] {
        ptr_mut_from_data::<[T]>(
            PtrData {
                addr: self.pt_untyped().ptr()@.addr,
                provenance: self.pt_untyped().ptr()@.provenance,
                metadata: self.metadata(),
            },
        )
    }

    /// The size of the pointed-to region is the number of elements times the size of `T`.
    open spec fn size(self) -> nat {
        self.metadata() as nat * size_of::<T>()
    }

    /// A `PointsToUnaligned<[T]>` is well-formed at the pointer level
    /// if its memory region is `Self::size(self.ptr()@.metadata)` bytes,
    /// and the underlying `PointsToUntyped` is well-formed.
    open spec fn wf_basic(self) -> bool {
        &&& self.bytes().len() == self.size()
        &&& self.is_valid() ==> {
            &&& self.typed_value().value()@.len() == self.metadata()
            &&& abs_decode::<[T]>(self.bytes(), self.typed_value().value())
        }
        &&& self.pt_untyped().wf()
        &&& self.metadata() == self.ptr()@.metadata
    }
}

impl<T> PointsToUnaligned<[T]> {
    /// Well-formedness is defined in the `PTProperties` trait function `wf_basic`.
    pub open spec fn wf(&self) -> bool {
        self.wf_basic()
    }
}

/**
Permission to access possibly-initialized, _typed_ memory.

The associated pointer ([`points_to.ptr()`](PTPhys::ptr)) is always a valid pointer for constructing
a reference to the underlying data. That means it's always aligned to its type
([`is_aligned`](PointsTo::is_aligned)) and is non-null ([`is_nonnull`](PTProperties::is_nonnull)).

### Notes

The invariants on a `PointsTo` are a little more restrictive than is necessary for all
Rust operations you might want to do. For example:

1. With a null pointer to a ZST, Rust lets you read and write (though not take a reference).

```
#[derive(Copy, Clone)]
#[repr(align(64))]
struct X { }

fn zst_test() {
    let x_ptr: *mut X = std::ptr::null_mut();

    let x = unsafe { *x_ptr };  // allowed

    let x = X { };
    unsafe { *x_ptr = x; }      // allowed

    let j = unsafe { &*x_ptr }; // not allowed because ptr is null
}
```

2. The [`std::ptr::read_unaligned`] and [`std::ptr::write_unaligned`] don't require the pointer
   to be aligned.

Currently, the first use-case isn't supported because `PointsTo` enforces non-nullness.
For the second, use `PointsToUnaligned`, which doesn't enforce alignment.
*/
pub tracked struct PointsTo<T: ?Sized> {
    pt_unaligned: PointsToUnaligned<T>,
}

#[cfg(verus_keep_ghost)]
impl<T> View for PointsTo<T> {
    type V = PointsToData<T>;

    open spec fn view(&self) -> Self::V {
        PointsToData { ptr: self.ptr(), value: self.typed_value(), bytes: self.bytes() }
    }
}

impl<T: ?Sized> PointsTo<T> {
    /// The underlying `PointsToUnaligned` permission to the pointed-to memory.
    pub closed spec fn pt_unaligned(self) -> PointsToUnaligned<T> {
        self.pt_unaligned
    }

    /// The (possibly-valid) typed value that this permission tracks.
    pub open spec fn typed_value(self) -> TypedValue<T> {
        self.pt_unaligned().typed_value()
    }

    /// The metadata of the `*mut T` pointer this permission is for.
    pub open spec fn metadata(self) -> Metadata<T> {
        self.pt_unaligned().metadata()
    }

    /// The contiguous sequence of bytes that this permission tracks.
    #[verifier::inline]
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        self.pt_unaligned().bytes()
    }

    /// Returns `true` if the permission's associated memory is valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_valid(&self) -> bool {
        self.typed_value().is_valid()
    }

    /// Returns `true` if the permission's associated memory is not valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_empty(&self) -> bool {
        self.typed_value().is_empty()
    }

    /// Returns a tracked reference to the underlying `PointsToUnaligned` permission.
    ///
    /// This has no `wf()` requires/ensures,
    /// which gives flexibility for getting the underlying `PointsToUnaligned`
    /// when the permission is not well-formed.
    /// However, the `wf()` conditions on `self` should imply that `pt_unaligned` is `wf()`.
    // This is implemented by making `PTTypedValue::wf` on `self` include `self.pt_unaligned().wf()`.
    pub proof fn tracked_pt_unaligned(tracked &self) -> tracked &PointsToUnaligned<T>
        returns
            self.pt_unaligned(),
    {
        &self.pt_unaligned
    }
}

impl<T: ?Sized> PTPhysSealed for PointsTo<T> {}

impl<T> PTPhys for PointsTo<T> {
    type A = T;

    /// Delegates to the underlying `PointsToUnaligned`'s pointer.
    open spec fn ptr(self) -> *mut T {
        self.pt_unaligned().ptr()
    }

    /// Delegates to the underlying `PointsToUnaligned`'s size.
    open spec fn size(self) -> nat {
        size_of::<T>()
    }

    /// Delegates to the underlying `PointsToUnaligned`'s `wf_basic`.
    /// This does not capture all well-formedness conditions:
    /// pointer alignment is specified in `PTTypedValue::wf`.
    open spec fn wf_basic(self) -> bool {
        &&& self.ptr()@.addr as nat % align_of::<T>() == 0
        &&& self.pt_unaligned().wf()
    }
}

impl<T> FixedSize for PointsTo<T> {
    /// A `PointsTo<T>` always tracks `size_of::<T>()` bytes of memory.
    open spec fn const_size() -> nat {
        size_of::<T>()
    }

    proof fn size_eq_const_size(tracked &self) {
    }
}

#[cfg(verus_keep_ghost)]
impl<T> View for PointsTo<[T]> {
    type V = PointsToData<[T]>;

    open spec fn view(&self) -> Self::V {
        PointsToData { ptr: self.ptr(), value: self.typed_value(), bytes: self.bytes() }
    }
}

impl<T> PTPhys for PointsTo<[T]> {
    type A = [T];

    /// Delegates to the underlying `PointsToUnaligned`'s pointer.
    open spec fn ptr(self) -> *mut [T] {
        self.pt_unaligned().ptr()
    }

    /// Delegates to the underlying `PointsToUnaligned`'s size.
    open spec fn size(self) -> nat {
        self.pt_unaligned().size()
    }

    /// Delegates to the underlying `PointsToUnaligned`'s `wf_basic`.
    /// This does not capture all well-formedness conditions:
    /// pointer alignment is specified in `PTTypedValue::wf`.
    open spec fn wf_basic(self) -> bool {
        &&& self.ptr()@.addr as nat % align_of::<T>() == 0
        &&& self.pt_unaligned().wf()
    }
}

impl<T> PointsTo<[T]> {
    /// Well-formedness is defined in the `PTProperties` trait function `wf_basic`.
    pub open spec fn wf(&self) -> bool {
        self.wf_basic()
    }
}

impl<T> PointsTo<T> {
    /// If the permission's associated memory is valid,
    /// returns the value that the pointer points to.
    /// Otherwise, the result is meaningless.
    #[verifier::inline]
    pub open spec fn value(&self) -> T
        recommends
            self.is_valid(),
    {
        self.typed_value().value()
    }

    /// Well-formedness is defined in the `PTProperties` trait function `wf_basic`.
    pub open spec fn wf(&self) -> bool {
        self.wf_basic()
    }

    /// This takes a mutable borrow of the `T` from a mutable borrow of a `PointsTo<T>`.
    /// The pointer of this borrow matches the permission's pointer.
    ///
    /// Writing through the reference updates both the value and the underlying bytes,
    /// so `final(self)` is well-formed with bytes that decode to the final value.
    /// This is an axiom because the bytes live in separate ghost state from the `TypedValue<T>`,
    /// so they can't be updated through a borrow of the value alone.
    pub axiom fn borrow_mut(tracked &mut self) -> (tracked val: &mut T)
        requires
            self.wf(),
            self.is_valid(),
        ensures
            *val == old(self).value(),
            mut_ref_ptr(val) == old(self).ptr(),
            final(self).is_valid(),
            final(self).ptr() == old(self).ptr(),
            final(self).value() == *final(val),
            final(self).wf(),
    ;
}

} // verus!
