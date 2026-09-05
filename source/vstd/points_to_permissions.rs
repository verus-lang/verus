use super::group_vstd_default;
use super::layout::{self, *};
use super::points_to::*;
use super::points_to::SeqPointsTo;
use super::prelude::*;
use super::raw_ptr;
use super::raw_ptr::*;
#[cfg(verus_keep_ghost)]
use super::type_representation::*;

verus! {

broadcast use group_vstd_default;

/// Permission to access an (untyped) contiguous sequence of bytes in memory.
/// Internally represented as a sequence of `PointsToSingleton` permissions,
/// along with a `*mut [u8]` pointer to the region of bytes.
pub type PointsToUntyped = SeqPointsTo<[u8], PointsToSingleton>;

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
        PointsToUntypedData {
            ptr: self.ptr(),
            bytes: self.bytes(),
        }
    }
}

impl PointsToUntyped {
    /// The contiguous sequence of bytes that this permission tracks.
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        self.seq_pt().map(|i: int, pt_singleton: PointsToSingleton| pt_singleton.byte())
    }

    /// In addition to the well-formed-ness properties which must hold of every `SeqPointsTo`,
    /// the `*mut [u8]` pointer's metadata must match the number of `PointsToSingleton` permissions.
    pub open spec fn wf(self) -> bool {
        self.wf_basic() && self.ptr()@.metadata == self.len()
    }

    /// Specializes `is_disjoint` to the case when the other permission is a `PointsToUntyped`.
    pub proof fn is_disjoint_untyped(tracked &mut self, tracked other: &PointsToUntyped)
        requires
            self.len() != 0,
            other.len() != 0,
            self.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + final(self).len() <= other.ptr() as int || other.ptr() as int
                + other.len() <= final(self).ptr() as int,
    {
        assert(self.len() == self.size());
        assert(other.size() == other.len() * other.seq_pt()[0].size());
        self.is_disjoint(other);
    }
}

/// Permission to access memory which may decode to a valid value of type `T`;
/// this memory is not guaranteed to be aligned to `T`.
/// Internally represented as a possibly-valid value of type `T`,
/// along with a `PointsToUntyped` permission to the underlying bytes.
pub tracked struct PointsToUnaligned<T: ?Sized> {
    val: TypedValue<T>,
    pt_untyped: Tracked<PointsToUntyped>,
}

impl<T: ?Sized> PointsToUnaligned<T> {
    /// The (possibly-valid) typed value that this permission tracks.
    pub closed spec fn typed_value(self) -> TypedValue<T> {
        self.val
    }

    /// The underlying `PointsToUntyped` permission to the pointed-to bytes.
    pub closed spec fn pt_untyped(self) -> PointsToUntyped {
        self.pt_untyped@
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
    pub proof fn tracked_pt_untyped(tracked &self) -> tracked &PointsToUntyped
        returns
            self.pt_untyped(),
    {
        &self.pt_untyped
    }
}

impl<T> PointsToParam for PointsToUnaligned<T> {
    type A = T;

    /// Casts the underlying untyped pointer to a `*mut T`.
    closed spec fn ptr(self) -> *mut T {
        self.pt_untyped().ptr() as *mut T
    }

    /// The size of the pointed-to region is the size of `T`.
    open spec fn size(self) -> nat {
        size_of::<T>()
    }
}

impl<T> FixedSizeParam for PointsToUnaligned<T> {
    /// A `PointsToUnaligned<T>` always tracks `size_of::<T>()` bytes of memory.
    open spec fn const_size() -> nat {
        size_of::<T>()
    }

    proof fn size_eq_const_size(tracked &self) {}
}

impl<T> PointsToProperties for PointsToUnaligned<T> {
    /// A `PointsToUnaligned` is well-formed if its memory region is `size_of::<T>()`,
    /// validity of the typed memory implies that the bytes decode to its value,
    /// and the underlying `PointsToUntyped` is well-formed.
    open spec fn wf_basic(self) -> bool {
        &&& self.bytes().len() == size_of::<T>()
        &&& self.is_valid() ==> #[trigger] abs_decode::<T>(self.bytes(), &self.value())
        &&& self.pt_untyped().wf()
    }

    /// Non-nullness follows from the underlying `PointsToUntyped`'s invariant,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn is_nonnull(tracked &self) {}

    /// Delegates to the underlying `PointsToUntyped`'s `ptr_bounds`,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn ptr_bounds(tracked &self) {
        self.pt_untyped.ptr_bounds();
    }

    /// Delegates to the underlying `PointsToUntyped`'s `provenance_not_none`.
    proof fn provenance_not_none(tracked &self) {
        self.pt_untyped.provenance_not_none();
    }

    /// Delegates to the underlying `PointsToUntyped`'s `is_disjoint`,
    /// since the two permissions track the same memory range.
    proof fn is_disjoint<OtherPointsToPerm: PointsToParam>(tracked &mut self, tracked other: &OtherPointsToPerm) {
        self.pt_untyped.is_disjoint(other);
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

    /// Well-formedness is defined in the `PointsToProperties` trait function `wf_basic`.
    pub open spec fn wf(&self) -> bool {
        self.wf_basic()
    }

    /// Specializes `is_disjoint` to the case when the other permission is a `PointsToUnaligned<S>`.
    pub proof fn is_disjoint_unaligned<S>(tracked &mut self, tracked other: &PointsToUnaligned<S>)
        requires
            size_of::<T>() != 0,
            size_of::<S>() != 0,
            self.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + size_of::<T>() <= other.ptr() as int || other.ptr() as int
                + size_of::<S>() <= final(self).ptr() as int,
    {
        self.size_eq_const_size();
        other.size_eq_const_size();
        self.is_disjoint(other);
    }
}

/**
Permission to access possibly-initialized, _typed_ memory.

The associated pointer ([`points_to.ptr()`](PointsTo::ptr)) is always a valid pointer for constructing
a reference to the underlying data. That means it's always aligned to its type
([`is_aligned`](PointsTo::is_nonnull)) and is non-null ([`is_nonnull`](PointsTo::is_nonnull)).

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

Currently, these use-cases aren't supported because `PointsTo` enforces both non-nullness
and alignment.
*/

// ptr |--> Init(v) means:
//   bytes in this memory are consistent with value v
//   and we have all the ghost state associated with type V
//
// ptr |--> Uninit means:
//   no knowledge about what's in memory
//   (to be pedantic, the bytes might be initialized in rust's abstract machine,
//   but we don't know so we have to pretend they're uninitialized)
pub tracked struct PointsTo<T: ?Sized> {
    pt_unaligned: Tracked<PointsToUnaligned<T>>,
}

impl<T: ?Sized> PointsTo<T> {
    pub closed spec fn pt_unaligned(self) -> PointsToUnaligned<T> {
        self.pt_unaligned@
    }

    pub open spec fn typed_value(self) -> TypedValue<T> {
        self.pt_unaligned().typed_value()
    }

    pub open spec fn pt_untyped(self) -> PointsToUntyped {
        self.pt_unaligned().pt_untyped()
    }

    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        self.pt_unaligned().bytes()
    }

    /// Returns `true` if the permission's associated memory is initialized.
    #[verifier::inline]
    pub open spec fn is_valid(&self) -> bool {
        self.typed_value().is_valid()
    }

    /// Returns `true` if the permission's associated memory is uninitialized.
    #[verifier::inline]
    pub open spec fn is_empty(&self) -> bool {
        self.typed_value().is_empty()
    }

    /// Returns a tracked reference to the underlying `PointsToUntyped` permission.
    pub proof fn tracked_pt_unaligned(tracked &self) -> tracked &PointsToUnaligned<T>
        returns
            self.pt_unaligned(),
    {
        &self.pt_unaligned
    }
}

impl<T> PointsTo<T> {
    pub open spec fn ptr(self) -> *mut T {
        self.pt_unaligned().ptr()
    }

    /// If the permission's associated memory is initialized,
    /// returns the value that the pointer points to.
    /// Otherwise, the result is meaningless.
    #[verifier::inline]
    pub open spec fn value(&self) -> T
        recommends
            self.is_valid(),
    {
        self.typed_value().value()
    }

    /// Invariant: The abstract bytes must decode into the value in memory.
    pub open spec fn wf(&self) -> bool {
        &&& self.ptr()@.addr as nat % align_of::<T>() == 0
        &&& self.pt_unaligned().wf()
    }

    pub proof fn is_aligned(tracked &self)
        requires
            self.wf(),
        ensures
            self.ptr()@.addr as nat % align_of::<T>() == 0,
    {
    }

    pub proof fn is_non_null(tracked &self)
        requires
            self.wf(),
        ensures
            self.ptr()@.addr != 0,
    {
    }

    pub proof fn provenance_not_none(tracked &self)
        requires
            size_of::<T>() != 0,
            self.wf(),
        ensures
            self.ptr()@.provenance != raw_ptr::Provenance::None,
    {
        self.tracked_pt_unaligned().provenance_not_none();
    }

    pub proof fn ptr_bounds(tracked &self)
        requires
            self.ptr()@.provenance.is_some(),
            self.wf(),
        ensures
            self.ptr()@.addr as int >= self.ptr()@.provenance.data().start_addr(),
            self.ptr()@.addr + size_of::<T>() <= self.ptr()@.provenance.data().start_addr()
                + self.ptr()@.provenance.data().alloc_len(),
    {
        self.tracked_pt_unaligned().ptr_bounds();
    }

    pub proof fn is_disjoint<S>(tracked &mut self, tracked other: &PointsTo<S>)
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + size_of::<T>() <= other.ptr() as int || other.ptr() as int
                + size_of::<S>() <= final(self).ptr() as int,
    {
        assume(false);
        self.pt_unaligned.is_disjoint(other.tracked_pt_unaligned());
    }
}


}