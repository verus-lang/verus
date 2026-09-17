use super::group_vstd_default;
use super::layout::{self, *};
use super::points_to::*;
use super::prelude::*;
use super::raw_ptr;
use super::raw_ptr::*;
#[cfg(verus_keep_ghost)]
use super::type_representation::*;

verus! {

broadcast use group_vstd_default;

pub tracked struct SeqPointsTo<T: ?Sized, PointsToPerm: PointsToProperties + FixedSizeParam> {
    seq_pt: Seq<PointsToPerm>,
    ptr: Ghost<*mut T>,
}

impl<T, PointsToPerm> PointsToParam for SeqPointsTo<T, PointsToPerm> where
    T: ?Sized,
    PointsToPerm: PointsToProperties + FixedSizeParam,
 {
    type A = T;

    closed spec fn ptr(self) -> *mut T {
        self.ptr@
    }

    /// The size of the pointed-to region is given by the length of the sequence
    /// times the (constant) size of the permission type in the sequence.
    open spec fn size(self) -> nat {
        self.seq_pt().len() * PointsToPerm::const_size()
    }
}

impl<T, PointsToPerm> PointsToProperties for SeqPointsTo<T, PointsToPerm> where
    T: ?Sized,
    PointsToPerm: PointsToProperties + FixedSizeParam,
 {
    open spec fn wf_basic(self) -> bool {
        // Defining the provenance and address for the individual PointsToPerms
        &&& forall|i|
            #![trigger self[i].ptr()@.provenance]
            #![trigger self[i].ptr()@.addr]
            #![trigger self[i].wf_basic()]
            0 <= i < self.len() ==> {
                &&& self[i].ptr()@.provenance == self.ptr()@.provenance
                &&& self[i].ptr()@.addr == self.ptr()@.addr + i * PointsToPerm::const_size()
                &&& self[i].wf_basic()
            }
            // The ptr is non-null
        &&& self.ptr()@.addr
            != 0
        // If ptr's provenance is Some, the address is in bounds of the provenance
        &&& self.ptr()@.provenance.is_some() ==> {
            &&& self.ptr()@.provenance.data().start_addr() <= self.ptr()@.addr
            &&& self.ptr()@.addr <= self.ptr()@.provenance.data().start_addr()
                + self.ptr()@.provenance.data().alloc_len()
        }
    }

    /// Non-nullness is guaranteed by the invariant.
    proof fn is_nonnull(tracked &self) {
    }

    /// If the size is non-zero, the length must be nonzero.
    /// Then this follows from the `provenance_not_none` property of an individual `PointsToPerm`.
    proof fn provenance_not_none(tracked &self) {
        self.seq_pt.tracked_borrow(0).size_eq_const_size();
        self.seq_pt.tracked_borrow(0).provenance_not_none();
    }

    proof fn ptr_bounds(tracked &self) {
        if self.len() > 0 {
            self.seq_pt.tracked_borrow(self.len() - 1).ptr_bounds();
            self.seq_pt.tracked_borrow(self.len() - 1).size_eq_const_size();
            super::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                PointsToPerm::const_size() as int,
                (self.len() - 1) as int,
                1,
            );
        }
    }

    proof fn is_disjoint<OtherPointsToPerm: PointsToParam>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    ) {
        let self_addr = self.ptr()@.addr as int;
        let other_addr = other.ptr()@.addr as int;
        let csize = PointsToPerm::const_size() as int;
        let len = self.len() as int;

        if other_addr < self_addr {
            // `other` starts strictly before `self`'s whole range: since element 0
            // starts exactly where `self` does, its disjointness from `other` is
            // exactly the disjointness we need for the whole array.
            self.seq_pt.tracked_borrow_mut(0).size_eq_const_size();
            self.seq_pt.tracked_borrow_mut(0).is_disjoint(other);
            assert(self.seq_pt =~= old(self).seq_pt);
        } else if other_addr >= self_addr + len * csize {
            // `other` starts at or after `self`'s whole range ends: the last
            // element ends exactly where `self` does, so its disjointness from
            // `other` gives us what we need.
            self.seq_pt.tracked_borrow_mut(len - 1).size_eq_const_size();
            self.seq_pt.tracked_borrow_mut(len - 1).is_disjoint(other);
            assert(self.seq_pt =~= old(self).seq_pt);
            super::arithmetic::mul::lemma_mul_is_distributive_add_other_way(csize, len - 1, 1);
        } else {
            // `other` starts strictly inside `self`'s range: find the element `k`
            // whose byte range contains `other`'s start address, and derive a
            // contradiction from the fact that it can't possibly be disjoint from
            // `other` (since `other`'s own start address lies within it).
            let k = (other_addr - self_addr) / csize;
            super::arithmetic::div_mod::lemma_fundamental_div_mod(other_addr - self_addr, csize);
            super::arithmetic::div_mod::lemma_remainder(other_addr - self_addr, csize);
            super::arithmetic::div_mod::lemma_multiply_divide_lt(
                other_addr - self_addr,
                csize,
                len,
            );
            super::arithmetic::div_mod::lemma_div_pos_is_pos(other_addr - self_addr, csize);
            self.seq_pt.tracked_borrow_mut(k).size_eq_const_size();
            self.seq_pt.tracked_borrow_mut(k).is_disjoint(other);
        }
    }
}

impl<T, PointsToPerm> SeqPointsTo<T, PointsToPerm> where
    T: ?Sized,
    PointsToPerm: PointsToProperties + FixedSizeParam,
 {
    /// The sequence of permissions that the `SeqPointsTo` contains.
    pub closed spec fn seq_pt(self) -> Seq<PointsToPerm> {
        self.seq_pt
    }

    /// The length of the sequence of `PointsToPerm`.
    #[verifier::inline]
    pub open spec fn len(self) -> nat {
        self.seq_pt().len()
    }

    /// `[]` operator, synonymous with `index`.
    #[verifier::inline]
    pub open spec fn spec_index(self, index: int) -> PointsToPerm
        recommends
            0 <= index < self.len(),
    {
        self.seq_pt()[index]
    }
}

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
        PointsToUntypedData { ptr: self.ptr(), bytes: self.bytes() }
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

/// The interface for a `PointsToUnaligned` permission,
/// which represents permission to access possibly-unaligned memory
/// which may decode to a valid value of type `T`.
/// We track the pointer to that memory,
/// the (possibly-valid) typed value, and its abstract bytes.
#[cfg(verus_keep_ghost)]
pub ghost struct PointsToUnalignedData<T> {
    pub ptr: *mut T,
    pub value: TypedValue<T>,
    pub bytes: Seq<AbstractByte>,
}

#[cfg(verus_keep_ghost)]
impl<T> View for PointsToUnaligned<T> {
    type V = PointsToUnalignedData<T>;

    open spec fn view(&self) -> Self::V {
        PointsToUnalignedData { ptr: self.ptr(), value: self.typed_value(), bytes: self.bytes() }
    }
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

    proof fn size_eq_const_size(tracked &self) {
    }
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
    proof fn is_nonnull(tracked &self) {
    }

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
    proof fn is_disjoint<OtherPointsToPerm: PointsToParam>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    ) {
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
    Valid(Box<T>),
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
}

impl<T> TypedValue<[T]> {
    /// If it is a [`TypedValue::Valid`] value, returns the value.
    /// Otherwise, the return value is meaningless.
    // Does this make sense as the return value? Returning [T] doesn't work bc it's not Sized.
    #[verifier::inline]
    pub open spec fn value(&self) -> &[T]
        recommends
            self is Valid,
    {
        &*self->0
    }
}

/**
Permission to access possibly-initialized, _typed_ memory.

The associated pointer ([`points_to.ptr()`](PointsTo::ptr)) is always a valid pointer for constructing
a reference to the underlying data. That means it's always aligned to its type
([`is_aligned`](PointsTo::is_aligned)) and is non-null ([`is_nonnull`](PointsTo::is_nonnull)).

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

/// The interface for a `PointsTo` permission,
/// which represents permission to access memory which is aligned to `T`,
/// whose bytes may decode to a valid value of type `T`.
/// We track the pointer to that memory,
/// the (possibly-valid) typed value, and its abstract bytes.
/// 
/// Data associated with a `PointsTo` permission.
/// We keep track of both the pointer, the (potentially uninitialized) value
/// it points to, and the abstract bytes in memory corresponding to Rust's abstract machine.
///
/// If `mem_contents` is `Init(T)`, this signifies that `ptr` points to initialized memory,
/// and the value of `mem_contents` is consistent with the bytes `ptr` points to,
/// We also have all the ghost state associated with type `T`.
///
/// If `mem_contents` is `Uninit`, then we have no knowledge about what's in memory,
/// and we assume `ptr` points to uninitialized memory.
/// (To be pedantic, the bytes might be initialized in Rust's abstract machine,
///  but we don't know, so we have to pretend they're uninitialized.)
#[cfg(verus_keep_ghost)]
pub ghost struct PointsToData<T> {
    pub ptr: *mut T,
    pub value: TypedValue<T>,
    pub bytes: Seq<AbstractByte>,
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
        self.pt_unaligned@
    }

    /// The (possibly-valid) typed value that this permission tracks.
    pub open spec fn typed_value(self) -> TypedValue<T> {
        self.pt_unaligned().typed_value()
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
    pub proof fn tracked_pt_unaligned(tracked &self) -> tracked &PointsToUnaligned<T>
        returns
            self.pt_unaligned(),
    {
        &self.pt_unaligned
    }
}

impl<T> PointsToParam for PointsTo<T> {
    type A = T;

    /// Delegates to the underlying `PointsToUnaligned`'s pointer.
    open spec fn ptr(self) -> *mut T {
        self.pt_unaligned().ptr()
    }

    /// The size of the pointed-to region is the size of `T`.
    open spec fn size(self) -> nat {
        size_of::<T>()
    }
}

impl<T> FixedSizeParam for PointsTo<T> {
    /// A `PointsTo<T>` always tracks `size_of::<T>()` bytes of memory.
    open spec fn const_size() -> nat {
        size_of::<T>()
    }

    proof fn size_eq_const_size(tracked &self) {
    }
}

impl<T> PointsToProperties for PointsTo<T> {
    /// A `PointsTo` is well-formed if its pointer is aligned to `T`,
    /// and the underlying `PointsToUnaligned` is well-formed.
    open spec fn wf_basic(self) -> bool {
        &&& self.ptr()@.addr as nat % align_of::<T>() == 0
        &&& self.pt_unaligned().wf()
    }

    /// Non-nullness follows from the underlying `PointsToUnaligned`'s invariant,
    /// since `self.ptr()` and `self.pt_unaligned().ptr()` are the same pointer.
    proof fn is_nonnull(tracked &self) {
    }

    /// Delegates to the underlying `PointsToUnaligned`'s `ptr_bounds`,
    /// since `self.ptr()` and `self.pt_unaligned().ptr()` are the same pointer.
    proof fn ptr_bounds(tracked &self) {
        self.pt_unaligned.ptr_bounds();
    }

    /// Delegates to the underlying `PointsToUnaligned`'s `provenance_not_none`.
    proof fn provenance_not_none(tracked &self) {
        self.pt_unaligned.provenance_not_none();
    }

    /// Delegates to the underlying `PointsToUnaligned`'s `is_disjoint`,
    /// since the two permissions track the same memory range.
    proof fn is_disjoint<OtherPointsToPerm: PointsToParam>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    ) {
        self.pt_unaligned.is_disjoint(other);
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

    /// Well-formedness is defined in the `PointsToProperties` trait function `wf_basic`.
    pub open spec fn wf(&self) -> bool {
        self.wf_basic()
    }

    pub proof fn is_aligned(tracked &self)
        requires
            self.wf(),
        ensures
            self.ptr()@.addr as nat % align_of::<T>() == 0,
    {
    }

    /// Specializes `is_disjoint` to the case when the other permission is a `PointsTo<S>`.
    pub proof fn is_disjoint_pointsto<S>(tracked &mut self, tracked other: &PointsTo<S>)
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

impl<T> SeqPointsTo<T, PointsTo<T>> {
    /// In addition to the well-formed-ness properties which must hold of every `SeqPointsTo`,
    /// the `*mut T` pointer must be aligned to `T`.
    pub open spec fn wf(self) -> bool {
        &&& self.wf_basic() 
        &&& self.ptr()@.addr as nat % align_of::<T>() == 0
    }

    /// A "flattened" view of the abstract bytes.
    /// Because the abstract bytes do not change across casting/transmuting, it is often more
    /// convenient to have a single flattened view of the bytes that is the same as for `PointsTo<[T]>`.
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        Self::bytes_inner(self.seq_pt())
    }

    pub open spec fn bytes_inner(perms: Seq<PointsTo<T>>) -> Seq<AbstractByte> {
        perms.fold_left(
            Seq::empty(),
            |acc: Seq<AbstractByte>, elt: PointsTo<T>| acc + elt.bytes(),
        )
    }

    pub open spec fn typed_value(self) -> Seq<TypedValue<T>> {
        self.seq_pt().map(|i: int, pt: PointsTo<T>| pt.typed_value())
    }

    /// Returns `true` if all of the permission's associated memory is valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_valid(&self) -> bool {
        forall|i| 0 <= i < self.len() ==> #[trigger] self[i].is_valid()
    }

    /// Returns `true` if any part of the permission's associated memory is not valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_empty(&self) -> bool {
        !self.is_valid()
    }

    /// Returns `true` if all of the permission's associated memory is not valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_fully_empty(&self) -> bool {
        forall|i| 0 <= i < self.len() ==> #[trigger] self[i].is_empty()
    }

    /// Given that all of the permission's associated memory is initialized,
    /// returns the underlying values as a sequence.
    #[verifier::inline]
    pub open spec fn value(&self) -> Seq<T>
        recommends
            self.is_valid(),
    {
        Seq::new(self.len(), |i| self[i].value())
    }

    /// Returns a `tracked` reference to the underlying `Seq<PointsTo<T>>`,
    /// given `tracked &self`.
    pub proof fn tracked_pt_seq(tracked &self) -> (tracked ret: &Seq<PointsTo<T>>)
        requires
            self.wf(),
        ensures
            ret == self.seq_pt(),
    {
        &self.seq_pt
    }

    // /// Specializes `is_disjoint` to the case when the other permission is a `PointsToUntyped`.
    // pub proof fn is_disjoint_untyped(tracked &mut self, tracked other: &PointsToUntyped)
    //     requires
    //         self.len() != 0,
    //         other.len() != 0,
    //         self.wf(),
    //     ensures
    //         *old(self) == *final(self),
    //         final(self).ptr() as int + final(self).len() <= other.ptr() as int || other.ptr() as int
    //             + other.len() <= final(self).ptr() as int,
    // {
    //     assert(self.len() == self.size());
    //     assert(other.size() == other.len() * other.seq_pt()[0].size());
    //     self.is_disjoint(other);
    // }
}

} // verus!
