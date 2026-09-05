use super::group_vstd_default;
use super::layout::{self, *};
use super::prelude::*;
use super::raw_ptr;
use super::raw_ptr::*;
#[cfg(verus_keep_ghost)]
use super::type_representation::*;

verus! {

broadcast use group_vstd_default;

/// Defines parameters common to all `PointsTo` permissions: 
/// the pointer to memory and the size of the pointed-to region.
pub trait PointsToParam: Sized {
    type A: ?Sized;

    /// The pointer that this permission is associated with.
    spec fn ptr(self) -> *mut Self::A;

    /// The size of the memory region that this permission tracks.
    spec fn size(self) -> nat;
}

/// Restricts `PointsToParam` to permissions whose pointed-to size is determined by the type alone.
/// This lets code which is generic over some `PointsToParam`
/// rely on all instances of that type reporting the same `size()`
/// (for example, `SeqPointsTo` requires that every permission in the sequence must track the same size of memory).
pub trait FixedSizeParam: PointsToParam {
    /// The (constant) size of the memory region that this permission tracks,
    /// which is the same for every `PointsTo` permission satisfying this trait bound.
    spec fn const_size() -> nat;

    /// Ensures that the `PointsToParam` size is always the same as the constant size defined here.
    proof fn size_eq_const_size(tracked &self)
        ensures
            self.size() == Self::const_size(),
    ;
}

/// Defines properties which should hold of any `PointsTo` permission.
pub trait PointsToProperties: PointsToParam {
    /// Define basic well-formed-ness conditions. 
    /// This function is designed to apply to a generic trait implementation 
    /// of this trait for a `PointsTo` permission,
    /// and specific implementatations of the `PointsTo` permissions can define additional well-formedness properites.
    /// 
    /// See `SeqPointsTo` and `PointsToUntyped` for an example.
    spec fn wf_basic(self) -> bool;

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
    // TODO: change data() to unwrap()
    proof fn ptr_bounds(tracked &self)
        requires
            self.ptr()@.provenance.is_some(),
            self.wf_basic(),
        ensures
            self.ptr()@.addr as int >= self.ptr()@.provenance.data().start_addr(),
            self.ptr()@.addr + self.size() <= self.ptr()@.provenance.data().start_addr()
                + self.ptr()@.provenance.data().alloc_len(),
    ;

    /// If the size of the pointed-to region is nonzero, 
    /// then the pointer's provenance is non-null.
    proof fn provenance_not_none(tracked &self)
        requires
            self.size() != 0,
            self.wf_basic(),
        ensures
            self.ptr()@.provenance != raw_ptr::Provenance::None,
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
    /// the disjointness definition as stated here here does not hold,
    /// since the ZST pointer could be in the middle of the non-ZST's range.
    proof fn is_disjoint<OtherPointsToPerm: PointsToParam>(tracked &mut self, tracked other: &OtherPointsToPerm)
        requires
            self.size() != 0,
            other.size() != 0,
            self.wf_basic(),
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + final(self).size() <= other.ptr() as int || other.ptr() as int
                + other.size() <= final(self).ptr() as int,
    ;
}

/// Permission to access a byte of memory.
#[verifier::external_body]
pub tracked struct PointsToSingleton {
    no_copy: NoCopy,
}

impl PointsToParam for PointsToSingleton {
    type A = u8;

    /// This permission points to a single byte of memory.
    uninterp spec fn ptr(self) -> *mut u8;

    /// This permission tracks a single byte of memory.
    open spec fn size(self) -> nat {
        size_of::<u8>()
    }
}

impl PointsToProperties for PointsToSingleton {
    /// A `PointsToSingleton` is always well-formed.
    open spec fn wf_basic(self) -> bool {
        true
    }

    /// Guarantee that the `PointsToSingleton` points to a non-null address.
    ///
    /// See <https://doc.rust-lang.org/std/ptr/#safety>
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
    axiom fn is_disjoint<PointsToPerm: PointsToParam>(tracked &mut self, tracked other: &PointsToPerm);
}

impl FixedSizeParam for PointsToSingleton {
    /// A `PointsToSingleton` always tracks a single byte of memory.
    open spec fn const_size() -> nat {
        size_of::<u8>()
    }

    proof fn size_eq_const_size(tracked &self) {}
}

impl PointsToSingleton {
    /// The byte that this permission tracks.
    pub uninterp spec fn byte(self) -> AbstractByte;

    /// Guarantees that the memory ranges associated with two distinct, non-ZST permissions will not overlap,
    /// since you cannot have two permissions to the same memory.
    /// (`self` is an &mut reference to enforce distinctness,
    /// so you cannot pass the same PointsTo as both arguments.)
    /// Since `u8` is not a ZST, this implies the pointers have distinct addresses.
    pub proof fn is_disjoint_singleton(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + size_of::<u8>() <= other.ptr() as int || other.ptr() as int
                + size_of::<u8>() <= final(self).ptr() as int,
    {
        self.is_disjoint(other);
    }
}

/// The interface for a `PointsToSingleton` permission, 
/// which represents permission to access a single byte in memory.
/// We track the pointer to that memory as well as 
/// the abstract byte corresponding to Rust's abstract machine.
#[cfg(verus_keep_ghost)]
pub ghost struct PointsToSingletonData {
    pub ptr: *mut u8,
    pub byte: AbstractByte,
}

#[cfg(verus_keep_ghost)]
impl View for PointsToSingleton {
    type V = PointsToSingletonData;

    open spec fn view(&self) -> Self::V {
        PointsToSingletonData {
            ptr: self.ptr(),
            byte: self.byte(),
        }
    }
}

pub tracked struct SeqPointsTo<T: ?Sized, PointsToPerm: PointsToProperties + FixedSizeParam> {
    seq_pt: Seq<PointsToPerm>,
    ptr: Ghost<*mut T>,
}

impl<T: ?Sized, PointsToPerm: PointsToProperties + FixedSizeParam> PointsToParam for SeqPointsTo<T, PointsToPerm> {
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

impl<T: ?Sized, PointsToPerm: PointsToProperties + FixedSizeParam> PointsToProperties for SeqPointsTo<T, PointsToPerm> {
    open spec fn wf_basic(self) -> bool {
        // Defining the provenance and address for the individual PointsToSingletons
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
    proof fn is_nonnull(tracked &self) {}

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

    proof fn is_disjoint<OtherPointsToPerm: PointsToParam>(tracked &mut self, tracked other: &OtherPointsToPerm) {
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
            super::arithmetic::div_mod::lemma_multiply_divide_lt(other_addr - self_addr, csize, len);
            super::arithmetic::div_mod::lemma_div_pos_is_pos(other_addr - self_addr, csize);
            self.seq_pt.tracked_borrow_mut(k).size_eq_const_size();
            self.seq_pt.tracked_borrow_mut(k).is_disjoint(other);
        }
    }
}

impl<T: ?Sized, PointsToPerm: PointsToProperties + FixedSizeParam> SeqPointsTo<T, PointsToPerm> {
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

    // Sanity check: ensures that if the length is 0, the size is always 0,
    // even though the permission size calculation indexes into an empty sequence.
    proof fn len_zero_size_zero(&self) 
        requires
            self.seq_pt().len() == 0,
        ensures
            self.size() == 0,
    {}
}

impl SeqPointsTo<[u8], PointsToSingleton> {
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

pub tracked struct PointsToUnaligned<T: ?Sized> {
    val: TypedValue<T>,
    pt_untyped: Tracked<PointsToUntyped>,
}

impl<T: ?Sized> PointsToUnaligned<T> {
    pub closed spec fn typed_value(self) -> TypedValue<T> {
        self.val
    }

    pub closed spec fn pt_untyped(self) -> PointsToUntyped {
        self.pt_untyped@
    }

    #[verifier::inline]
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        self.pt_untyped().bytes()
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

    /// Returns the size of the pointed-to region, in bytes.
    #[verifier::inline]
    pub open spec fn size(self) -> nat {
        self.pt_untyped().len()
    }

    /// Returns a tracked reference to the underlying `PointsToUntyped` permission.
    pub proof fn tracked_pt_untyped(tracked &self) -> tracked &PointsToUntyped
        returns
            self.pt_untyped(),
    {
        &self.pt_untyped
    }
}

impl<T> PointsToUnaligned<T> {
    pub open spec fn ptr(self) -> *mut T {
        self.pt_untyped().ptr() as *mut T
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
        &&& self.bytes().len() == size_of::<T>()
        &&& self.is_valid() ==> #[trigger] abs_decode::<T>(self.bytes(), &self.value())
        &&& self.pt_untyped().wf()
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
        self.pt_untyped.provenance_not_none();
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
        self.pt_untyped.ptr_bounds();
    }

    pub proof fn is_disjoint<S>(tracked &mut self, tracked other: &PointsToUnaligned<S>)
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + size_of::<T>() <= other.ptr() as int || other.ptr() as int
                + size_of::<S>() <= final(self).ptr() as int,
    {
        assume(false);
        self.pt_untyped.is_disjoint(other.tracked_pt_untyped());
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

    /// Returns the size of the pointed-to region, in bytes.
    #[verifier::inline]
    pub open spec fn size(self) -> nat {
        self.pt_unaligned().size()
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

// impl IsPointsTo for PointsToUntyped {}
// impl<T: ?Sized> IsPointsTo for PointsToUnaligned<T> {}
// impl<T: ?Sized> IsPointsTo for PointsTo<T> {}

// impl<T: ?Sized, PointsToPerm: IsPointsTo> IsPointsTo for SeqPointsTo<T, PointsToPerm> {

// }

// impl<T: ?Sized, PointsToPerm: IsPointsTo> SeqPointsTo<T, PointsToPerm> {

// }

// impl SeqPointsTo<[u8], PointsToSingleton> {

// }

// impl<T> SeqPointsTo<T, PointsTo<T>> {

// }

// TODO: is_disjoint, impl View for PointsTo types (helps to clarify the interface)
} // verus!
