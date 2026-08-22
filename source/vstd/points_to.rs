use super::prelude::*;
use super::raw_ptr;
use super::raw_ptr::*;
use super::raw_ptr_new;
#[cfg(verus_keep_ghost)]
use super::type_representation::*;

verus! {

#[verifier::external_body]
pub tracked struct PointsToSingleton {
    no_copy: NoCopy,
}

impl PointsToSingleton {
    /// The byte pointer that this permission is associated with.
    pub uninterp spec fn ptr(&self) -> *mut u8;

    /// The byte that this permission tracks.
    pub uninterp spec fn byte(&self) -> AbstractByte;

    /// Guarantee that the `PointsToSingleton` points to a non-null address.
    ///
    /// See <https://doc.rust-lang.org/std/ptr/#safety>
    pub axiom fn is_nonnull(tracked &self)
        ensures
            self.ptr()@.addr != 0,
    ;

    /// The memory associated with a pointer should always be within bounds of its spatial provenance.
    pub axiom fn ptr_bounds(tracked &self)
        requires
            self.ptr()@.provenance.is_some(),
        ensures
    // Q: better to use size of u8 or 1?

            self.ptr()@.addr as int >= self.ptr()@.provenance.data().start_addr(),
            self.ptr()@.addr + size_of::<u8>() <= self.ptr()@.provenance.data().start_addr()
                + self.ptr()@.provenance.data().alloc_len(),
    ;

    /// Since `u8` is not a ZST, the pointer's provenance is non-null.
    /// <https://doc.rust-lang.org/std/ptr/index.html#provenance>
    pub axiom fn provenance_non_null(tracked &self)
        ensures
            self.ptr()@.provenance != raw_ptr::Provenance::None,
    ;

    /// Guarantees that the memory ranges associated with two distinct, non-ZST permissions will not overlap,
    /// since you cannot have two permissions to the same memory.
    /// (`self` is an &mut reference to enforce distinctness,
    /// so you cannot pass the same PointsTo as both arguments.)
    /// Since `u8` is not a ZST, this implies the pointers have distinct addresses.
    pub axiom fn is_disjoint(tracked &mut self, tracked other: &PointsToSingleton)
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + size_of::<u8>() <= other.ptr() as int || other.ptr() as int
                + size_of::<u8>() <= final(self).ptr() as int,
    ;
    // TODO: prove alignment?

}

// TODO: impl View for PointsToSingleton?
pub tracked struct PointsToUntyped {
    seq_perm: Tracked<Seq<PointsToSingleton>>,
    ptr: Ghost<*mut [u8]>,
}

impl PointsToUntyped {
    pub closed spec fn bytes(self) -> Seq<AbstractByte> {
        self.seq_perm.map(|i: int, perm: PointsToSingleton| perm.byte())
    }

    pub closed spec fn ptr(self) -> *mut [u8] {
        *self.ptr
    }

    pub closed spec fn seq_perm(self) -> Seq<PointsToSingleton> {
        *self.seq_perm
    }

    pub open spec fn wf(self) -> bool {
        &&& forall|i|
            0 <= i < self.len() ==> {
                &&& self[i].ptr()@.provenance == self.ptr()@.provenance
                &&& self[i].ptr()@.addr == self.ptr()@.addr + i
            }
        &&& self.ptr()@.metadata == self.len()
        &&& self.ptr()@.addr != 0
    }

    /// The length of the sequence of `PointsToUntyped`.
    #[verifier::inline]
    pub open spec fn len(self) -> nat {
        self.bytes().len()
    }

    /// `[]` operator, synonymous with `index`.
    #[verifier::inline]
    pub open spec fn spec_index(self, index: int) -> PointsToSingleton
        recommends
            0 <= index < self.len(),
    {
        self.seq_perm()[index]
    }
    // TODO: prove provenance is some, in bounds, alignment, disjointness

}

/// Represents (typed) contents of memory.
// Don't use std Option here in order to avoid circular dependency issues
// with verifying the standard library.
// (Also, using our own enum here lets us have more meaningful
// variant names like Uninit/Init.)
#[verifier::accept_recursive_types(T)]
pub tracked enum TypedValue<T: ?Sized> {
    /// Represents uninitialized memory.
    Empty,
    /// Represents initialized memory with the given value of type `T`.
    Valid(Box<T>),
}

impl<T> TypedValue<T> {
    /// Returns `true` if it is a [`MemContents::Init`] value.
    #[verifier::inline]
    pub open spec fn is_valid(&self) -> bool {
        self is Valid
    }

    /// Returns `true` if it is a [`MemContents::Uninit`] value.
    #[verifier::inline]
    pub open spec fn is_empty(&self) -> bool {
        self is Empty
    }

    /// If it is a [`MemContents::Init`] value, returns the value.
    /// Otherwise, the return value is meaningless.
    #[verifier::inline]
    pub open spec fn value(&self) -> T
        recommends
            self is Valid,
    {
        *self->0
    }
}

#[verifier::accept_recursive_types(T)]
pub tracked struct PointsToUnaligned<T: ?Sized> {
    val: TypedValue<T>,
    perm: Tracked<PointsToUntyped>,
}

impl<T> PointsToUnaligned<T> {
    pub closed spec fn perm(self) -> PointsToUntyped {
        self.perm@
    }

    pub open spec fn ptr(self) -> *mut T {
        self.perm().ptr() as *mut T
    }

    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        self.perm().bytes()
    }

    pub closed spec fn typed_value(self) -> TypedValue<T> {
        self.val
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
    pub axiom fn abstract_bytes_decode(&self)
        ensures
            self.is_valid() ==> #[trigger] abs_decode::<T>(self.bytes(), &self.value()),
            self.is_empty() ==> self.bytes().len() == size_of::<T>(),
    ;
}

// PointsToData
// impl View for PointsTo
} // verus!
