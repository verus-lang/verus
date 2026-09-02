use super::group_vstd_default;
use super::layout::{self, *};
use super::prelude::*;
use super::raw_ptr;
use super::raw_ptr::*;
use super::raw_ptr_new;
#[cfg(verus_keep_ghost)]
use super::type_representation::*;

verus! {

broadcast use group_vstd_default;

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
    pub axiom fn is_disjoint(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + size_of::<u8>() <= other.ptr() as int || other.ptr() as int
                + size_of::<u8>() <= final(self).ptr() as int,
    ;

    // necessary? Might only matter for PointsTo
    pub proof fn is_aligned(tracked &self)
        ensures
            self.ptr()@.addr as int % layout::align_of::<u8>() as int == 0,
    {
        broadcast use align_of_u8;

    }
}

pub tracked struct PointsToUntyped {
    seq_perm: Tracked<Seq<PointsToSingleton>>,
    ptr: Ghost<*mut [u8]>,
}

impl PointsToUntyped {
    pub closed spec fn seq_perm(self) -> Seq<PointsToSingleton> {
        self.seq_perm@
    }

    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        self.seq_perm().map(|i: int, pt_singleton: PointsToSingleton| pt_singleton.byte())
    }

    pub closed spec fn ptr(self) -> *mut [u8] {
        self.ptr@
    }

    pub open spec fn wf(self) -> bool {
        // Defining the provenance and address for the individual PointsToSingletons
        &&& forall|i|
            #![trigger self[i].ptr()@.provenance]
            #![trigger self[i].ptr()@.addr]
            0 <= i < self.len() ==> {
                &&& self[i].ptr()@.provenance == self.ptr()@.provenance
                &&& self[i].ptr()@.addr == self.ptr()@.addr + i
            }
            // Defining the metadata of the ptr
        &&& self.ptr()@.metadata == self.len()
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

    pub proof fn provenance_non_null(tracked &self)
        requires
            self.len() != 0,
            self.wf(),
        ensures
            self.ptr()@.provenance != raw_ptr::Provenance::None,
    {
        self.seq_perm.tracked_borrow(0).provenance_non_null();
    }

    pub proof fn ptr_bounds(tracked &self)
        requires
            self.ptr()@.provenance.is_some(),
            self.wf(),
        ensures
            self.ptr()@.addr as int >= self.ptr()@.provenance.data().start_addr(),
            self.ptr()@.addr + self.len() <= self.ptr()@.provenance.data().start_addr()
                + self.ptr()@.provenance.data().alloc_len(),
    {
        if self.len() > 0 {
            self.seq_perm.tracked_borrow(0).ptr_bounds();
            self.seq_perm.tracked_borrow(self.len() - 1).ptr_bounds();
        }
    }

    // necessary?
    pub proof fn is_aligned(tracked &self)
        ensures
            self.ptr()@.addr as int % layout::align_of::<u8>() as int == 0,
    {
        broadcast use align_of_u8;

    }

    // TODO: prove (recursively?)
    pub proof fn is_disjoint(tracked &mut self, tracked other: &PointsToUntyped)
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + final(self).len() <= other.ptr() as int || other.ptr() as int
                + other.len() <= final(self).ptr() as int,
    {
        assume(false);
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

    pub proof fn provenance_non_null(tracked &self)
        requires
            size_of::<T>() != 0,
            self.wf(),
        ensures
            self.ptr()@.provenance != raw_ptr::Provenance::None,
    {
        self.pt_untyped.provenance_non_null();
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

// impl<T> PointsToUnaligned<[T]> {
//     pub open spec fn ptr(self) -> *mut [T] {
//         ptr_mut_from_data::<[T]>(
//             PtrData {
//                 addr: self.perm().ptr()@.addr,
//                 provenance: self.perm().ptr()@.provenance,
//                 // if the size is 0 the metadata could still be nonzero, even if the byte length is 0
//                 // but we have no way of knowing what it should be if the memory is not valid
//                 // maybe create a test program with 0 memory to see what the pointer is?
//                 metadata: if size_of::<T>() == 0 {
//                     self.value().len()
//                 } else {
//                     (self.perm().len() / size_of::<T>()) as usize
//                 },
//             },
//         )
//     }
//     pub open spec fn len(self) -> nat {
//         self.ptr()@.metadata as nat
//     }
//     /// If the permission's associated memory is initialized,
//     /// returns the value that the pointer points to.
//     /// Otherwise, the result is meaningless.
//     #[verifier::inline]
//     pub open spec fn value(&self) -> &[T]
//         recommends
//             self.is_valid(),
//     {
//         self.typed_value().value()
//     }
//     /// Invariant: The abstract bytes must decode into the value in memory.
//     pub open spec fn wf(&self) -> bool {
//         &&& self.bytes().len() == size_of::<T>()
//             * self.len()
//         // &&& self.bytes().len() % size_of::<T>() == 0
//         &&& self.is_valid() ==> #[trigger] abs_decode::<[T]>(self.bytes(), self.value())
//         &&& self.perm().wf()
//     }
//     // pub proof fn len_val(tracked &self)
//     //     requires
//     //         self.wf(),
//     //     ensures
//     //         self.bytes().len() == size_of::<T>() * self.len(),
//     // {
//     //     if size_of::<T>() != 0 {
//     //         assert(self.bytes().len() == size_of::<T>() * (self.bytes().len() / size_of::<T>())) by (nonlinear_arith)
//     //             requires
//     //                 self.bytes().len() % size_of::<T>() == 0,
//     //                 size_of::<T>() != 0,
//     //         ;
//     //     } else {
//     //         assume(false);
//     //     }
//     // }
//     pub proof fn is_non_null(tracked &self)
//         requires
//             self.wf(),
//         ensures
//             self.ptr()@.addr != 0,
//     {
//     }
//     pub proof fn provenance_non_null(tracked &self)
//         requires
//             size_of::<T>() * self.len() != 0,
//             self.wf(),
//         ensures
//             self.ptr()@.provenance != raw_ptr::Provenance::None,
//     {
//         self.perm.provenance_non_null();
//     }
//     pub proof fn ptr_bounds(tracked &self)
//         requires
//             self.ptr()@.provenance.is_some(),
//             self.wf(),
//         ensures
//             self.ptr()@.addr as int >= self.ptr()@.provenance.data().start_addr(),
//             self.ptr()@.addr + size_of::<T>() * self.len()
//                 <= self.ptr()@.provenance.data().start_addr()
//                 + self.ptr()@.provenance.data().alloc_len(),
//     {
//         // self.len_val();
//         self.perm.ptr_bounds();
//     }
//     pub proof fn is_disjoint<S>(tracked &mut self, tracked other: &PointsToUnaligned<[S]>)
//         ensures
//             *old(self) == *final(self),
//             final(self).ptr() as int + size_of::<T>() * final(self).len() <= other.ptr() as int
//                 || other.ptr() as int + size_of::<S>() * other.len() <= final(self).ptr() as int,
//     {
//         assume(false);
//         self.perm.is_disjoint(other.tracked_pt_untyped());
//     }
// }
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

    pub proof fn provenance_non_null(tracked &self)
        requires
            size_of::<T>() != 0,
            self.wf(),
        ensures
            self.ptr()@.provenance != raw_ptr::Provenance::None,
    {
        self.tracked_pt_unaligned().provenance_non_null();
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

// TODO: is_disjoint, impl View for PointsTo types (helps to clarify the interface)
} // verus!
