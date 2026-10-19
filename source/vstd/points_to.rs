use super::group_vstd_default;
use super::layout::{self, *};
use super::prelude::*;
use super::raw_ptr_new::*;
#[cfg(verus_keep_ghost)]
use super::type_representation::*;

verus! {

// A private seal trait to prevent `PointsToPhys` from being implemented outside of vstd.
pub(crate) trait PointsToPhysSealed {}

/// Defines the physical memory region that a `PointsTo` permission covers,
/// by specifying the pointer to memory and the size of the pointed-to region.
#[allow(private_bounds)]
pub trait PointsToPhys: Sized + PointsToPhysSealed {
    type A: ?Sized; //caller choice vs implementor choice, so maybe can go with implementor

    /// The pointer that this permission is associated with.
    spec fn ptr(self) -> *mut Self::A;

    /// The size of the memory region that this permission tracks.
    spec fn size(self) -> nat;

    /// Define basic well-formed-ness conditions.
    /// This function is designed to apply to a generic trait implementation
    /// of this trait for a `PointsTo` permission,
    /// and specific implementatations of the `PointsTo` permissions can define additional well-formedness properites.
    /// Among other things, it ties `size()` to the memory the permission actually holds.
    ///
    /// See `SeqPointsTo` and `PointsToUntyped` for an example.
    spec fn wf_basic(self) -> bool;
}

/// Restricts `PointsToPhys` to permissions whose pointed-to size is determined by the type alone.
/// This lets code which is generic over some `PointsToPhys`
/// rely on all instances of that type reporting the same `size()`
/// (for example, `SeqPointsTo` requires that every permission in the sequence must track the same size of memory).
pub trait FixedSize: PointsToPhys {
    /// The (constant) size of the memory region that this permission tracks,
    /// which is the same for every `PointsTo` permission satisfying this trait bound.
    spec fn const_size() -> nat;

    /// Ensures that the `PointsToPhys` size is always the same as the constant size defined here.
    proof fn size_eq_const_size(tracked &self)
        ensures
            self.size() == Self::const_size(),
    ;
}

/// Defines properties which should hold of any `PointsTo` permission.
pub trait PointsToProperties: PointsToPhys {
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
    /// the disjointness definition as stated here here does not hold,
    /// since the ZST pointer could be in the middle of the non-ZST's range.
    ///
    /// Both permissions must be `wf_basic`, since that is what ties `size()` to the memory actually held.
    proof fn is_disjoint<OtherPointsToPerm: PointsToPhys>(
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

    /// Specifies that `new` keeps `old`'s pointers and length, and satisfies whatever else
    /// (e.g. decode validity of a typed value) is needed for `wf_basic` to carry over from `old`.
    /// Each implementation defines what this means for its permission type.
    spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool;

    /// If `old` satisfies `wf_basic` and `new` satisfies `ptrs_len_same_valid` with respect to it,
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
pub tracked struct PointsToSingleton {
    no_copy: NoCopy,
}

impl PointsToPhysSealed for PointsToSingleton {}

impl PointsToPhys for PointsToSingleton {
    type A = u8;

    /// This permission points to a single byte of memory.
    uninterp spec fn ptr(self) -> *mut u8;

    /// This permission tracks a single byte of memory.
    open spec fn size(self) -> nat {
        size_of::<u8>()
    }

    /// A `PointsToSingleton` is always well-formed.
    open spec fn wf_basic(self) -> bool {
        true
    }
}

impl PointsToProperties for PointsToSingleton {
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
    axiom fn is_disjoint<PointsToPerm: PointsToPhys>(
        tracked &mut self,
        tracked other: &PointsToPerm,
    );

    /// A `PointsToSingleton` only needs to keep its pointer.
    open spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool {
        new.ptr() == old.ptr()
    }

    /// Trivial, since a `PointsToSingleton` is always well-formed.
    proof fn stays_wf_basic(old: Self, new: Self) {
    }
}

impl FixedSize for PointsToSingleton {
    /// A `PointsToSingleton` always tracks a single byte of memory.
    open spec fn const_size() -> nat {
        size_of::<u8>()
    }

    proof fn size_eq_const_size(tracked &self) {
    }
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
        PointsToSingletonData { ptr: self.ptr(), byte: self.byte() }
    }
}

// impl<T: ?Sized> IsPointsTo for PointsToUnaligned<T> {}
// impl<T: ?Sized> IsPointsTo for PointsTo<T> {}
// impl<T: ?Sized, PointsToPerm: IsPointsTo> IsPointsTo for SeqPointsTo<T, PointsToPerm> {
// }
// impl<T> SeqPointsTo<T, PointsTo<T>> {
// }
} // verus!
