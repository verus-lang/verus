#![allow(unused_imports)]

use super::ptr_model;
use super::ptr_model::*;
use super::super::group_vstd_default;
use super::super::layout::{self, *};
use super::super::modes::tracked_ref;
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
/// Additionally defines pointer-level well-formedness which is required
/// for proving properties that hold for any `PointsTo` permission,
/// along with the conditions that preserve well-formedness.
#[allow(private_bounds)]
pub trait PTPhys: Sized + PTPhysSealed {
    type A: ?Sized;

    /// The pointer that this permission is associated with.
    spec fn ptr(self) -> *mut Self::A;

    /// The size, in bytes, of the memory region tracked by a permission
    /// whose pointer has the given metadata.
    /// A permission `p` tracks `Self::size(p.ptr()@.metadata)` bytes.
    spec fn size(metadata: Metadata<Self::A>) -> nat;

    /// Define basic well-formedness conditions on the permission's pointer
    /// which are necessary to ensure all of the `PTProperties` requirements.
    /// `PTTypedValue::wf` builds on this to add conditions on the bytes and typed value,
    /// as well as adding pointer conditions specific to a given permission type.
    spec fn wf_basic(self) -> bool;

    /// Specifies necessary conditions for ensuring that `new` and `old` are permissions
    /// to the same region of memory and that `wf_basic` carries over from `old`:
    /// `new` must keep `old`'s pointers and length.
    /// Each implementation defines what this means for its permission type.
    spec fn ptrs_len_same(old: Self, new: Self) -> bool;

    /// If `old` satisfies `wf_basic` and `new` satisfies `ptrs_len_same` with respect to it,
    /// then `new` satisfies `wf_basic`.
    proof fn stays_wf_basic(old: Self, new: Self)
        requires
            old.wf_basic(),
            Self::ptrs_len_same(old, new),
        ensures
            new.wf_basic(),
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
            self.ptr()@.addr + Self::size(self.ptr()@.metadata)
                <= self.ptr()@.provenance.unwrap().start_addr() + self.ptr()@.provenance.unwrap().alloc_len(),
    ;

    /// If the size of the pointed-to region is nonzero,
    /// then the pointer's provenance is non-null.
    proof fn provenance_not_none(tracked &self)
        requires
            Self::size(self.ptr()@.metadata) != 0,
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
            Self::size(self.ptr()@.metadata) != 0,
            OtherPointsToPerm::size(other.ptr()@.metadata) != 0,
            self.wf_basic(),
            other.wf_basic(),
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + Self::size(final(self).ptr()@.metadata) <= other.ptr()@.addr
                || other.ptr()@.addr + OtherPointsToPerm::size(other.ptr()@.metadata) <= final(self).ptr()@.addr,
    ;
}

/// Defines the typed data tracked by a `PointsTo` permission
/// to a single, possibly-valid value of type `Self::A`,
/// along with well-formedness conditions and the conditions that preserve them.
pub trait PTTypedValue: PTPhys {
    /// The (possibly-valid) typed value that this permission tracks.
    spec fn typed_value(self) -> TypedValue<Self::A>;

    /// The abstract bytes of the memory that this permission tracks.
    spec fn bytes(self) -> Seq<AbstractByte>;

    /// Well-formedness: the pointer-level conditions (`wf_basic`),
    /// the alignment requirement for this permission type,
    /// and validity constraints (`valid_value`).
    open spec fn wf(self) -> bool {
        &&& self.wf_basic()
        &&& Self::satisfies_alignment(self.ptr()@.addr)
        &&& self.valid_value()
    }

    /// Validity constraints on the typed value:
    /// if it is valid, the bytes decode to it,
    /// and it satisfies `additional_validity_constraints`.
    open spec fn valid_value(self) -> bool {
        self.typed_value().is_valid() ==> {
            &&& abs_decode(self.bytes(), self.typed_value().value_ref())
            &&& Self::additional_validity_constraints(self.typed_value().value_ref(), self.ptr()@.metadata)
        }
    }

    /// Validity constraints on a valid `value`, beyond its bytes decoding to it,
    /// given the pointer metadata `metadata`.
    /// For a slice, this means the slice has `metadata` elements;
    /// for a `Sized` type, it is always `true`.
    spec fn additional_validity_constraints(value: &Self::A, metadata: Metadata<Self::A>) -> bool;

    /// Whether `addr` satisfies this permission type's alignment requirement:
    /// alignment to `Self::A` for `PointsTo`,
    /// and no requirement (`true`) for `PointsToUnaligned`.
    spec fn satisfies_alignment(addr: usize) -> bool;

    /// Specifies conditions which must hold on the bytes and typed value if the permission is well-formed.
    proof fn bytes_decode(&self)
        requires
            self.wf(),
        ensures
            self.bytes().len() == Self::size(self.ptr()@.metadata),
            self.typed_value().is_valid() ==> {
                &&& abs_decode(self.bytes(), self.typed_value().value_ref())
                &&& Self::additional_validity_constraints(self.typed_value().value_ref(), self.ptr()@.metadata)
            },
    ;

    /// A well-formed permission's address satisfies the alignment requirement.
    proof fn satisfies_alignment_of_wf(&self)
        requires
            self.wf(),
        ensures
            Self::satisfies_alignment(self.ptr()@.addr),
    ;

    /// Well-formedness implies the pointer-level well-formedness.
    proof fn lemma_wf_basic(&self)
        requires
            self.wf(),
        ensures
            self.wf_basic(),
    ;

    /// Invariants which must hold between `old` and `new` to preserve well-formedness (see `stays_wf`).
    open spec fn ptrs_len_same_valid_value(old: Self, new: Self) -> bool {
        &&& Self::ptrs_len_same(old, new)
        &&& new.valid_value()
    }

    /// Two well-formed permissions with the same pointer satisfy `ptrs_len_same_valid_value`.
    broadcast proof fn lemma_ptrs_len_same_valid_value(old: Self, new: Self)
        requires
            old.wf(),
            new.wf(),
            new.ptr() == old.ptr(),
        ensures
            #[trigger] Self::ptrs_len_same_valid_value(old, new),
    ;

    /// If `old` is well-formed and `new` satisfies `ptrs_len_same_valid_value`,
    /// then `new` is well-formed.
    proof fn stays_wf(old: Self, new: Self)
        requires
            old.wf(),
            Self::ptrs_len_same_valid_value(old, new),
        ensures
            new.wf(),
    ;
}

/// Defines constructors and conversions
/// for a `PointsTo` permission to a single, possibly-valid value of type `Self::A`.
pub trait PTValueOps: PTTypedValue + PTProperties {
    /// Creates an empty permission to a zero-sized region,
    /// at any non-null, in-bounds pointer that satisfies the alignment requirement.
    proof fn zero_sized(ptr: *mut Self::A) -> (tracked out: Self)
        requires
            ptr@.addr != 0,
            ptr_addr_in_bounds(ptr),
            Self::size(ptr@.metadata) == 0,
            Self::satisfies_alignment(ptr@.addr),
        ensures
            out.ptr() == ptr,
            out.bytes().len() == 0,
            out.typed_value().is_empty(),
            out.wf(),
    {
        // PointsToUntyped::zero_sized needs a pointer to a zero-sized type.
        let tracked pt_untyped = PointsToUntyped::zero_sized(ptr_mut_from_data::<()>(
            PtrData { addr: ptr@.addr, provenance: ptr@.provenance, metadata: () },
        ));
        Self::from_untyped(pt_untyped, ptr@.metadata)
    }

    /// Borrows the typed value.
    proof fn borrow_typed_value(tracked &self) -> tracked &TypedValue<Self::A>
        requires
            self.wf(),
        returns
            self.typed_value(),
    ;

    /// Moves the typed value out, leaving `self` empty.
    proof fn take_typed_value(tracked &mut self) -> (tracked v: TypedValue<Self::A>)
        requires
            self.wf(),
        ensures
            v == old(self).typed_value(),
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value().is_empty(),
            final(self).wf(),
    ;

    /// Replaces the typed value with `v`.
    /// If `v` is valid, the bytes must decode to its value and the metadata must match it.
    proof fn put_typed_value(tracked &mut self, tracked v: TypedValue<Self::A>)
        requires
            self.wf(),
            v.is_valid() ==> {
                &&& abs_decode(self.bytes(), v.value_ref())
                &&& Self::additional_validity_constraints(v.value_ref(), self.ptr()@.metadata)
            },
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value() == v,
            final(self).wf(),
    ;

    /// Borrows the value, which must be valid.
    proof fn borrow(tracked &self) -> tracked &Self::A
        requires
            self.wf(),
            self.typed_value().is_valid(),
        returns
            self.typed_value().value_ref(),
    {
        match self.borrow_typed_value() {
            TypedValue::Valid(b) => b,
            TypedValue::Empty => proof_from_false(),
        }
    }

    /// Splits the permission into an untyped permission to the same bytes and the typed value.
    proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, v): (PointsToUntyped, TypedValue<Self::A>))
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: Self::size(self.ptr()@.metadata) as usize,
            }),
            pt_untyped.bytes() == self.bytes(),
            pt_untyped.wf(),
            v == self.typed_value(),
    ;

    /// Creates a permission from an untyped permission, a typed value and pointer metadata.
    /// The inverse of `into_untyped_with_typed_value`.
    /// If `typed_value` is valid, the bytes must decode to its value and the metadata must match it.
    proof fn from_untyped_with_typed_value(
        tracked pt_untyped: PointsToUntyped,
        tracked typed_value: TypedValue<Self::A>,
        metadata: Metadata<Self::A>,
    ) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            pt_untyped.len() == Self::size(metadata),
            Self::satisfies_alignment(pt_untyped.ptr()@.addr),
            typed_value.is_valid() ==> {
                &&& abs_decode(pt_untyped.bytes(), typed_value.value_ref())
                &&& Self::additional_validity_constraints(typed_value.value_ref(), metadata)
            },
        ensures
            out.ptr() == ptr_mut_from_data::<Self::A>(PtrData {
                addr: pt_untyped.ptr()@.addr,
                provenance: pt_untyped.ptr()@.provenance,
                metadata,
            }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value() == typed_value,
            out.wf(),
    ;

    /// Converts to an untyped permission for the same bytes,
    /// dropping the typed value, if any.
    proof fn into_untyped(tracked self) -> (tracked pt_untyped: PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: Self::size(self.ptr()@.metadata) as usize,
            }),
            pt_untyped.bytes() == self.bytes(),
            pt_untyped.wf(),
    {
        let tracked (pt_untyped, _) = self.into_untyped_with_typed_value();
        pt_untyped
    }

    /// Borrows the underlying untyped permission.
    proof fn as_untyped(tracked &self) -> (tracked pt_untyped: &PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: Self::size(self.ptr()@.metadata) as usize,
            }),
            pt_untyped.bytes() == self.bytes(),
            pt_untyped.wf(),
    ;

    /// Mutably borrows the underlying untyped permission.
    /// The typed value, if any, is dropped (call `take_typed_value` first to keep it).
    ///
    /// `final(self)` is empty
    /// and has the final untyped permission's bytes, address, and provenance,
    /// but keeps its original pointer metadata (since this is a separate field).
    /// If the final untyped permission has the same pointers and length as the original,
    /// `self` is well-formed afterwards
    /// (including that the metadata still defines the size of bytes).
    proof fn as_untyped_mut(tracked &mut self) -> (tracked pt_untyped: &mut PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(PtrData {
                addr: old(self).ptr()@.addr,
                provenance: old(self).ptr()@.provenance,
                metadata: Self::size(old(self).ptr()@.metadata) as usize,
            }),
            pt_untyped.bytes() == old(self).bytes(),
            pt_untyped.wf(),
            final(self).ptr() == ptr_mut_from_data::<Self::A>(PtrData {
                addr: final(pt_untyped).ptr()@.addr,
                provenance: final(pt_untyped).ptr()@.provenance,
                metadata: old(self).ptr()@.metadata,
            }),
            final(self).bytes() == final(pt_untyped).bytes(),
            final(self).typed_value().is_empty(),
            PointsToUntyped::ptrs_len_same(*pt_untyped, *final(pt_untyped)) ==> final(self).wf(),
    ;

    /// Creates an empty permission to `pt_untyped`'s bytes, with the given pointer metadata.
    proof fn from_untyped(tracked pt_untyped: PointsToUntyped, metadata: Metadata<Self::A>) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            pt_untyped.len() == Self::size(metadata),
            Self::satisfies_alignment(pt_untyped.ptr()@.addr),
        ensures
            out.ptr() == ptr_mut_from_data::<Self::A>(PtrData {
                addr: pt_untyped.ptr()@.addr,
                provenance: pt_untyped.ptr()@.provenance,
                metadata,
            }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value().is_empty(),
            out.wf(),
    {
        Self::from_untyped_with_typed_value(pt_untyped, TypedValue::Empty, metadata)
    }
}

/// Restricts `PTValueOps` to permissions whose value type is `Sized`,
/// so its value can be moved in and out of the permission.
/// `PointsTo<T>` permissions are the element permissions of a typed `SeqPointsTo`.
pub trait PTSizedValue: PTValueOps<A: Sized> {
    /// The alignment requirement is preserved by offsets that are multiples of the size.
    proof fn lemma_satisfies_alignment_offset(addr: usize, i: nat)
        requires
            Self::satisfies_alignment(addr),
            addr + i * Self::size(()) <= usize::MAX,
        ensures
            Self::satisfies_alignment((addr + i * Self::size(())) as usize),
    ;

    /// A `Sized` value has no additional validity constraints.
    proof fn lemma_additional_validity_constraints(value: &Self::A)
        ensures
            Self::additional_validity_constraints(value, ()),
    ;

    /// Moves the value out, leaving `self` empty.
    proof fn take(tracked &mut self) -> (tracked v: Self::A)
        requires
            self.wf(),
            self.typed_value().is_valid(),
        ensures
            v == old(self).typed_value().value(),
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value().is_empty(),
            final(self).wf(),
    {
        match self.take_typed_value() {
            TypedValue::Valid(b) => b.get(),
            TypedValue::Empty => proof_from_false(),
        }
    }

    /// Puts `v` in the permission. The bytes must decode to `v`.
    proof fn put(tracked &mut self, tracked v: Self::A)
        requires
            self.wf(),
            abs_decode(self.bytes(), &v),
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value().is_valid(),
            final(self).typed_value().value() == v,
            final(self).wf(),
    {
        Self::lemma_additional_validity_constraints(&v);
        self.put_typed_value(TypedValue::Valid(Tracked(v)));
    }

    /// Copies `*v` into the permission. The bytes must decode to `*v`.
    proof fn copy(tracked &mut self, tracked v: &Self::A) where Self::A: Copy
        requires
            self.wf(),
            abs_decode(self.bytes(), v),
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value().is_valid(),
            final(self).typed_value().value() == *v,
            final(self).wf(),
    {
        self.put(*v);
    }

    /// Copies `*v` into the permission as its typed value.
    /// If `*v` is valid, the bytes must decode to its value.
    proof fn copy_typed_value(tracked &mut self, tracked v: &TypedValue<Self::A>) where Self::A: Copy
        requires
            self.wf(),
            v.is_valid() ==> abs_decode(self.bytes(), &v.value()),
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value() == *v,
            final(self).wf(),
    {
        if v.is_valid() {
            Self::lemma_additional_validity_constraints(&v.value());
        }
        self.put_typed_value(v.tracked_copy());
    }

    /// Creates a valid permission holding `value` from an untyped permission
    /// whose bytes decode to `value`.
    proof fn from_untyped_with_value(tracked pt_untyped: PointsToUntyped, tracked value: Self::A) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            pt_untyped.len() == Self::size(()),
            Self::satisfies_alignment(pt_untyped.ptr()@.addr),
            abs_decode(pt_untyped.bytes(), &value),
        ensures
            out.ptr() == ptr_mut_from_data::<Self::A>(PtrData {
                addr: pt_untyped.ptr()@.addr,
                provenance: pt_untyped.ptr()@.provenance,
                metadata: (),
            }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value().is_valid(),
            out.typed_value().value() == value,
            out.wf(),
    {
        Self::lemma_additional_validity_constraints(&value);
        Self::from_untyped_with_typed_value(pt_untyped, TypedValue::Valid(Tracked(value)), ())
    }
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
    open spec fn size(metadata: ()) -> nat {
        1
    }

    /// A `PointsToByte` is always well-formed.
    open spec fn wf_basic(self) -> bool {
        true
    }

    /// If the pointer stays the same, `old` and `new` are permissions to the same memory.
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        new.ptr() == old.ptr()
    }

    /// Trivial, since a `PointsToByte` is always well-formed.
    proof fn stays_wf_basic(old: Self, new: Self) {
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
            final(self).ptr()@.addr + size_of::<u8>() <= other.ptr()@.addr
                || other.ptr()@.addr + size_of::<u8>() <= final(self).ptr()@.addr,
    {
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
#[verifier::accept_recursive_types(T)]
pub tracked struct SeqPointsTo<T, P: PTProperties> {
    seq_pt: Seq<P>,
    ptr: Ghost<*mut [T]>,
}

impl<T, P: PTProperties> PTPhysSealed for SeqPointsTo<T, P> {}

impl<T, P: PTProperties<A = T>> PTPhys for SeqPointsTo<T, P> {
    type A = [T];

    /// The pointer to the whole region; its metadata is the number of elements.
    closed spec fn ptr(self) -> *mut [T] {
        self.ptr@
    }

    /// The size of the pointed-to region is given by the length of the sequence (the pointer's metadata)
    /// times the size of the permission type in the sequence.
    ///
    /// Note that since this impl block restricts `P` to permissions satisfying `PTProperties`
    /// with the associated type set to `T` (which is implicitly `Sized`),
    /// `P` is a permission whose pointer has `()` metadata.
    open spec fn size(metadata: usize) -> nat {
        metadata as nat * P::size(())
    }

    open spec fn wf_basic(self) -> bool {
        // The pointer's metadata is the number of permissions
        &&& self.ptr()@.metadata == self.len()
        // Defining the provenance and address for the individual permissions
        &&& forall|i|
            #![trigger self[i].ptr()@.provenance]
            #![trigger self[i].ptr()@.addr]
            #![trigger self[i].wf_basic()]
            0 <= i < self.len() ==> {
                &&& self[i].ptr()@.provenance == self.ptr()@.provenance
                &&& self[i].ptr()@.addr == self.ptr()@.addr + i * P::size(())
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

    /// `new` has the same pointer and length as `old`, and each element of `new` keeps the
    /// corresponding element of `old`'s pointer and satisfies its `ptrs_len_same`.
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& new.len() == old.len()
        &&& forall|i: int|
            #![trigger new[i]]
            0 <= i < new.len() ==> P::ptrs_len_same(old[i], new[i]) && new[i].ptr() == old[i].ptr()
    }

    proof fn stays_wf_basic(old: Self, new: Self) {
        assert forall|i: int| 0 <= i < new.len() implies #[trigger] new[i].wf_basic() by {
            P::stays_wf_basic(old[i], new[i]);
        }
    }
}

impl<T, P: PTProperties<A = T>> SeqPointsTo<T, P> {
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

    /// Borrows the sequence of permissions.
    pub proof fn tracked_seq_pt(tracked &self) -> tracked &Seq<P>
        returns
            self.seq_pt(),
    {
        &self.seq_pt
    }

    /// Mutably borrows the sequence of permissions, leaving the pointer unchanged.
    /// If the final permissions keep their original pointers and lengths,
    /// `self` satisfies `wf_basic` afterwards.
    pub proof fn tracked_seq_pt_mut(tracked &mut self) -> (tracked ret: &mut Seq<P>)
        ensures
            *ret == old(self).seq_pt(),
            final(self).seq_pt() == *final(ret),
            final(self).ptr() == old(self).ptr(),
            old(self).wf_basic() && Self::ptrs_len_same(*old(self), *final(self)) ==> final(self).wf_basic(),
    {
        let old_self = *self;
        let self_ref = self;
        let tracked ret = &mut self.seq_pt;
        if old_self.wf_basic() && Self::ptrs_len_same(old_self, *final(self_ref)) {
            Self::stays_wf_basic(old_self, *final(self_ref));
        }
        ret
    }

    /// Consumes this `SeqPointsTo`, returning the underlying `Seq<P>`.
    pub proof fn into_seq(tracked self) -> (tracked perms: Seq<P>)
        returns
            self.seq_pt(),
    {
        self.seq_pt
    }

    /// A mutably borrowed `Seq<P>` acts as a mutably borrowed `SeqPointsTo<T, P>` with the given pointer.
    pub axiom fn from_seq_mut<'a>(tracked s: &'a mut Seq<P>, ptr: *mut [T]) -> (tracked out: &'a mut Self)
        ensures
            out.seq_pt() == *old(s),
            out.ptr() == ptr,
            *final(s) == final(out).seq_pt(),
    ;
}

/// Permission to access an (untyped) contiguous sequence of bytes in memory.
/// Internally represented as a sequence of `PointsToByte` permissions,
/// along with a `*mut [u8]` pointer to the region of bytes.
pub type PointsToUntyped = SeqPointsTo<u8, PointsToByte>;

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
        self.wf_basic()
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
            Self::ptrs_len_same(*joined, *final(joined)) ==> {
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

    /// If valid, a reference to the value; otherwise meaningless.
    pub open spec fn value_ref(&self) -> &T
        recommends
            self.is_valid(),
    {
        &*self->0
    }

    /// Borrows a value as a valid typed value.
    pub proof fn valid_ref<'a>(tracked v: &'a T) -> (tracked out: &'a Self)
        ensures
            out.is_valid(),
            out.value_ref() == v,
    {
        let tracked t = tracked_ref(v);
        shr_ref_struct_wrap(t, &TypedValue::Valid(*t), "Valid", "0")
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
    /// A sequence of borrows of typed values acts as one borrow of a slice typed value.
    /// If any element is empty, the slice is empty.
    pub axiom fn from_elems_ref<'a>(tracked elems: Seq<&'a TypedValue<T>>)
        -> (tracked out: &'a TypedValue<[T]>)
        ensures
            // Valid with the elements' values if every element is valid
            // (a zero-length Seq counts as valid); otherwise empty.
            (forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid()) ==> {
                &&& out.is_valid()
                &&& out.value_ref()@ == Seq::new(elems.len(), |i: int| elems[i].value())
            },
            !(forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid()) ==> out.is_empty(),
    ;

    /// A sequence of mutable borrows of typed values acts as one mutable borrow of a slice typed value.
    /// If any element is empty, the slice starts empty.
    pub axiom fn from_elems_mut<'a>(tracked elems: Seq<&'a mut TypedValue<T>>)
        -> (tracked out: &'a mut TypedValue<[T]>)
        ensures
            // Initially: valid with the elements' values if every element is valid
            // (a zero-length Seq counts as valid); otherwise empty.
            (forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid()) ==> {
                &&& out.is_valid()
                &&& out.value_ref()@ == Seq::new(elems.len(), |i: int| elems[i].value())
            },
            !(forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid()) ==> out.is_empty(),
            // Finally: a valid slice of the same length is distributed back to the elements;
            // anything else leaves every element empty.
            final(out).is_valid() && final(out).value_ref()@.len() == elems.len() ==> forall|i: int|
                #![trigger elems[i]]
                0 <= i < elems.len() ==> {
                    &&& final(elems[i]).is_valid()
                    &&& final(elems[i]).value() == final(out).value_ref()@[i]
                },
            !(final(out).is_valid() && final(out).value_ref()@.len() == elems.len()) ==> forall|i: int|
                #![trigger elems[i]]
                0 <= i < elems.len() ==> final(elems[i]).is_empty(),
    ;
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
impl<T: ?Sized> View for PointsToUnaligned<T> where PointsToUnaligned<T>: PTTypedValue<A = T> {
    type V = PointsToData<T>;

    open spec fn view(&self) -> Self::V {
        PointsToData {
            ptr: self.ptr(),
            value: <Self as PTTypedValue>::typed_value(*self),
            bytes: <Self as PTTypedValue>::bytes(*self),
        }
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
    // This is implemented by making `PTTypedValue::wf` on `self` include `wf_basic`,
    // which includes `self.pt_untyped().wf()`.
    pub proof fn tracked_pt_untyped(tracked &self) -> tracked &PointsToUntyped
        returns
            self.pt_untyped(),
    {
        &self.pt_untyped
    }

    /// Returns a tracked reference to the typed value.
    pub proof fn tracked_typed_value(tracked &self) -> tracked &TypedValue<T>
        returns
            self.typed_value(),
    {
        &self.val
    }

    /// Splits the permission into an untyped permission to the same bytes and the typed value.
    /// It says nothing about `wf()`.
    pub proof fn into_raw_parts(tracked self) -> (tracked (pt_untyped, typed_value): (PointsToUntyped, TypedValue<T>))
        ensures
            pt_untyped == self.pt_untyped(),
            typed_value == self.typed_value(),
    {
        (self.pt_untyped, self.val)
    }

    /// Creates a permission from an untyped permission, a typed value and pointer metadata.
    /// The inverse of `into_raw_parts`.
    /// It says nothing about `wf()`: callers prove it from the parts.
    pub proof fn from_raw_parts(
        tracked pt_untyped: PointsToUntyped,
        tracked typed_value: TypedValue<T>,
        metadata: Metadata<T>,
    ) -> (tracked out: Self)
        ensures
            out.pt_untyped() == pt_untyped,
            out.typed_value() == typed_value,
            out.metadata() == metadata,
    {
        PointsToUnaligned { val: typed_value, pt_untyped, metadata: Ghost(metadata) }
    }

    /// Mutably borrows the untyped bytes and the typed value separately
    /// (the inverse of `from_raw_parts_mut`).
    /// The metadata is unchanged.
    pub proof fn as_raw_parts_mut(tracked &mut self)
        -> (tracked (pt_untyped, typed_value): (&mut PointsToUntyped, &mut TypedValue<T>))
        ensures
            *pt_untyped == old(self).pt_untyped(),
            *typed_value == old(self).typed_value(),
            final(self).pt_untyped() == *final(pt_untyped),
            final(self).typed_value() == *final(typed_value),
            final(self).metadata() == old(self).metadata(),
    {
        (&mut self.pt_untyped, &mut self.val)
    }

    /// Converts a borrowed untyped permission and a borrowed typed value, with the given pointer metadata,
    /// into one borrowed `PointsToUnaligned` permission.
    /// This is the borrowed version of building the permission from its parts.
    /// It says nothing about `wf()`: callers prove it from the parts.
    pub axiom fn from_raw_parts_ref<'a>(
        tracked pt_untyped: &'a PointsToUntyped,
        tracked typed_value: &'a TypedValue<T>,
        metadata: Metadata<T>,
    ) -> (tracked out: &'a Self)
        ensures
            out.pt_untyped() == *pt_untyped,
            out.typed_value() == *typed_value,
            out.metadata() == metadata,
    ;

    /// Converts a mutable borrow of an untyped permission and a mutable borrow of a typed value, with the given pointer metadata,
    /// into one mutably borrowed `PointsToUnaligned` permission.
    /// The borrowed parts' final values are the final permission's parts.
    /// It says nothing about `wf()`: callers prove it from the parts.
    pub axiom fn from_raw_parts_mut<'a>(
        tracked pt_untyped: &'a mut PointsToUntyped,
        tracked typed_value: &'a mut TypedValue<T>,
        metadata: Metadata<T>,
    ) -> (tracked out: &'a mut Self)
        ensures
            out.pt_untyped() == *old(pt_untyped),
            out.typed_value() == *old(typed_value),
            out.metadata() == metadata,
            *final(pt_untyped) == final(out).pt_untyped(),
            *final(typed_value) == final(out).typed_value(),
    ;
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
}

impl<T: ?Sized> PTPhysSealed for PointsToUnaligned<T> {}

impl<T> PTPhys for PointsToUnaligned<T> {
    type A = T;

    /// Builds the `*mut T` from the underlying untyped pointer's address and provenance
    /// and the stored metadata.
    open spec fn ptr(self) -> *mut T {
        ptr_mut_from_data::<T>(
            PtrData {
                addr: self.pt_untyped().ptr()@.addr,
                provenance: self.pt_untyped().ptr()@.provenance,
                metadata: self.metadata(),
            },
        )
    }

    /// The size of the pointed-to region is the size of `T`.
    open spec fn size(metadata: ()) -> nat {
        size_of::<T>()
    }

    /// A `PointsToUnaligned` is well-formed at the pointer level
    /// if its memory region is `size_of::<T>()` bytes,
    /// and the underlying `PointsToUntyped` is well-formed.
    open spec fn wf_basic(self) -> bool {
        &&& self.pt_untyped().wf()
        &&& self.pt_untyped().len() == Self::size(self.ptr()@.metadata)
    }

    /// `new` has the same pointer
    /// and the same underlying `PointsToUntyped` pointers and length as `old`.
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUntyped::ptrs_len_same(old.pt_untyped(), new.pt_untyped())
    }

    proof fn stays_wf_basic(old: Self, new: Self) {
    }
}

impl<T> PTPhys for PointsToUnaligned<[T]> {
    type A = [T];

    /// Builds the `*mut [T]` from the underlying untyped pointer's address and provenance
    /// and the stored metadata.
    open spec fn ptr(self) -> *mut [T] {
        ptr_mut_from_data::<[T]>(
            PtrData {
                addr: self.pt_untyped().ptr()@.addr,
                provenance: self.pt_untyped().ptr()@.provenance,
                metadata: self.metadata(),
            },
        )
    }

    /// The size of the pointed-to region is the number of elements times the size of `T`.
    open spec fn size(metadata: usize) -> nat {
        metadata as nat * size_of::<T>()
    }

    /// A `PointsToUnaligned<[T]>` is well-formed at the pointer level
    /// if its memory region is `Self::size(self.ptr()@.metadata)` bytes,
    /// and the underlying `PointsToUntyped` is well-formed.
    open spec fn wf_basic(self) -> bool {
        &&& self.pt_untyped().wf()
        &&& self.pt_untyped().len() == Self::size(self.ptr()@.metadata)
    }

    /// `new` has the same pointer
    /// and the same underlying `PointsToUntyped` pointers and length as `old`.
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUntyped::ptrs_len_same(old.pt_untyped(), new.pt_untyped())
    }

    proof fn stays_wf_basic(old: Self, new: Self) {
    }
}

impl<T> PTTypedValue for PointsToUnaligned<T> {
    /// The inherent `typed_value` accessor.
    open spec fn typed_value(self) -> TypedValue<T> {
        PointsToUnaligned::<T>::typed_value(self)
    }

    /// The underlying untyped permission's bytes.
    open spec fn bytes(self) -> Seq<AbstractByte> {
        self.pt_untyped().bytes()
    }

    /// Always `true`: a `Sized` value has no additional validity constraints.
    open spec fn additional_validity_constraints(value: &T, metadata: ()) -> bool {
        true
    }

    /// Always `true`: a `PointsToUnaligned` has no alignment requirement.
    open spec fn satisfies_alignment(addr: usize) -> bool {
        true
    }

    proof fn bytes_decode(&self) {
        // This assert is only there so Verus unfolds the inherited default `wf` here,
        // which it otherwise doesn't do at `PointsToUnaligned<T>`.
        assert(self.wf());
    }

    proof fn satisfies_alignment_of_wf(&self) {
    }

    proof fn lemma_wf_basic(&self) {
    }

    // ptrs_len_same_valid_value: the trait's default body.

    /// From `PointsToUntyped::lemma_ptrs_len_same_untyped` on the underlying permissions.
    proof fn lemma_ptrs_len_same_valid_value(old: Self, new: Self) {
        PointsToUntyped::lemma_ptrs_len_same_untyped(old.pt_untyped(), new.pt_untyped());
        // As in `bytes_decode`, this assert unfolds the default `ptrs_len_same_valid_value`.
        assert(Self::ptrs_len_same_valid_value(old, new));
    }

    /// From `PointsToUntyped::stays_wf` on the underlying permissions.
    proof fn stays_wf(old: Self, new: Self) {
        PointsToUntyped::stays_wf(old.pt_untyped(), new.pt_untyped());
    }
}

impl<T> PTTypedValue for PointsToUnaligned<[T]> {
    /// The inherent `typed_value` accessor.
    open spec fn typed_value(self) -> TypedValue<[T]> {
        PointsToUnaligned::<[T]>::typed_value(self)
    }

    /// The underlying untyped permission's bytes.
    open spec fn bytes(self) -> Seq<AbstractByte> {
        self.pt_untyped().bytes()
    }

    /// The slice has `metadata` elements.
    open spec fn additional_validity_constraints(value: &[T], metadata: usize) -> bool {
        value@.len() == metadata
    }

    /// Always `true`: a `PointsToUnaligned` has no alignment requirement.
    open spec fn satisfies_alignment(addr: usize) -> bool {
        true
    }

    proof fn bytes_decode(&self) {
        // As in `PointsToUnaligned<T>`'s `bytes_decode`,
        // this assert unfolds the inherited default `wf`.
        assert(self.wf());
    }

    proof fn satisfies_alignment_of_wf(&self) {
    }

    proof fn lemma_wf_basic(&self) {
        // As in `bytes_decode`, this assert unfolds the default `wf`.
        assert(self.wf());
    }

    // ptrs_len_same_valid_value: the trait's default body.

    /// From `PointsToUntyped::lemma_ptrs_len_same_untyped` on the underlying permissions.
    proof fn lemma_ptrs_len_same_valid_value(old: Self, new: Self) {
        // As in `bytes_decode`, these asserts unfold the default `wf` and `ptrs_len_same_valid_value`.
        assert(old.wf() && new.wf());
        PointsToUntyped::lemma_ptrs_len_same_untyped(old.pt_untyped(), new.pt_untyped());
        assert(Self::ptrs_len_same_valid_value(old, new));
    }

    /// From `PointsToUntyped::stays_wf` on the underlying permissions.
    proof fn stays_wf(old: Self, new: Self) {
        // As in `bytes_decode`, this assert unfolds the default `wf` and `ptrs_len_same_valid_value`.
        assert(old.wf() && Self::ptrs_len_same_valid_value(old, new));
        PointsToUntyped::stays_wf(old.pt_untyped(), new.pt_untyped());
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
impl<T: ?Sized> View for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    type V = PointsToData<T>;

    open spec fn view(&self) -> Self::V {
        PointsToData {
            ptr: self.ptr(),
            value: <Self as PTTypedValue>::typed_value(*self),
            bytes: <Self as PTTypedValue>::bytes(*self),
        }
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

    /// A mutably borrowed `PointsToUnaligned<T>` acts as a mutably borrowed `PointsTo<T>`
    /// (the `&mut` counterpart of the `shr_ref_struct_wrap` in `as_aligned`).
    pub axiom fn from_unaligned_mut<'a>(tracked u: &'a mut PointsToUnaligned<T>)
        -> (tracked out: &'a mut Self)
        ensures
            out.pt_unaligned() == *old(u),
            *final(u) == final(out).pt_unaligned(),
    ;
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

    /// This takes a mutable borrow of the `T` from a mutable borrow of a `PointsTo<T>`.
    /// The pointer of this borrow matches the permission's pointer.
    ///
    /// Writing through the reference updates both the value and the underlying bytes,
    /// so `final(self)` is well-formed with bytes that decode to the final value.
    // This is an axiom because the bytes live in separate ghost state from the `TypedValue<T>`,
    // so they can't be updated through a borrow of the value alone.
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

impl<T: ?Sized> PTPhysSealed for PointsTo<T> {}

impl<T: ?Sized> PTPhys for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    type A = T;

    /// Delegates to the underlying `PointsToUnaligned`'s pointer.
    open spec fn ptr(self) -> *mut T {
        self.pt_unaligned().ptr()
    }

    /// Delegates to the underlying `PointsToUnaligned`'s size.
    open spec fn size(metadata: Metadata<T>) -> nat {
        <PointsToUnaligned<T> as PTPhys>::size(metadata)
    }

    /// Delegates to the underlying `PointsToUnaligned`'s `wf_basic`.
    /// This does not capture all well-formedness conditions:
    /// pointer alignment is specified in `PTTypedValue::wf`.
    open spec fn wf_basic(self) -> bool {
        self.pt_unaligned().wf_basic()
    }

    /// `new` has the same pointer as `old`,
    /// and they satisfy the `PointsToUnaligned` requirements
    /// for preserving pointer-level well-formed-ness.
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& <PointsToUnaligned<T> as PTPhys>::ptrs_len_same(old.pt_unaligned(), new.pt_unaligned())
    }

    /// Delegates to `PointsToUnaligned`'s `stays_wf_basic`.
    proof fn stays_wf_basic(old: Self, new: Self) {
        <PointsToUnaligned<T> as PTPhys>::stays_wf_basic(old.pt_unaligned(), new.pt_unaligned());
    }
}

impl<T: ?Sized> PTTypedValue for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    /// Delegates to the underlying `PointsToUnaligned`'s typed value.
    open spec fn typed_value(self) -> TypedValue<T> {
        <PointsToUnaligned<T> as PTTypedValue>::typed_value(self.pt_unaligned())
    }

    /// Delegates to the underlying `PointsToUnaligned`'s bytes.
    open spec fn bytes(self) -> Seq<AbstractByte> {
        <PointsToUnaligned<T> as PTTypedValue>::bytes(self.pt_unaligned())
    }

    /// A `PointsTo` is well-formed if its pointer is aligned to `T`,
    /// and the underlying `PointsToUnaligned` is well-formed.
    open spec fn wf(self) -> bool {
        &&& self.pt_unaligned().wf()
        &&& Self::satisfies_alignment(self.ptr()@.addr)
    }

    /// Delegates to `PointsToUnaligned::additional_validity_constraints`.
    open spec fn additional_validity_constraints(value: &T, metadata: Metadata<T>) -> bool {
        <PointsToUnaligned<T> as PTTypedValue>::additional_validity_constraints(value, metadata)
    }

    /// The pointer's address is aligned to `T`.
    /// Includes the (trivial) `PointsToUnaligned` requirement
    /// to satisfy generic preconditions defined over the trait `PTValueOps`.
    open spec fn satisfies_alignment(addr: usize) -> bool {
        &&& <PointsToUnaligned<T> as PTTypedValue>::satisfies_alignment(addr)
        &&& addr as nat % spec_align_of_val::<T>(arbitrary()) == 0
    }

    proof fn bytes_decode(&self) {
        self.pt_unaligned().bytes_decode();
    }

    proof fn satisfies_alignment_of_wf(&self) {
    }

    proof fn lemma_wf_basic(&self) {
        self.pt_unaligned().lemma_wf_basic();
    }

    /// Delegates to the underlying `PointsToUnaligned`.
    open spec fn valid_value(self) -> bool {
        <PointsToUnaligned<T> as PTTypedValue>::valid_value(self.pt_unaligned())
    }

    /// `new` has the same pointer as `old`,
    /// and they satisfy the `PointsToUnaligned` requirements
    /// for preserving well-formed-ness.
    open spec fn ptrs_len_same_valid_value(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& <PointsToUnaligned<T> as PTTypedValue>::ptrs_len_same_valid_value(old.pt_unaligned(), new.pt_unaligned())
    }

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn lemma_ptrs_len_same_valid_value(old: Self, new: Self) {
        <PointsToUnaligned<T> as PTTypedValue>::lemma_ptrs_len_same_valid_value(old.pt_unaligned(), new.pt_unaligned());
    }

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn stays_wf(old: Self, new: Self) {
        <PointsToUnaligned<T> as PTTypedValue>::stays_wf(old.pt_unaligned(), new.pt_unaligned());
    }
}

} // verus!
