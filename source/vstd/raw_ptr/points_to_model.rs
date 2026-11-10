#![allow(unused_imports)]

use super::super::group_vstd_default;
use super::super::layout::{self, *};
#[cfg(verus_keep_ghost)]
use super::super::modes::tracked_ref;
use super::super::prelude::*;
#[cfg(verus_keep_ghost)]
use super::super::type_representation::*;
use super::abstract_bytes::*;
use super::ptr_model;
use super::ptr_model::*;

verus! {

broadcast use {
    ptr_model::group_raw_ptr_axioms,
    layout::group_layout_axioms,
    super::super::seq::group_seq_axioms,
};
// A private seal trait to prevent `PTPhys` from being implemented outside of vstd.

pub(crate) trait PTPhysSealed {

}

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

    /// Ensures that the permission actually holds a `PointsToByte` permission 
    /// for every byte in its memory range.
    proof fn borrow_byte(tracked &self, addr: int) -> (tracked b: &PointsToByte)
        requires
            self.wf_basic(),
            self.ptr()@.addr <= addr < self.ptr()@.addr + Self::size(self.ptr()@.metadata),
        ensures
            b.byte_ptr()@.addr == addr,
            b.byte_ptr()@.provenance == self.ptr()@.provenance,
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
                <= self.ptr()@.provenance.unwrap().start_addr()
                + self.ptr()@.provenance.unwrap().alloc_len(),
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
                || other.ptr()@.addr + OtherPointsToPerm::size(other.ptr()@.metadata)
                <= final(self).ptr()@.addr,
    ;
}

/// Permission to access a byte of memory.
#[verifier::external_body]
pub tracked struct PointsToByte {
    no_copy: NoCopy,
}

impl PTPhysSealed for PointsToByte {

}

impl PTPhys for PointsToByte {
    type A = u8;

    /// The inherent `byte_ptr` accessor.
    open spec fn ptr(self) -> *mut u8 {
        self.byte_ptr()
    }

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

    // The only address in range is this permission's own.
    proof fn borrow_byte(tracked &self, addr: int) -> (tracked b: &PointsToByte) {
        self
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
    // If `self`'s address is in `other`'s range,
    // `other`'s byte at that address contradicts `is_disjoint_byte`.
    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    ) {
        let addr = self.ptr()@.addr as int;
        if other.ptr()@.addr <= addr < other.ptr()@.addr + OtherPointsToPerm::size(
            other.ptr()@.metadata,
        ) {
            let tracked b = other.borrow_byte(addr);
            self.is_disjoint_byte(b);
        }
    }
}

impl PointsToByte {
    /// The pointer to the single byte of memory this permission is for (its `PTPhys::ptr`).
    // An inherent fn, not only the `PTPhys` one,
    // so that `PTPhys::borrow_byte`'s spec can use it without depending on this type's `PTPhys` impl.
    pub uninterp spec fn byte_ptr(self) -> *mut u8;

    /// The byte that this permission tracks.
    pub uninterp spec fn byte(self) -> AbstractByte;

    /// Guarantees that the byte associated with this permission 
    /// is not associated with any other `PointsToByte` permission.
    /// (`self` is an &mut reference to enforce distinctness,
    /// so you cannot pass the same `PointsToByte` as both arguments.)
    pub axiom fn is_disjoint_byte(tracked &mut self, tracked other: &Self)
        requires
            self.wf_basic(),
            other.wf_basic(),
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + size_of::<u8>() <= other.ptr()@.addr || other.ptr()@.addr
                + size_of::<u8>() <= final(self).ptr()@.addr,
    ;
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

impl<T, P: PTProperties> PTPhysSealed for SeqPointsTo<T, P> {

}

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
        &&& self.ptr()@.metadata
            == self.len()
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
        &&& self.ptr()@.addr
            != 0
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

    // Borrows the byte from the element whose range contains `addr`.
    proof fn borrow_byte(tracked &self, addr: int) -> (tracked b: &PointsToByte) {
        let base = self.ptr()@.addr as int;
        let s = P::size(()) as int;
        let len = self.len() as int;
        assert(len != 0 && s != 0) by (nonlinear_arith)
            requires
                len * s > addr - base >= 0,
        ;
        let k = (addr - base) / s;
        super::super::arithmetic::div_mod::lemma_fundamental_div_mod(addr - base, s);
        super::super::arithmetic::div_mod::lemma_multiply_divide_lt(addr - base, s, len);
        self.seq_pt.tracked_borrow(k).borrow_byte(addr)
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
            old(self).wf_basic() && Self::ptrs_len_same(*old(self), *final(self))
                ==> final(self).wf_basic(),
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

    /// Creates a `SeqPointsTo` from a sequence of permissions and a pointer to the whole region.
    /// The inverse of `into_seq`.
    /// It says nothing about `wf_basic()`: callers prove it from the parts.
    pub proof fn from_seq(tracked s: Seq<P>, ptr: *mut [T]) -> (tracked out: Self)
        ensures
            out.seq_pt() == s,
            out.ptr() == ptr,
    {
        SeqPointsTo { seq_pt: s, ptr: Ghost(ptr) }
    }

    /// A borrowed `Seq<P>` acts as a borrowed `SeqPointsTo<T, P>` with the given pointer.
    pub proof fn from_seq_ref<'a>(tracked s: &'a Seq<P>, ptr: *mut [T]) -> (tracked out: &'a Self)
        ensures
            out.seq_pt() == *s,
            out.ptr() == ptr,
    {
        shr_ref_struct_wrap(s, &SeqPointsTo { seq_pt: *s, ptr: Ghost(ptr) }, "", "seq_pt")
    }

    /// A mutably borrowed `Seq<P>` acts as a mutably borrowed `SeqPointsTo<T, P>` with the given pointer.
    pub axiom fn from_seq_mut<'a>(tracked s: &'a mut Seq<P>, ptr: *mut [T]) -> (tracked out:
        &'a mut Self)
        ensures
            out.seq_pt() == *old(s),
            out.ptr() == ptr,
            *final(s) == final(out).seq_pt(),
    ;

    // TODO(real-ptr-flag): remove, with its callers, once pointers have an `is_real` flag.
    // It only proves the `isize::MAX` bounds on `from_elems_ref`/`from_elems_mut` and `tracked_from_spec`.
    /// The memory fits in an allocation:
    /// it takes at most `isize::MAX` bytes.
    pub proof fn lemma_size_bound(tracked &self)
        requires
            self.wf_basic(),
        ensures
            Self::size(self.ptr()@.metadata) <= isize::MAX,
    {
        broadcast use ptr_model::provenance_properties;

        if Self::size(self.ptr()@.metadata) != 0 {
            self.provenance_not_none();
            self.ptr_bounds();
        }
    }

    /// Permissions with the same sequence of permissions and pointer are equal.
    pub proof fn lemma_ext(a: Self, b: Self)
        requires
            a.seq_pt() == b.seq_pt(),
            a.ptr() == b.ptr(),
        ensures
            a == b,
    {
    }
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
    // TODO(verify-rustlib-transmute-v2): unsound without a length bound
    // (one shared borrow repeated past `usize::MAX` contradicts `axiom_spec_len`);
    // there it requires `elems.len() <= usize::MAX, elems.len() * size_of::<T>() <= isize::MAX`.
    /// A sequence of borrows of typed values acts as one borrow of a slice typed value.
    /// If any element is empty, the slice is empty.
    /// The slice length must fit in a `usize`.
    pub axiom fn from_elems_ref<'a>(tracked elems: Seq<&'a TypedValue<T>>) -> (tracked out:
        &'a TypedValue<[T]>)
        requires
            elems.len() <= usize::MAX,
            // TODO(real-ptr-flag): remove this bound once pointers have an `is_real` flag.
            // Until then, it stops a slice too large for memory from giving a well-formed `PointsTo`.
            // The `usize::MAX` bound above stays.
            elems.len() * size_of::<T>() <= isize::MAX,
        ensures
    // Valid with the elements' values if every element is valid
    // (a zero-length Seq counts as valid); otherwise empty.

            (forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid()) ==> {
                &&& out.is_valid()
                &&& out.value_ref()@ == Seq::new(elems.len(), |i: int| elems[i].value())
            },
            !(forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid())
                ==> out.is_empty(),
    ;

    // TODO(verify-rustlib-transmute-v2): gets the same length bound as `from_elems_ref` there.
    /// A sequence of mutable borrows of typed values acts as one mutable borrow of a slice typed value.
    /// If any element is empty, the slice starts empty.
    /// The slice length must fit in a `usize`.
    pub axiom fn from_elems_mut<'a>(tracked elems: Seq<&'a mut TypedValue<T>>) -> (tracked out:
        &'a mut TypedValue<[T]>)
        requires
            elems.len() <= usize::MAX,
            // TODO(real-ptr-flag): remove this bound once pointers have an `is_real` flag.
            // Until then, it stops a slice too large for memory from giving a well-formed `PointsTo`.
            // The `usize::MAX` bound above stays.
            elems.len() * size_of::<T>() <= isize::MAX,
        ensures
    // Initially: valid with the elements' values if every element is valid
    // (a zero-length Seq counts as valid); otherwise empty.

            (forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid()) ==> {
                &&& out.is_valid()
                &&& out.value_ref()@ == Seq::new(elems.len(), |i: int| elems[i].value())
            },
            !(forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid())
                ==> out.is_empty(),
            // Finally: a valid slice of the same length is distributed back to the elements;
            // anything else leaves every element empty.
            final(out).is_valid() && final(out).value_ref()@.len() == elems.len() ==> forall|i: int|

                #![trigger elems[i]]
                0 <= i < elems.len() ==> {
                    &&& final(elems[i]).is_valid()
                    &&& final(elems[i]).value() == final(out).value_ref()@[i]
                },
            !(final(out).is_valid() && final(out).value_ref()@.len() == elems.len()) ==> forall|
                i: int,
            |
                #![trigger elems[i]]
                0 <= i < elems.len() ==> final(elems[i]).is_empty(),
    ;
}

/// `pt_untyped` and `typed_value` are the parts of a well-formed `PointsToUnaligned<T>` for a pointer with view `ptr`.
pub open spec fn pt_unaligned_parts_wf<T>(
    ptr: PtrData<T>,
    pt_untyped: PointsToUntyped,
    typed_value: TypedValue<T>,
) -> bool {
    &&& pt_untyped.wf()
    &&& pt_untyped.ptr()@.addr == ptr.addr
    &&& pt_untyped.ptr()@.provenance == ptr.provenance
    &&& pt_untyped.len() == size_of::<T>()
    &&& typed_value.is_valid() ==> abstract_bytes_decode(pt_untyped.bytes(), typed_value.value_ref())
}

/// `pt_untyped` and `typed_value` are the parts of a well-formed `PointsTo<T>` for a pointer with view `ptr`.
pub open spec fn pt_parts_wf<T>(
    ptr: PtrData<T>,
    pt_untyped: PointsToUntyped,
    typed_value: TypedValue<T>,
) -> bool {
    &&& pt_unaligned_parts_wf(ptr, pt_untyped, typed_value)
    &&& ptr.addr as nat % align_of::<T>() == 0
}

/// `pt_untyped` and `typed_value` are the parts of a well-formed `PointsTo<[T]>` for a pointer with view `ptr`.
pub open spec fn pt_parts_wf_slice<T>(
    ptr: PtrData<[T]>,
    pt_untyped: PointsToUntyped,
    typed_value: TypedValue<[T]>,
) -> bool {
    &&& pt_untyped.wf()
    &&& pt_untyped.ptr()@.addr == ptr.addr
    &&& pt_untyped.ptr()@.provenance == ptr.provenance
    &&& pt_untyped.len() == ptr.metadata * size_of::<T>()
    &&& ptr.addr as nat % align_of::<T>() == 0
    &&& typed_value.is_valid() ==> {
        &&& abstract_bytes_decode(pt_untyped.bytes(), typed_value.value_ref())
        &&& typed_value.value_ref()@.len() == ptr.metadata
    }
}

} // verus!
