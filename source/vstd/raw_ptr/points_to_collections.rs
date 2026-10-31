#![allow(unused_imports)]

use super::points_to_model::*;
use super::ptr_model::*;
use crate::vstd::group_vstd_default;
use crate::vstd::layout::{self, *};
use crate::vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::vstd::set_lib::set_int_range;
#[cfg(verus_keep_ghost)]
use crate::vstd::type_representation::*;

verus! {

broadcast use {
    crate::vstd::raw_ptr::ptr_model::group_raw_ptr_axioms,
    layout::group_layout_axioms,
    crate::vstd::seq::group_seq_axioms,
};

/// Variable-sized uninitialized memory.
///
/// Permission is for an arbitrary set of addresses, not necessarily contiguous,
/// and with a given provenance.
/// Internally represented as a map from addresses to `PointsToByte` permissions.
/// Does not implement `PTPhys`, since it has no single pointer,
/// although equivalent properties from `PTProperties` hold.
// Note reading from uninitialized memory is UB, so we shouldn't give any
// reading capabilities to `PointsToRaw`. Turning a `PointsToRaw` into a typed `PointsTo`
// should always leave it as 'uninitialized'.
pub tracked struct PointsToRaw {
    bytes: Map<int, PointsToByte>,
    provenance: Ghost<Provenance>,
}

impl PointsToRaw {
    /// The domain is finite, and each byte permission is at its key's address,
    /// with this permission's provenance.
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.bytes.dom().finite()
        &&& forall|a: int| #[trigger]
            self.bytes.dom().contains(a) ==> {
                &&& self.bytes[a].ptr()@.addr == a
                &&& self.bytes[a].ptr()@.provenance == self.provenance@
            }
    }

    /// Provenance of the `PointsToRaw` permission;
    /// this corresponds to the original allocation and does not change.
    pub closed spec fn provenance(self) -> Provenance {
        self.provenance@
    }

    /// The map from addresses to `PointsToByte` permissions.
    pub closed spec fn bytes(self) -> Map<int, PointsToByte> {
        self.bytes
    }

    /// Memory addresses (domain) that the `PointsToRaw` permission gives access to.
    /// This set may be split apart and/or recombined, in order to create permissions to smaller pieces of the allocation.
    pub open spec fn dom(self) -> Set<int> {
        self.bytes().dom()
    }

    /// The abstract byte at address `a`.
    pub open spec fn byte(self, a: int) -> AbstractByte
        recommends
            self.dom().contains(a),
    {
        self.bytes()[a].byte()
    }

    /// Returns `true` if the domain of this permission is exactly the range `[start, start + len)`.
    pub open spec fn is_range(self, start: int, len: int) -> bool {
        set_int_range(start, start + len) =~= self.dom()
    }

    /// Returns `true` if the domain of this permission contains the range `[start, start + len)`.
    pub open spec fn contains_range(self, start: int, len: int) -> bool {
        set_int_range(start, start + len) <= self.dom()
    }

    /// The contents of `[start, start + len)` as a sequence.
    pub open spec fn bytes_range(self, start: int, len: nat) -> Seq<AbstractByte>
        recommends
            self.contains_range(start, len as int),
    {
        Seq::new(len, |i: int| self.byte(start + i))
    }

    /// Constructs a `PointsToRaw` permission over an empty domain with the given provenance.
    pub proof fn empty(provenance: Provenance) -> (tracked out: Self)
        ensures
            out.dom() == Set::<int>::empty(),
            out.provenance() == provenance,
    {
        broadcast use group_vstd_default;

        PointsToRaw { bytes: Map::tracked_empty(), provenance: Ghost(provenance) }
    }

    /// Splits the current `PointsToRaw` permission into a permission with domain `range`
    /// and a permission containing the rest of the domain,
    /// provided that `range` is contained in the domain of the current permission.
    pub proof fn split(tracked self, range: Set<int>) -> (tracked (subperm, rest): (Self, Self))
        requires
            range.subset_of(self.dom()),
        ensures
            subperm.provenance() == self.provenance(),
            rest.provenance() == self.provenance(),
            subperm.dom() == range,
            rest.dom() == self.dom().difference(range),
            forall|a| subperm.dom().contains(a) ==> #[trigger] subperm.byte(a) == self.byte(a),
            forall|a| rest.dom().contains(a) ==> #[trigger] rest.byte(a) == self.byte(a),
    {
        broadcast use group_vstd_default;

        use_type_invariant(&self);
        let ghost dom = self.dom();
        let tracked PointsToRaw { bytes: mut bytes, provenance } = self;
        let tracked sub_bytes = bytes.tracked_remove_keys(range);
        assert(sub_bytes.dom() =~= dom.intersect(range));
        assert(bytes.dom() =~= dom.difference(range));
        (PointsToRaw { bytes: sub_bytes, provenance }, PointsToRaw { bytes, provenance })
    }

    /// Joins two `PointsToRaw` permissions into one,
    /// provided that they have the same provenance.
    /// The memory addresses of the new permission is the union of the domains of `self` and `other`.
    pub proof fn join(tracked self, tracked other: Self) -> (tracked joined: Self)
        requires
            self.provenance() == other.provenance(),
        ensures
            joined.provenance() == self.provenance(),
            joined.dom() == self.dom() + other.dom(),
            // (the domains are disjoint by is_disjoint, so these don't conflict)
            forall|a| self.dom().contains(a) ==> #[trigger] joined.byte(a) == self.byte(a),
            forall|a| other.dom().contains(a) ==> #[trigger] joined.byte(a) == other.byte(a),
    {
        broadcast use group_vstd_default;

        use_type_invariant(&self);
        use_type_invariant(&other);
        let tracked mut first = self;
        if first.dom() != Set::<int>::empty() && other.dom() != Set::<int>::empty() {
            first.is_disjoint(&other);
        }
        assert forall|a| first.dom().contains(a) implies !other.dom().contains(a) by {
            assert(!first.dom().intersect(other.dom()).contains(a));
        }
        let tracked PointsToRaw { bytes: mut bytes, provenance } = first;
        let tracked PointsToRaw { bytes: other_bytes, .. } = other;
        let ghost (dom, other_dom) = (bytes.dom(), other_bytes.dom());
        bytes.tracked_union_prefer_right(other_bytes);
        assert(bytes.dom() =~= dom + other_dom);
        PointsToRaw { bytes, provenance }
    }

    /// The memory associated with an address in the domain should always be within bounds of its spatial provenance.
    pub proof fn ptr_bounds(tracked &self)
        ensures
            forall|a|
                self.dom().contains(a) ==> self.provenance().unwrap().start_addr() <= a
                    < self.provenance().unwrap().start_addr()
                    + self.provenance().unwrap().alloc_len(),
    {
        broadcast use group_vstd_default;

        use_type_invariant(self);
        if exists|a|
            self.dom().contains(a) && !(self.provenance().unwrap().start_addr() <= a
                < self.provenance().unwrap().start_addr()
                + self.provenance().unwrap().alloc_len()) {
            let a = choose|a|
                self.dom().contains(a) && !(self.provenance().unwrap().start_addr() <= a
                    < self.provenance().unwrap().start_addr()
                    + self.provenance().unwrap().alloc_len());
            let tracked byte = self.bytes.tracked_borrow(a);
            byte.provenance_not_none();
            byte.ptr_bounds();
        }
    }

    /// If the address domain is non-empty, then the provenance is not none.
    /// <https://doc.rust-lang.org/std/ptr/index.html#provenance>
    pub proof fn provenance_not_none(tracked &self)
        requires
            self.dom() != Set::<int>::empty(),
        ensures
            self.provenance() != Provenance::None,
    {
        broadcast use group_vstd_default;

        use_type_invariant(self);
        if forall|a| !self.dom().contains(a) {
            assert(self.dom() =~= Set::<int>::empty());
        }
        let a = choose|a| self.dom().contains(a);
        self.bytes.tracked_borrow(a).provenance_not_none();
    }

    /// Guarantees that the memory ranges associated with two distinct, non-empty permissions will not overlap,
    /// since you cannot have two permissions to the same memory.
    /// (`self` is an `&mut` reference to enforce distinctness,
    /// so you cannot pass the same `PointsToRaw` as both arguments.)
    pub proof fn is_disjoint(tracked &mut self, tracked other: &PointsToRaw)
        requires
            self.dom() != Set::<int>::empty(),
            other.dom() != Set::<int>::empty(),
        ensures
            *old(self) == *final(self),
            final(self).dom().intersect(other.dom()).is_empty(),
    {
        broadcast use group_vstd_default;

        use_type_invariant(&*self);
        use_type_invariant(other);
        if exists|a| #[trigger] self.dom().contains(a) && other.dom().contains(a) {
            let a = choose|a| #[trigger] self.dom().contains(a) && other.dom().contains(a);
            let tracked mut taken = PointsToRaw::empty(self.provenance());
            crate::vstd::modes::tracked_swap(self, &mut taken);
            let tracked PointsToRaw { bytes: mut bytes, .. } = taken;
            let tracked mut byte = bytes.tracked_remove(a);
            byte.is_disjoint_byte(other.bytes.tracked_borrow(a));
        }
    }

    /// Builds a map from `perms`, keyed by address, given that they're consecutive from `start`.
    proof fn map_from_seq(
        tracked perms: Seq<PointsToByte>,
        start: int,
        provenance: Provenance,
    ) -> (tracked m: Map<int, PointsToByte>)
        requires
            forall|i: int|
                0 <= i < perms.len() ==> {
                    &&& (#[trigger] perms[i]).ptr()@.addr == start + i
                    &&& perms[i].ptr()@.provenance == provenance
                },
        ensures
            m.dom() == set_int_range(start, start + perms.len()),
            forall|i: int| 0 <= i < perms.len() ==> m[start + i] == #[trigger] perms[i],
            forall|a: int| #[trigger]
                m.dom().contains(a) ==> {
                    &&& m[a].ptr()@.addr == a
                    &&& m[a].ptr()@.provenance == provenance
                },
        decreases perms.len(),
    {
        broadcast use group_vstd_default;

        if perms.len() == 0 {
            let tracked m = Map::tracked_empty();
            m
        } else {
            let tracked mut rest = perms;
            let tracked last = rest.tracked_pop();
            let tracked mut m = Self::map_from_seq(rest, start, provenance);
            m.tracked_insert(start + rest.len(), last);
            assert(m.dom() =~= set_int_range(start, start + perms.len()));
            assert forall|i: int| 0 <= i < perms.len() implies m[start + i]
                == #[trigger] perms[i] by {
                if i < rest.len() {
                    assert(perms[i] == rest[i]);
                }
            }
            m
        }
    }

    /// Removes the bytes at `[start, start + len)` from `m`, in address order.
    proof fn seq_from_map(
        tracked m: Map<int, PointsToByte>,
        start: int,
        len: nat,
    ) -> (tracked perms: Seq<PointsToByte>)
        requires
            set_int_range(start, start + len) <= m.dom(),
        ensures
            perms.len() == len,
            forall|i: int| 0 <= i < len ==> #[trigger] perms[i] == m[start + i],
        decreases len,
    {
        broadcast use group_vstd_default;

        if len == 0 {
            Seq::tracked_empty()
        } else {
            let tracked mut rest = m;
            let tracked last = rest.tracked_remove(start + len - 1);
            let tracked mut perms = Self::seq_from_map(rest, start, (len - 1) as nat);
            perms.tracked_push(last);
            perms
        }
    }

    /// Converts a `PointsToUntyped` into a `PointsToRaw` holding the same bytes.
    pub proof fn from_untyped(tracked pt_untyped: PointsToUntyped) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
        ensures
            out.provenance() == pt_untyped.ptr()@.provenance,
            out.is_range(pt_untyped.ptr()@.addr as int, pt_untyped.len() as int),
            out.bytes_range(pt_untyped.ptr()@.addr as int, pt_untyped.len()) == pt_untyped.bytes(),
    {
        let ghost old_untyped = pt_untyped;
        let ghost start = pt_untyped.ptr()@.addr as int;
        let ghost provenance = pt_untyped.ptr()@.provenance;
        let tracked perms = pt_untyped.into_seq();
        let tracked bytes = Self::map_from_seq(perms, start, provenance);
        crate::vstd::set_lib::lemma_int_range(start, start + old_untyped.len());
        let tracked out = PointsToRaw { bytes, provenance: Ghost(provenance) };
        out
    }

    /// Converts a `PointsToRaw` holding exactly the bytes in `[start, start + len)`
    /// into a `PointsToUntyped` for that range.
    pub proof fn into_untyped(tracked self, start: usize, len: nat) -> (tracked out:
        PointsToUntyped)
        requires
            self.is_range(start as int, len as int),
            start != 0,
            len == 0 && self.provenance().is_some() ==> self.provenance().unwrap().start_addr()
                <= start <= self.provenance().unwrap().start_addr()
                + self.provenance().unwrap().alloc_len(),
        ensures
            out.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData { addr: start, provenance: self.provenance(), metadata: len as usize },
            ),
            out.bytes() == self.bytes_range(start as int, len),
            out.wf(),
    {
        broadcast use group_vstd_default;

        use_type_invariant(&self);
        let ghost old_self = self;
        if len > 0 {
            assert(self.dom().contains(start as int));
            self.provenance_not_none();
            self.ptr_bounds();
            assert(self.dom().contains(start + len - 1));
        }
        let ptr = ptr_mut_from_data::<u8>(
            PtrData { addr: start, provenance: self.provenance(), metadata: () },
        );
        let tracked PointsToRaw { bytes, .. } = self;
        let tracked perms = Self::seq_from_map(bytes, start as int, len);
        assert forall|i: int| 0 <= i < perms.len() implies {
            &&& (#[trigger] perms[i]).ptr()@.provenance == ptr@.provenance
            &&& perms[i].ptr()@.addr == ptr@.addr + i * PointsToByte::size(())
        } by {
            assert(bytes.dom().contains(start + i));
        }
        let tracked out = PointsToUntyped::from_seq(perms, ptr);
        out
    }
}

/// The interface for a `SeqPointsTo<T, PointsTo<T>>` permission,
/// which represents permission to access a contiguous sequence of memory locations,
/// each aligned to `T` and possibly holding a valid value of type `T`.
/// We track the `*mut T` pointer to the start of that memory, along with the
/// `PointsTo<T>` permission for each element.
///
/// Note: the actual struct has a `*mut [T]` pointer,
/// but we can get the metadata from the length of `seq_pt`,
/// so the view only has the thin pointer.
#[cfg(verus_keep_ghost)]
pub ghost struct SeqPointsToData<T> {
    pub ptr: *mut T,
    pub seq_pt: Seq<PointsTo<T>>,
}

#[cfg(verus_keep_ghost)]
impl<T> View for SeqPointsTo<T, PointsTo<T>> {
    type V = SeqPointsToData<T>;

    open spec fn view(&self) -> Self::V {
        SeqPointsToData { ptr: self.thin_ptr(), seq_pt: self.seq_pt() }
    }
}

// The only typed sequence impl (there is no generic typed impl).
impl<T> SeqPointsTo<T, PointsTo<T>> {
    /// The pointer to the start of the memory region tracked by this permission,
    /// without the metadata (the metadata is the same as `self.len()`).
    pub open spec fn thin_ptr(self) -> *mut T {
        self.ptr() as *mut T
    }

    /// In addition to the well-formedness properties which must hold of every `SeqPointsTo` (`wf_basic`),
    /// the pointer must be aligned to `T`, and each element must be fully well-formed.
    // `SeqPointsTo::wf_basic` ensures each element satisfies its own `T::wf_basic()`,
    // which only captures pointer-level well-formedness conditions for ensuring `PTProperties` invariants.
    pub open spec fn wf(self) -> bool {
        &&& self.wf_basic()
        &&& PointsTo::<T>::satisfies_alignment(self.ptr()@.addr)
        &&& forall|i| 0 <= i < self.len() ==> #[trigger] self[i].wf()
    }

    /// A "flattened" view of the abstract bytes.
    /// Because the abstract bytes do not change across casting/transmuting, it is often more
    /// convenient to have a single flattened view of the bytes that is the same as for `PointsTo<[T]>`.
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        Self::bytes_inner(self.seq_pt())
    }

    /// The concatenation of the abstract bytes of each permission in `perms`.
    pub open spec fn bytes_inner(perms: Seq<PointsTo<T>>) -> Seq<AbstractByte> {
        perms.fold_left(Seq::empty(), |acc: Seq<AbstractByte>, elt: PointsTo<T>| acc + elt.bytes())
    }

    /// The sequence of (possibly-valid) typed values of each element.
    pub open spec fn seq_typed_value(self) -> Seq<TypedValue<T>> {
        self.seq_pt().map(|i: int, pt: PointsTo<T>| pt.typed_value())
    }

    /// Returns `true` if all of the permission's associated memory in `[start, end)` is valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_valid_subrange(&self, start: int, end: int) -> bool {
        &&& 0 <= start <= end <= self.len()
        &&& forall|i: int| start <= i < end ==> #[trigger] self[i].is_valid()
    }

    /// Given that `[start, end)` is valid, returns the underlying values in it as a sequence.
    #[verifier::inline]
    pub open spec fn value_subrange(&self, start: int, end: int) -> Seq<T>
        recommends
            self.is_valid_subrange(start, end),
    {
        Seq::new((end - start) as nat, |i: int| self[start + i].value())
    }

    /// Returns `true` if all of the permission's associated memory is valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_valid(&self) -> bool {
        self.is_valid_subrange(0, self.len() as int)
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
    pub open spec fn seq_value(&self) -> Seq<T>
        recommends
            self.is_valid(),
    {
        self.value_subrange(0, self.len() as int)
    }

    /// The pointer-level `ptrs_len_same`,
    /// which ensures `old` and `new` have the same pointer and length
    /// and that `P::ptrs_len_same` holds on each element of `old` and `new`,
    /// plus each element's validity constraints (`valid_value`).
    pub open spec fn ptrs_len_same_valid_value(old: Self, new: Self) -> bool {
        &&& Self::ptrs_len_same(old, new)
        &&& forall|i| #![trigger new[i]] 0 <= i < new.len() ==> new[i].valid_value()
    }

    /// If `old` is well-formed and `new` has the same pointers and length, with each element
    /// still satisfying its validity constraints (`valid_value`), then `new` is well-formed.
    pub proof fn stays_wf(old: Self, new: Self)
        requires
            old.wf(),
            Self::ptrs_len_same_valid_value(old, new),
        ensures
            new.wf(),
    {
        assert forall|i| 0 <= i < new.len() implies #[trigger] new[i].wf() by {
            PointsTo::<T>::stays_wf(old[i], new[i]);
        }
    }

    /// If `old` and `new` are both well-formed with the same pointer, then each element
    /// of `new` keeps the corresponding element of `old`'s pointers and length, and still
    /// satisfies its validity constraints.
    /// Having the same pointer means the length is the same (the pointer carries it),
    /// so there is no separate length precondition.
    pub broadcast proof fn lemma_ptrs_len_same_valid_value(old: Self, new: Self)
        requires
            old.wf(),
            new.wf(),
            new.ptr() == old.ptr(),
        ensures
            #[trigger] Self::ptrs_len_same_valid_value(old, new),
    {
        assert forall|i: int| #![trigger new[i]] 0 <= i < new.len() implies {
            &&& new[i].valid_value()
            &&& PointsTo::<T>::ptrs_len_same(old[i], new[i])
            &&& new[i].ptr() == old[i].ptr()
        } by {
            assert(new[i].ptr()@.addr == old[i].ptr()@.addr);
            PointsTo::<T>::lemma_ptrs_len_same_valid_value(old[i], new[i]);
        }
    }

    /// A `SeqPointsTo<T, PointsTo<T>>` is always aligned to `T`.
    pub proof fn is_aligned(tracked &self)
        requires
            self.wf(),
        ensures
            self.ptr()@.addr as nat % align_of::<T>() == 0,
    {
    }

    /// Proof of equivalence for two different ways to get the `TypedValue<T>` at a given index `i`.
    pub broadcast proof fn typed_value_equiv(self, i: int)
        requires
            0 <= i < self.len(),
        ensures
            #![trigger self.seq_typed_value()[i]]
            #![trigger self.seq_pt()[i]]
            self.seq_typed_value()[i] == self.seq_pt()[i].typed_value(),
    {
    }

    /// The length of the flattened abstract bytes for a sequence of well-formed permissions
    /// matches the size of this type multiplied by the number of elements in the sequence.
    proof fn bytes_len_helper(perms: Seq<PointsTo<T>>)
        requires
            forall|i: int| 0 <= i < perms.len() ==> #[trigger] perms[i].wf(),
        ensures
            Self::bytes_inner(perms).len() == perms.len() * size_of::<T>(),
        decreases perms.len(),
    {
        if perms.len() > 0 {
            Self::bytes_len_helper(perms.drop_last());
            perms.last().bytes_decode();
            assert((perms.len() - 1) * size_of::<T>() + size_of::<T>() == perms.len() * size_of::<
                T,
            >()) by (nonlinear_arith);
        }
    }

    /// The length of the abstract bytes matches the size of this type multiplied by the number of elements this permission represents.
    pub broadcast proof fn bytes_len(&self)
        requires
            self.wf(),
        ensures
            #[trigger] self.bytes().len() == self.len() * size_of::<T>(),
    {
        Self::bytes_len_helper(self.seq_pt());
    }

    // Relates the abstract bytes for a sequence of permissions to subranges of those permissions and subranges of the abstract bytes.
    // Useful for avoiding reasoning about fold_left directly.
    proof fn bytes_subrange(perms: Seq<PointsTo<T>>, split: int)
        requires
            0 <= split <= perms.len(),
            forall|i: int| 0 <= i < perms.len() ==> #[trigger] perms[i].wf(),
        ensures
    // abstract bytes can be split by subranges of the permissions themselves

            Self::bytes_inner(perms) == Self::bytes_inner(perms.subrange(0, split))
                + Self::bytes_inner(perms.subrange(split, perms.len() as int)),
            // abstract bytes of a prefix of permssions correspond to a prefix of the entire abstract bytes
            Self::bytes_inner(perms.subrange(0, split)) == Self::bytes_inner(perms).subrange(
                0,
                split * size_of::<T>(),
            ),
            // abstract bytes of a suffix of permissions correspond to suffix of the entire abstract bytes
            Self::bytes_inner(perms.subrange(split, perms.len() as int)) == Self::bytes_inner(
                perms,
            ).subrange(split * size_of::<T>(), perms.len() as int * size_of::<T>()),
            // the abstract bytes of a prefix of permissions has the expected length
            Self::bytes_inner(perms.subrange(0, split)).len() == split * size_of::<T>(),
            // the abstract bytes of a suffix of permissions has the expected length
            Self::bytes_inner(perms.subrange(split, perms.len() as int)).len() == (perms.len()
                - split) * size_of::<T>(),
        decreases perms.len() - split,
    {
        broadcast use group_vstd_default, crate::vstd::arithmetic::mul::group_mul_basics;

        if perms.len() > split {
            Self::bytes_subrange(perms.subrange(0, perms.len() - 1), split);
            perms.lemma_slice_of_slice(0, perms.len() - 1, 0, split);
            perms.lemma_slice_of_slice(0, perms.len() - 1, split, perms.len() - 1);
            assert(Self::bytes_inner(perms.subrange(0, perms.len() - 1)) == Self::bytes_inner(
                perms.subrange(0, split),
            ) + Self::bytes_inner(perms.subrange(split, perms.len() - 1)));

            assert(perms.subrange(split, perms.len() as int).drop_last() == perms.subrange(
                split,
                perms.len() - 1,
            ));

            Self::bytes_len_helper(perms.subrange(0, split));
            Self::bytes_len_helper(perms.subrange(split, perms.len() as int));
            assert(Self::bytes_inner(perms).len() - Self::bytes_inner(
                perms.subrange(0, split),
            ).len() == Self::bytes_inner(perms.subrange(split, perms.len() as int)).len());
            assert(perms.len() * size_of::<T>() - split * size_of::<T>() == (perms.len() - split)
                * size_of::<T>()) by (nonlinear_arith);
        } else {
            Self::bytes_len_helper(perms);
        }
    }

    /// The abstract bytes of an individual permission in a sequence corresponds to a subrange of length `size_of::<T>()`
    /// from the entire abstract bytes.
    pub broadcast proof fn bytes_equiv(&self, i: int)
        requires
            self.wf(),
            0 <= i < self.len(),
        ensures
            #[trigger] self.seq_pt()[i].bytes() == self.bytes().subrange(
                i * size_of::<T>(),
                (i + 1) * size_of::<T>(),
            ),
    {
        Self::bytes_len_helper(self.seq_pt());

        Self::bytes_subrange(self.seq_pt(), i + 1);
        Self::bytes_subrange(self.seq_pt().subrange(0, i + 1), i);
        self.bytes().lemma_slice_of_slice(
            0,
            (i + 1) * size_of::<T>(),
            i * size_of::<T>(),
            (i + 1) * size_of::<T>(),
        );
    }

    /// If `sub` holds the permissions in `[start, end)` of `self`,
    /// then its abstract bytes are the subrange `[start * size_of::<T>(), end * size_of::<T>())`
    /// of `self`'s abstract bytes.
    pub proof fn bytes_subrange_equiv(&self, sub: Self, start: int, end: int)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
            sub.seq_pt() == self.seq_pt().subrange(start, end),
        ensures
            sub.bytes() == self.bytes().subrange(start * size_of::<T>(), end * size_of::<T>()),
    {
        let perms = self.seq_pt();
        Self::bytes_len_helper(perms);

        Self::bytes_subrange(perms, end);
        Self::bytes_subrange(perms.subrange(0, end), start);
        perms.lemma_slice_of_slice(0, end, start, end);
        assert(start * size_of::<T>() <= end * size_of::<T>()) by (nonlinear_arith)
            requires
                start <= end,
        ;
        assert(end * size_of::<T>() <= perms.len() * size_of::<T>()) by (nonlinear_arith)
            requires
                end <= perms.len(),
        ;
        self.bytes().lemma_slice_of_slice(
            0,
            end * size_of::<T>(),
            start * size_of::<T>(),
            end * size_of::<T>(),
        );
    }

    /// For all positions in this sequence, the bytes for that position (given `self.wf()`)
    /// can be decoded into the value in memory at that position.
    proof fn bytes_decode_helper(&self, len: int)
        requires
            0 <= len <= self.len(),
            self.wf(),
        ensures
            forall|i: int|
                0 <= i < len ==> {
                    &&& (#[trigger] self.seq_typed_value()[i]).is_valid() ==> abs_decode::<T>(
                        self.seq_pt()[i].bytes(),
                        &self.seq_typed_value()[i].value(),
                    )
                    &&& self.seq_pt()[i].bytes().len() == size_of::<T>()
                },
        decreases len,
    {
        if len > 0 {
            self.bytes_decode_helper(len - 1);
            assert(self.seq_pt()[len - 1].wf());
        }
    }

    /// For all positions in this sequence,
    /// the abstract bytes for that position can be decoded into the value in memory at that position.
    pub proof fn bytes_decode(&self)
        requires
            self.wf(),
        ensures
            forall|i: int|
                0 <= i < self.len() ==> {
                    &&& (#[trigger] self.seq_typed_value()[i]).is_valid() ==> abs_decode::<T>(
                        self.bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
                        &self.seq_typed_value()[i].value(),
                    )
                    &&& self.seq_pt()[i].bytes().len() == size_of::<T>()
                },
    {
        broadcast use SeqPointsTo::bytes_equiv;

        self.bytes_decode_helper(self.len() as int);
    }

    /// We can construct a `SeqPointsTo` with `length`-many `PointsTo` permissions,
    /// provided that `T` is zero-sized;
    /// the pointer is non-null, aligned, and within bounds of its provenance;
    /// and the length is bounded by `usize::MAX`.
    pub proof fn zero_sized(ptr: *mut T, length: nat) -> (tracked out: Self)
        requires
            size_of::<T>() == 0,
            ptr@.addr != 0,
            PointsTo::<T>::satisfies_alignment(ptr@.addr),
            ptr_addr_in_bounds(ptr),
            length <= usize::MAX,
        ensures
            forall|i| 0 <= i < out.len() ==> (#[trigger] out[i]).is_empty(),
            out.thin_ptr() == ptr,
            out.len() == length,
            out.wf(),
    {
        Self::empty(ptr).zero_sized_helper(length, length)
    }

    proof fn zero_sized_helper(tracked self, remaining: nat, total: nat) -> (tracked out: Self)
        requires
            size_of::<T>() == 0,
            self.len() + remaining == total,
            total <= usize::MAX,
            forall|i| 0 <= i < self.len() ==> (#[trigger] self[i]).is_empty(),
            self.wf(),
        ensures
            out.thin_ptr() == self.thin_ptr(),
            out.len() == total,
            forall|i| 0 <= i < out.len() ==> (#[trigger] out[i]).is_empty(),
            out.wf(),
        decreases remaining,
    {
        if remaining == 0 {
            self
        } else {
            let ghost old_self = self;
            let ptr = self.thin_ptr();
            let tracked zs_pt = PointsTo::zero_sized(ptr);
            let tracked mut perms = self.into_seq();
            perms.tracked_push(zs_pt);
            assert forall|i: int| 0 <= i < perms.len() implies {
                &&& #[trigger] perms[i].ptr()@.addr == ptr@.addr + i * size_of::<T>()
                &&& perms[i].ptr()@.provenance == ptr@.provenance
            } by {
                assert(i * size_of::<T>() == 0) by (nonlinear_arith)
                    requires
                        size_of::<T>() == 0,
                ;
            }
            let tracked seq = Self::from_seq(perms, ptr);
            seq.zero_sized_helper((remaining - 1) as nat, total)
        }
    }

    /// Splits the `SeqPointsTo` into two permissions at the index boundary `mid`.
    pub proof fn split(tracked self, mid: nat) -> (tracked (first, second): (Self, Self))
        requires
            mid <= self.len(),
            self.wf(),
        ensures
            first.seq_pt() == self.seq_pt().take(mid as int),
            second.seq_pt() == self.seq_pt().skip(mid as int),
            first.bytes() == self.bytes().take(mid as int * size_of::<T>()),
            second.bytes() == self.bytes().skip(mid as int * size_of::<T>()),
            first.ptr() == ptr_mut_from_data::<[T]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: mid as usize,
                },
            ),
            second.ptr() == ptr_mut_from_data::<[T]>(
                PtrData {
                    addr: (self.ptr()@.addr + mid * size_of::<T>()) as usize,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() - mid) as usize,
                },
            ),
            first.wf(),
            second.wf(),
    {
        let ghost old_self = self;
        self.lemma_offset_in_bounds(mid);
        PointsTo::<T>::lemma_satisfies_alignment_offset(self.ptr()@.addr, mid);
        let tracked (first, second) = self.split_basic(mid);
        Self::bytes_subrange(old_self.seq_pt(), mid as int);
        (first, second)
    }

    /// The address `i` elements past the start doesn't overflow, for any `i` up to the length.
    proof fn lemma_offset_in_bounds(tracked &self, i: nat)
        requires
            self.wf_basic(),
            i <= self.len(),
        ensures
            self.ptr()@.addr + i * size_of::<T>() <= usize::MAX,
    {
        let n = self.len();
        let s = size_of::<T>();
        if n * s != 0 {
            self.provenance_not_none();
            self.ptr_bounds();
        }
        assert(i * s <= n * s) by (nonlinear_arith)
            requires
                i <= n,
        ;
    }

    /// Concatenates `SeqPointsTo` permissions `self` and `other`,
    /// provided their pointers have the same provenance
    /// and `other`'s pointer starts at the end of `self`'s range.
    pub proof fn join(tracked self, tracked other: Self) -> (tracked joined: Self)
        requires
            self.wf(),
            other.wf(),
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len() * size_of::<T>(),
            size_of::<T>() == 0 ==> self.len() + other.len() <= usize::MAX,
        ensures
            joined.ptr() == ptr_mut_from_data::<[T]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() + other.len()) as usize,
                },
            ),
            joined.seq_pt() == self.seq_pt() + other.seq_pt(),
            joined.bytes() == self.bytes() + other.bytes(),
            joined.wf(),
    {
        let ghost old_self = self;
        let ghost old_other = other;

        let tracked joined = self.join_basic(other);

        Self::bytes_subrange(joined.seq_pt(), old_self.len() as int);
        assert(joined.seq_pt().subrange(0, old_self.len() as int) =~= old_self.seq_pt());
        assert(joined.seq_pt().subrange(old_self.len() as int, joined.len() as int)
            =~= old_other.seq_pt());
        joined
    }

    /// Given that `[start, end)` is within bounds,
    /// it is always possible to borrow a permission to just that subrange.
    pub proof fn subrange(tracked &self, start: nat, end: nat) -> (tracked sub: &Self)
        requires
            self.wf(),
            start <= end <= self.len(),
        ensures
            sub.wf(),
            sub.ptr() == ptr_mut_from_data::<[T]>(
                PtrData {
                    addr: (self.ptr()@.addr + start * size_of::<T>()) as usize,
                    provenance: self.ptr()@.provenance,
                    metadata: (end - start) as usize,
                },
            ),
            sub.seq_pt() == self.seq_pt().subrange(start as int, end as int),
    {
        self.lemma_offset_in_bounds(start);
        PointsTo::<T>::lemma_satisfies_alignment_offset(self.ptr()@.addr, start);
        self.subrange_basic(start, end)
    }

    /// Returns a mutable reference to the sub-permission covering indices `[i, j)`.
    /// The sub-permission has the same provenance,
    /// and its pointer is offset from `self.ptr()` by `i * size_of::<T>()`.
    ///
    /// `self` keeps its pointer,
    /// with the sub-sequence of permissions replaced by the final sub-permission's.
    /// Provided that the sub-permission keeps its pointers and length,
    /// with each element still satisfying its validity constraints (`ptrs_len_same_valid_value`),
    /// `self` is also still well-formed.
    pub proof fn subrange_mut(tracked &mut self, i: nat, j: nat) -> (tracked subperm: &mut Self)
        requires
            self.wf(),
            i <= j <= self.len(),
        ensures
            subperm.wf(),
            subperm.ptr() == ptr_mut_from_data::<[T]>(
                PtrData {
                    addr: (old(self).ptr()@.addr + i * size_of::<T>()) as usize,
                    provenance: old(self).ptr()@.provenance,
                    metadata: (j - i) as usize,
                },
            ),
            subperm.seq_pt() == old(self).seq_pt().subrange(i as int, j as int),
            final(self).ptr() == old(self).ptr(),
            final(self).seq_pt() == old(self).seq_pt().subrange(0, i as int)
                + final(subperm).seq_pt() + old(self).seq_pt().subrange(
                j as int,
                old(self).len() as int,
            ),
            // Criteria necessary for re-establishing invariants
            Self::ptrs_len_same_valid_value(*subperm, *final(subperm)) ==> final(self).wf(),
    {
        let old_self = *self;
        let self_ref = self;
        // The shared subrange has the same pointer and permissions, so `subperm` is well-formed too.
        let tracked shared_sub = self.subrange(i, j);
        let ghost sub_ptr = shared_sub.ptr();
        let tracked seq_pt = self.tracked_seq_pt_mut();
        let tracked sub_seq_pt = seq_pt.tracked_borrow_subrange_mut(i as int, j as int);
        let tracked subperm = Self::from_seq_mut(sub_seq_pt, sub_ptr);
        let subperm_ref = subperm;

        // Final values
        let new_self = *final(self_ref);
        if Self::ptrs_len_same_valid_value(*subperm_ref, *final(subperm_ref)) {
            assert forall|k: int| 0 <= k < new_self.len() implies {
                &&& #[trigger] new_self[k].wf()
                &&& new_self[k].ptr() == old_self[k].ptr()
            } by {
                if i <= k < j {
                    PointsTo::<T>::stays_wf(subperm_ref[k - i], final(subperm_ref)[k - i]);
                }
            }
        }
        subperm
    }

    /// Takes a borrow of each of the `n` `TypedValue<T>`s starting at index `start`.
    proof fn borrow_typed_values(tracked &self, start: int, n: nat) -> (tracked val: Seq<
        &TypedValue<T>,
    >)
        requires
            self.wf(),
            0 <= start <= start + n <= self.len(),
        ensures
            val.len() == n,
            forall|i: int| 0 <= i < n ==> *#[trigger] val[i] == self.seq_typed_value()[start + i],
        decreases n,
    {
        if n == 0 {
            Seq::tracked_empty()
        } else {
            let tracked mut val = self.borrow_typed_values(start, (n - 1) as nat);
            let j = start + n - 1;
            let tracked last = self.tracked_seq_pt().tracked_borrow(j).borrow_typed_value();
            val.tracked_push(last);
            val
        }
    }

    /// This takes a borrow of each of the `TypedValue<T>`s in a subrange of `self`.
    pub proof fn borrow_typed_value_subrange(tracked &self, start: int, end: int) -> (tracked val:
        Seq<&TypedValue<T>>)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
        ensures
            val.map_values(|r: &TypedValue<T>| *r) == self.seq_typed_value().subrange(start, end),
    {
        let tracked val = self.borrow_typed_values(start, (end - start) as nat);
        val
    }

    /// The flattened abstract bytes depend only on the abstract bytes of each individual permission.
    proof fn bytes_inner_ext(a: Seq<PointsTo<T>>, b: Seq<PointsTo<T>>)
        requires
            a.len() == b.len(),
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].bytes() == b[i].bytes(),
        ensures
            Self::bytes_inner(a) == Self::bytes_inner(b),
        decreases a.len(),
    {
        if a.len() > 0 {
            Self::bytes_inner_ext(a.drop_last(), b.drop_last());
        }
    }

    /// This moves a subrange of the `TypedValue<T>`s out from `self`,
    /// leaving that subrange empty.
    pub proof fn take_typed_value_subrange(tracked &mut self, start: int, end: int) -> (tracked val:
        Seq<TypedValue<T>>)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
        ensures
            val == old(self).seq_typed_value().subrange(start, end),
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).seq_typed_value() == old(self).seq_typed_value().update_subrange_with(
                start,
                Seq::new((end - start) as nat, |i: int| TypedValue::Empty),
            ),
            final(self).wf(),
        decreases end - start,
    {
        if start == end {
            Seq::tracked_empty()
        } else {
            let old_self = *self;

            // Take the last value in the range out of the element at `end - 1`
            let tracked elt = self.index_mut(end - 1);
            let tracked taken = elt.take_typed_value();

            // The bytes of the whole sequence are unchanged
            Self::bytes_inner_ext(old_self.seq_pt(), self.seq_pt());

            // Take the rest of the range out of the preceding elements
            let tracked mut val = self.take_typed_value_subrange(start, end - 1);
            val.tracked_push(taken);

            val
        }
    }

    /// Consumes the `Seq<TypedValue<T>>`
    /// and puts it in the specified subrange of the `TypedValue<T>`s for `self`.
    pub proof fn put_typed_value_subrange(
        tracked &mut self,
        start: int,
        tracked val: Seq<TypedValue<T>>,
    )
        requires
            self.wf(),
            0 <= start <= start + val.len() <= self.len(),
            forall|i: int|
                0 <= i < val.len() ==> {
                    (#[trigger] val[i]).is_valid() ==> abs_decode::<T>(
                        self.bytes().subrange(
                            (start + i) * size_of::<T>(),
                            (start + i + 1) * size_of::<T>(),
                        ),
                        &val[i].value(),
                    )
                },
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).seq_typed_value() == old(self).seq_typed_value().update_subrange_with(
                start,
                val,
            ),
            final(self).wf(),
        decreases val.len(),
    {
        if val.len() > 0 {
            let old_self = *self;
            let tracked mut rest = val;
            let tracked first = rest.tracked_pop_front();

            // Put the first value into the element at `start`
            old_self.bytes_equiv(start);
            let tracked elt = self.index_mut(start);
            elt.put_typed_value(first);

            // The bytes of the whole sequence are unchanged
            Self::bytes_inner_ext(old_self.seq_pt(), self.seq_pt());

            // Put the rest of the values into the following elements
            self.put_typed_value_subrange(start + 1, rest);
        }
    }

    /// Copies the `TypedValue<T>`s out of a sequence of shared references, given that `T` is `Copy`.
    proof fn copy_typed_values(tracked val: Seq<&TypedValue<T>>) -> (tracked out: Seq<
        TypedValue<T>,
    >) where T: Copy
        ensures
            out == val.map_values(|r: &TypedValue<T>| *r),
        decreases val.len(),
    {
        if val.len() == 0 {
            Seq::tracked_empty()
        } else {
            let tracked mut rest = val;
            let tracked last = rest.tracked_pop();
            let tracked mut out = Self::copy_typed_values(rest);
            out.tracked_push(last.tracked_copy());
            out
        }
    }

    /// Copies the given `TypedValue<T>`s into the subrange starting at `start`.
    pub proof fn copy_typed_value_subrange(
        tracked &mut self,
        start: int,
        tracked val: Seq<&TypedValue<T>>,
    ) where T: Copy
        requires
            self.wf(),
            0 <= start <= start + val.len() <= self.len(),
            forall|i: int|
                0 <= i < val.len() ==> {
                    (#[trigger] val[i]).is_valid() ==> abs_decode::<T>(
                        self.bytes().subrange(
                            (start + i) * size_of::<T>(),
                            (start + i + 1) * size_of::<T>(),
                        ),
                        &val[i].value(),
                    )
                },
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).seq_typed_value() == old(self).seq_typed_value().update_subrange_with(
                start,
                val.map_values(|r: &TypedValue<T>| *r),
            ),
            final(self).wf(),
    {
        let tracked copied = Self::copy_typed_values(val);
        self.put_typed_value_subrange(start, copied);
    }

    /// Takes a borrow of each of the `n` (valid) values starting at index `start`.
    proof fn borrow_values(tracked &self, start: int, n: nat) -> (tracked val: Seq<&T>)
        requires
            self.wf(),
            self.is_valid_subrange(start, start + n),
        ensures
            val.len() == n,
            forall|i: int| 0 <= i < n ==> *#[trigger] val[i] == self[start + i].value(),
        decreases n,
    {
        if n == 0 {
            Seq::tracked_empty()
        } else {
            let tracked mut val = self.borrow_values(start, (n - 1) as nat);
            let j = start + n - 1;
            let tracked elt = self.tracked_seq_pt().tracked_borrow(j);
            assert(<PointsTo<T> as PTTypedValue>::typed_value(*elt) == elt.typed_value());
            let tracked last = elt.borrow();
            val.tracked_push(last);
            val
        }
    }

    /// This takes a borrow of each of the values in a subrange of `self`.
    pub proof fn borrow_subrange(tracked &self, start: int, end: int) -> (tracked val: Seq<&T>)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
            self.is_valid_subrange(start, end),
        ensures
            val.map_values(|r: &T| *r) == self.value_subrange(start, end),
    {
        let tracked val = self.borrow_values(start, (end - start) as nat);
        val
    }

    /// This moves a subrange of the values out from `self`,
    /// leaving that subrange empty.
    pub proof fn take_subrange(tracked &mut self, start: int, end: int) -> (tracked val: Seq<T>)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
            self.is_valid_subrange(start, end),
        ensures
            val == old(self).value_subrange(start, end),
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).seq_typed_value() == old(self).seq_typed_value().update_subrange_with(
                start,
                Seq::new((end - start) as nat, |i: int| TypedValue::Empty),
            ),
            final(self).wf(),
        decreases end - start,
    {
        if start == end {
            Seq::tracked_empty()
        } else {
            let old_self = *self;

            // Take the last value in the range out of the element at `end - 1`
            let tracked elt = self.index_mut(end - 1);
            assert(<PointsTo<T> as PTTypedValue>::typed_value(*elt) == elt.typed_value());
            let tracked taken = elt.take();

            // The bytes of the whole sequence are unchanged
            Self::bytes_inner_ext(old_self.seq_pt(), self.seq_pt());

            // Take the rest of the range out of the preceding elements
            let tracked mut val = self.take_subrange(start, end - 1);
            val.tracked_push(taken);

            val
        }
    }

    /// Consumes the `Seq<T>`
    /// and puts it in the specified subrange of the `TypedValue<T>`s for `self`.
    pub proof fn put_subrange(tracked &mut self, start: int, tracked val: Seq<T>)
        requires
            self.wf(),
            0 <= start <= start + val.len() <= self.len(),
            forall|i: int|
                0 <= i < val.len() ==> {
                    abs_decode::<T>(
                        self.bytes().subrange(
                            (start + i) * size_of::<T>(),
                            (start + i + 1) * size_of::<T>(),
                        ),
                        &val[i],
                    )
                },
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).len() == old(self).len(),
            final(self).is_valid_subrange(start, start + val.len()),
            final(self).value_subrange(start, start + val.len()) == val,
            forall|i: int|
                0 <= i < old(self).len() && !(start <= i < start + val.len())
                    ==> #[trigger] final(self).seq_typed_value()[i] == old(
                    self,
                ).seq_typed_value()[i],
            final(self).wf(),
        decreases val.len(),
    {
        if val.len() > 0 {
            let old_self = *self;
            let tracked mut rest = val;
            let tracked first = rest.tracked_pop_front();

            // Put the first value into the element at `start`
            old_self.bytes_equiv(start);
            let tracked elt = self.index_mut(start);
            elt.put(first);

            // The bytes of the whole sequence are unchanged
            Self::bytes_inner_ext(old_self.seq_pt(), self.seq_pt());

            // Put the rest of the values into the following elements
            self.put_subrange(start + 1, rest);

            // The subrange holds `first` at `start`, followed by `rest`
            Self::typed_value_equiv(*self, start);
            assert forall|i: int| start <= i < start + val.len() implies #[trigger] self[i].value()
                == val[i - start] by {
                if i > start {
                    assert(rest[i - start - 1] == val[i - start]);
                }
            }
        }
    }

    /// Copies the first `n` values out of a shared reference to a sequence, given that `T` is `Copy`.
    proof fn copy_values(tracked val: &Seq<T>, n: nat) -> (tracked out: Seq<T>) where T: Copy
        requires
            n <= val.len(),
        ensures
            out == val.take(n as int),
        decreases n,
    {
        if n == 0 {
            Seq::tracked_empty()
        } else {
            let tracked mut out = Self::copy_values(val, (n - 1) as nat);
            let tracked last = *val.tracked_borrow((n - 1) as int);
            out.tracked_push(last);
            out
        }
    }

    /// Copies the given values into the subrange starting at `start`.
    pub proof fn copy_subrange(tracked &mut self, start: int, tracked val: &Seq<T>) where T: Copy
        requires
            self.wf(),
            0 <= start <= start + val.len() <= self.len(),
            forall|i: int|
                0 <= i < val.len() ==> {
                    abs_decode::<T>(
                        self.bytes().subrange(
                            (start + i) * size_of::<T>(),
                            (start + i + 1) * size_of::<T>(),
                        ),
                        &val[i],
                    )
                },
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).len() == old(self).len(),
            final(self).is_valid_subrange(start, start + val.len()),
            final(self).value_subrange(start, start + val.len()) == val,
            forall|i: int|
                0 <= i < old(self).len() && !(start <= i < start + val.len())
                    ==> #[trigger] final(self).seq_typed_value()[i] == old(
                    self,
                ).seq_typed_value()[i],
            final(self).wf(),
    {
        let tracked copied = Self::copy_values(val, val.len());
        assert(copied =~= *val);
        self.put_subrange(start, copied);
    }

    /// Takes a mutable borrow of the `T` in each of the (valid) permissions in `perms`.
    proof fn borrow_mut_values(tracked perms: &mut Seq<PointsTo<T>>) -> (tracked ret: Seq<&mut T>)
        requires
            forall|i: int| 0 <= i < perms.len() ==> #[trigger] perms[i].wf() && perms[i].is_valid(),
        ensures
            ret.len() == old(perms).len(),
            final(perms).len() == old(perms).len(),
            forall|i: int|
                #![trigger ret[i]]
                #![trigger final(perms)[i]]
                0 <= i < ret.len() ==> {
                    &&& *ret[i] == old(perms)[i].value()
                    &&& final(perms)[i].is_valid()
                    &&& final(perms)[i].ptr() == old(perms)[i].ptr()
                    &&& final(perms)[i].value() == *final(ret[i])
                    &&& final(perms)[i].wf()
                },
        decreases perms.len(),
    {
        broadcast use group_vstd_default;

        if perms.len() == 0 {
            Seq::tracked_empty()
        } else {
            let old_perms = *perms;
            let perms_ref = perms;
            assert(old_perms[0].wf());
            assert(old_perms[0].is_valid());
            let tracked (first, rest) = perms.tracked_split_borrow_mut(1);
            assert(first[0] == old_perms[0]);
            let tracked elt = first.tracked_borrow_mut(0);
            let elt_ref = elt;
            let tracked v = elt.borrow_mut();
            assert forall|i: int| 0 <= i < rest.len() implies #[trigger] rest[i].wf()
                && rest[i].is_valid() by {
                assert(rest[i] == old_perms[i + 1]);
            }
            let rest_ref = rest;
            let tracked mut ret = Self::borrow_mut_values(rest);
            let ret_rest = ret;
            ret.tracked_insert(0, v);
            assert(final(perms_ref)[0] == *final(elt_ref));
            assert forall|i: int| 0 < i < ret.len() implies #[trigger] ret[i] == ret_rest[i - 1]
                && final(perms_ref)[i] == final(rest_ref)[i - 1] && old_perms[i] == rest_ref[i
                - 1] by {}
            ret
        }
    }

    /// This takes a mutable borrow of each of the values in a subrange of `self`.
    pub proof fn borrow_mut_subrange(tracked &mut self, start: int, end: int) -> (tracked ret: Seq<
        &mut T,
    >)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
            self.is_valid_subrange(start, end),
        ensures
            ret.len() == end - start,
            forall|i: int|
                0 <= i < ret.len() ==> *#[trigger] ret[i] == old(self)[start + i].value(),
            final(self).ptr() == old(self).ptr(),
            final(self).is_valid_subrange(start, end),
            forall|i: int|
                #![trigger ret[i]]
                0 <= i < ret.len() ==> final(self)[start + i].value() == *final(ret[i]),
            forall|i: int|
                0 <= i < old(self).len() && !(start <= i < end)
                    ==> #[trigger] final(self).seq_typed_value()[i] == old(
                    self,
                ).seq_typed_value()[i],
            final(self).wf(),
    {
        let old_self = *self;
        let self_ref = self;
        let tracked seq_pt = self.tracked_seq_pt_mut();
        let tracked sub = seq_pt.tracked_borrow_subrange_mut(start, end);
        let sub_ref = sub;
        let tracked ret = Self::borrow_mut_values(sub);

        let new_self = *final(self_ref);
        assert forall|i: int| #![trigger new_self[i]] 0 <= i < new_self.len() implies {
            &&& new_self[i].wf()
            &&& new_self[i].wf_basic()
            &&& new_self[i].ptr() == old_self[i].ptr()
            &&& start <= i < end ==> new_self[i] == final(sub_ref)[i - start]
            &&& !(start <= i < end) ==> new_self[i] == old_self[i]
        } by {}
        ret
    }

    /// Converts a `SeqPointsTo<T, PointsTo<T>>` into a `PointsToUntyped` covering the same bytes,
    /// together with the `TypedValue<T>` of each element.
    /// (Use `into_untyped` instead if you don't need the typed values.)
    ///
    /// The resulting `PointsToUntyped` has the same address and provenance
    /// and a length of `self.len() * size_of::<T>()`,
    /// and preserves the abstract bytes.
    /// The returned `tracked typed_value` holds the typed contents from this memory,
    /// which can later be used to convert the `pt_untyped` permission back to a typed permission
    /// (see `SeqPointsTo::from_untyped_with_typed_value`).
    pub proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, typed_value):
        (PointsToUntyped, Seq<TypedValue<T>>))
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() * size_of::<T>()) as usize,
                },
            ),
            pt_untyped.bytes() == self.bytes(),
            typed_value == self.seq_typed_value(),
            pt_untyped.wf(),
        decreases self.len(),
    {
        let ghost old_self = self;
        if self.len() == 0 {
            assert(self.len() * size_of::<T>() == 0) by (nonlinear_arith)
                requires
                    self.len() == 0,
            ;
            let tracked pt_untyped = PointsToUntyped::zero_sized(
                ptr_mut_from_data::<()>(
                    PtrData {
                        addr: self.ptr()@.addr,
                        provenance: self.ptr()@.provenance,
                        metadata: (),
                    },
                ),
            );
            (pt_untyped, Seq::tracked_empty())
        } else {
            let tracked mut seq_pt = self.into_seq();
            let tracked last = seq_pt.tracked_pop();
            let tracked head = Self::from_seq(seq_pt, old_self.thin_ptr());
            let ghost old_head = head;
            let ghost old_last = last;
            let tracked (head_u8, mut head_typed_value) = head.into_untyped_with_typed_value();
            let tracked (last_u8, last_typed_value) = last.into_untyped_with_typed_value();
            head_typed_value.tracked_push(last_typed_value);
            let tracked pt_untyped = head_u8.join(last_u8);

            old_self.bytes_len();

            assert(head_typed_value =~= old_self.seq_typed_value()) by {
                assert forall|i: int| 0 <= i < old_self.len() implies head_typed_value[i]
                    == #[trigger] old_self.seq_typed_value()[i] by {}
            }
            (pt_untyped, head_typed_value)
        }
    }

    /// Creates a `SeqPointsTo<T, PointsTo<T>>` of length `capacity` from a `PointsToUntyped`,
    /// with the first `typed_value.len()` elements holding the given typed values,
    /// under the following conditions:
    ///
    /// (1) The pointer's address is aligned to `T`.
    ///
    /// (2) The length is exactly `capacity * size_of::<T>()`.
    ///
    /// (3) For each valid element in `typed_value`,
    ///     the corresponding abstract bytes for the `PointsToUntyped` can be decoded into its value.
    ///     `typed_value` may contain empty elements (these are ignored for purposes of decoding)
    ///     and can be a prefix of the total `capacity`
    ///     (in which case, the remaining memory is all logically uninitialized).
    ///
    /// The abstract bytes remain the same.
    /// This preserves the typed contents in memory on a roundtrip
    /// (see `SeqPointsTo::into_untyped_with_typed_value`).
    pub proof fn from_untyped_with_typed_value(
        tracked pt_untyped: PointsToUntyped,
        capacity: usize,
        tracked typed_value: Seq<TypedValue<T>>,
    ) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            PointsTo::<T>::satisfies_alignment(pt_untyped.ptr()@.addr),
            pt_untyped.len() == capacity * size_of::<T>(),
            typed_value.len() <= capacity,
            forall|i: int|
                0 <= i < typed_value.len() && typed_value[i].is_valid() ==> #[trigger] abs_decode::<
                    T,
                >(
                    pt_untyped.bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
                    &typed_value[i].value(),
                ),
        ensures
            out.ptr()@.addr == pt_untyped.ptr()@.addr,
            out.ptr()@.provenance == pt_untyped.ptr()@.provenance,
            out.len() == capacity,
            out.bytes() == pt_untyped.bytes(),
            forall|i: int|
                0 <= i < typed_value.len() ==> (#[trigger] out[i]).typed_value() == typed_value[i],
            out.wf(),
        decreases capacity,
    {
        let ghost old_untyped = pt_untyped;

        if capacity == 0 {
            assert(capacity * size_of::<T>() == 0) by (nonlinear_arith)
                requires
                    capacity == 0,
            ;
            let tracked out = Self::empty(pt_untyped.ptr() as *mut T);
            out
        } else {
            if size_of::<T>() != 0 {
                assert(capacity * size_of::<T>() != 0) by (nonlinear_arith)
                    requires
                        capacity != 0,
                        size_of::<T>() != 0,
                ;
                pt_untyped.provenance_not_none();
                pt_untyped.ptr_bounds();
            }
            assert(0 <= (capacity - 1) as nat * size_of::<T>() <= capacity * size_of::<T>())
                by (nonlinear_arith)
                requires
                    capacity > 0,
            ;
            PointsTo::<T>::lemma_satisfies_alignment_offset(
                pt_untyped.ptr()@.addr,
                (capacity - 1) as nat,
            );
            // Split into "head" and "tail", where tail is the last element's bytes
            let tracked (head, tail) = pt_untyped.split(
                ((capacity - 1) as nat * size_of::<T>()) as nat,
            );
            assert(tail.len() == size_of::<T>()) by (nonlinear_arith)
                requires
                    tail.len() + (capacity - 1) as nat * size_of::<T>() == capacity * size_of::<
                        T,
                    >(),
                    capacity > 0,
            ;

            // Convert the tail into a typed permission holding the last typed value, if supplied
            let tracked mut tail_pt = PointsTo::<T>::from_untyped(tail, ());
            let tracked mut head_typed_value = typed_value;
            if typed_value.len() == capacity {
                let tracked last = head_typed_value.tracked_pop();
                let i = (capacity - 1) as int;
                assert(tail_pt.bytes() =~= old_untyped.bytes().subrange(
                    i * size_of::<T>(),
                    (i + 1) * size_of::<T>(),
                ));
                tail_pt.put_typed_value(last);
            }
            let tail_ptr = tail_pt.ptr();
            let tail_bytes = tail_pt.bytes();
            let tracked mut tail_seq = Seq::tracked_empty();
            tail_seq.tracked_push(tail_pt);
            assert forall|i: int| 0 <= i < tail_seq.len() implies #[trigger] tail_seq[i].ptr()@.addr
                == tail_ptr@.addr + i * size_of::<T>() by {
                assert(0 * size_of::<T>() == 0) by (nonlinear_arith);
            }
            let tracked tail_typed = Self::from_seq(tail_seq, tail_ptr);

            // Invoke the inductive hypothesis on the head
            assert forall|i: int|
                0 <= i < head_typed_value.len()
                    && head_typed_value[i].is_valid() implies #[trigger] abs_decode::<T>(
                head.bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
                &head_typed_value[i].value(),
            ) by {
                assert(0 <= i * size_of::<T>() <= (i + 1) * size_of::<T>() <= (capacity - 1) as nat
                    * size_of::<T>()) by (nonlinear_arith)
                    requires
                        0 <= i < capacity - 1,
                ;
                old_untyped.bytes().lemma_slice_of_slice(
                    0,
                    ((capacity - 1) as nat * size_of::<T>()) as int,
                    i * size_of::<T>(),
                    (i + 1) * size_of::<T>(),
                );
            }
            let tracked head_typed = Self::from_untyped_with_typed_value(
                head,
                (capacity - 1) as usize,
                head_typed_value,
            );

            // Join head and tail
            assert(tail_typed.bytes() =~= tail_bytes) by {
                reveal_with_fuel(Seq::fold_left, 2);
            }
            let tracked out = head_typed.join(tail_typed);
            out
        }
    }

    /// Creates a `PointsToUntyped` from a `SeqPointsTo<T, PointsTo<T>>`
    /// with the same address and provenance
    /// and a length of `self.len() * size_of::<T>()`.
    /// If there are any typed values stored in memory, they are dropped here.
    /// (Use `into_untyped_with_typed_value` instead if you want to keep them.)
    pub proof fn into_untyped(tracked self) -> (tracked pt_untyped: PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() * size_of::<T>()) as usize,
                },
            ),
            pt_untyped.bytes() == self.bytes(),
            pt_untyped.wf(),
    {
        let tracked (pt_untyped, _) = self.into_untyped_with_typed_value();
        pt_untyped
    }

    /// Creates a `SeqPointsTo<T, PointsTo<T>>` of length `len`
    /// from a `PointsToUntyped` with the same address and provenance.
    /// The resulting permission will be empty (uninitialized).
    /// (Use `from_untyped_with_typed_value` instead if you want to supply typed values.)
    pub proof fn from_untyped(tracked pt_untyped: PointsToUntyped, len: usize) -> (tracked out:
        Self)
        requires
            pt_untyped.wf(),
            PointsTo::<T>::satisfies_alignment(pt_untyped.ptr()@.addr),
            pt_untyped.len() == len * size_of::<T>(),
        ensures
            out.ptr()@.addr == pt_untyped.ptr()@.addr,
            out.ptr()@.provenance == pt_untyped.ptr()@.provenance,
            out.len() == len,
            out.bytes() == pt_untyped.bytes(),
            out.is_fully_empty(),
            out.wf(),
    {
        let tracked mut out = Self::from_untyped_with_typed_value(
            pt_untyped,
            len,
            Seq::tracked_empty(),
        );
        // `from_untyped_with_typed_value` says nothing about the validity of elements past the
        // supplied `typed_value`, so empty all of them.
        let tracked _taken = out.take_typed_value_subrange(0, len as int);
        assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i].is_empty() by {
            out.typed_value_equiv(i);
        }
        out
    }

    /// Borrows the underlying `PointsToUntyped` permissions of the first `n` permissions,
    /// joined into a single `PointsToUntyped`.
    proof fn untyped_ref_join(tracked &self, n: nat) -> (tracked pt_untyped: &PointsToUntyped)
        requires
            self.wf(),
            n <= self.len(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (n * size_of::<T>()) as usize,
                },
            ),
            pt_untyped.bytes() == Self::bytes_inner(self.seq_pt().take(n as int)),
            pt_untyped.wf(),
        decreases n,
    {
        if n == 0 {
            let tracked empty = PointsToUntyped::zero_sized(
                ptr_mut_from_data::<()>(
                    PtrData {
                        addr: self.ptr()@.addr,
                        provenance: self.ptr()@.provenance,
                        metadata: (),
                    },
                ),
            );
            assert(n * size_of::<T>() == 0) by (nonlinear_arith)
                requires
                    n == 0,
            ;
            crate::vstd::modes::tracked_static_ref(empty)
        } else {
            let i = n - 1;

            // The prefix, joined
            let tracked a = self.untyped_ref_join(i as nat);

            // The last element
            let tracked b = self.tracked_seq_pt().tracked_borrow(i).as_untyped();

            assert(i * size_of::<T>() + size_of::<T>() == n * size_of::<T>()) by (nonlinear_arith)
                requires
                    i == n - 1,
            ;
            assert(self.seq_pt().take(n as int).drop_last() =~= self.seq_pt().take(i));
            PointsToUntyped::join_ref(a, b)
        }
    }

    /// Creates a reference to a `PointsToUntyped`
    /// from a reference to a `SeqPointsTo<T, PointsTo<T>>`,
    /// with the same address and provenance, a length of `self.len() * size_of::<T>()`,
    /// and the same abstract bytes.
    pub proof fn as_untyped(tracked &self) -> (tracked pt_untyped: &PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() * size_of::<T>()) as usize,
                },
            ),
            pt_untyped.bytes() == self.bytes(),
            pt_untyped.wf(),
    {
        broadcast use group_vstd_default;

        self.untyped_ref_join(self.len())
    }

    /// Mutably borrows the underlying `PointsToUntyped` permissions of all of `perms`, joined into
    /// a single `PointsToUntyped`, where the elements sit at consecutive addresses from `base`.
    /// If the result keeps its pointers and length, then each permission ends up empty and
    /// well-formed, and the permissions' bytes are the result's final bytes.
    proof fn untyped_mut_join(
        tracked perms: &mut Seq<PointsTo<T>>,
        base: *mut T,
    ) -> (tracked pt_untyped: &mut PointsToUntyped)
        requires
            base@.addr != 0,
            ptr_addr_in_bounds(base),
            forall|i: int|
                0 <= i < perms.len() ==> {
                    &&& #[trigger] perms[i].wf()
                    &&& perms[i].ptr()@.addr == base@.addr + i * size_of::<T>()
                    &&& perms[i].ptr()@.provenance == base@.provenance
                },
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: base@.addr,
                    provenance: base@.provenance,
                    metadata: (old(perms).len() * size_of::<T>()) as usize,
                },
            ),
            pt_untyped.bytes() == Self::bytes_inner(*old(perms)),
            pt_untyped.wf(),
            final(perms).len() == old(perms).len(),
            forall|i: int| 0 <= i < final(perms).len() ==> #[trigger] final(perms)[i].is_empty(),
            PointsToUntyped::ptrs_len_same(*pt_untyped, *final(pt_untyped)) ==> {
                &&& forall|i: int|
                    #![trigger final(perms)[i]]
                    0 <= i < final(perms).len() ==> {
                        &&& final(perms)[i].wf()
                        &&& final(perms)[i].ptr() == old(perms)[i].ptr()
                    }
                &&& Self::bytes_inner(*final(perms)) == final(pt_untyped).bytes()
            },
        decreases perms.len(),
    {
        broadcast use group_vstd_default;

        if perms.len() == 0 {
            let tracked empty = PointsToUntyped::zero_sized(
                ptr_mut_from_data::<()>(
                    PtrData { addr: base@.addr, provenance: base@.provenance, metadata: () },
                ),
            );
            crate::vstd::modes::tracked_static_mut_ref(empty)
        } else {
            let old_perms = *perms;
            let perms_ref = perms;
            let i = perms.len() - 1;
            assert(old_perms[i].wf());
            let tracked (init, last1) = perms.tracked_split_borrow_mut(i);
            let init_ref = init;
            assert forall|k: int| 0 <= k < init.len() implies {
                &&& #[trigger] init[k].wf()
                &&& init[k].ptr()@.addr == base@.addr + k * size_of::<T>()
                &&& init[k].ptr()@.provenance == base@.provenance
            } by {}

            // The prefix, joined
            let tracked a = Self::untyped_mut_join(init, base);

            // The last element
            let tracked b = last1.tracked_borrow_mut(0).as_untyped_mut();

            assert(i * size_of::<T>() + size_of::<T>() == old_perms.len() * size_of::<T>())
                by (nonlinear_arith)
                requires
                    i == old_perms.len() - 1,
            ;
            let tracked joined = PointsToUntyped::join_mut(a, b);
            let joined_ref = joined;

            // Final values
            if PointsToUntyped::ptrs_len_same(*joined_ref, *final(joined_ref)) {
                assert((*final(perms_ref)).drop_last() =~= *final(init_ref));
            }
            joined
        }
    }

    /// Creates a mutable reference to a `PointsToUntyped`
    /// from a mutable reference to a `SeqPointsTo<T, PointsTo<T>>`,
    /// with the same address and provenance and a length of `self.len() * size_of::<T>()`.
    /// If this permission carries any typed values, they are dropped here.
    pub proof fn as_untyped_mut(tracked &mut self) -> (tracked pt_untyped: &mut PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: old(self).ptr()@.addr,
                    provenance: old(self).ptr()@.provenance,
                    metadata: (old(self).len() * size_of::<T>()) as usize,
                },
            ),
            pt_untyped.bytes() == old(self).bytes(),
            pt_untyped.wf(),
            final(self).ptr() == old(self).ptr(),
            final(self).len() == old(self).len(),
            final(self).is_fully_empty(),
            // Criteria necessary for re-establishing invariants
            PointsToUntyped::ptrs_len_same(*pt_untyped, *final(pt_untyped)) ==> ({
                &&& final(self).bytes() == final(pt_untyped).bytes()
                &&& final(self).wf()
            }),
    {
        let base = self.thin_ptr();
        let tracked perms = self.tracked_seq_pt_mut();
        let tracked pt_untyped = Self::untyped_mut_join(perms, base);
        pt_untyped
    }

    /// Specializes `is_disjoint` to the case
    /// when the other permission is a `SeqPointsTo<S, PointsTo<S>>`.
    pub proof fn is_disjoint_seqpt<S>(
        tracked &mut self,
        tracked other: &SeqPointsTo<S, PointsTo<S>>,
    )
        requires
            self.len() != 0,
            other.len() != 0,
            size_of::<T>() != 0,
            size_of::<S>() != 0,
            self.wf(),
            other.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + final(self).len() * size_of::<T>() <= other.ptr()@.addr
                || other.ptr()@.addr + other.len() * size_of::<S>() <= final(self).ptr()@.addr,
    {
        broadcast use crate::vstd::arithmetic::mul::lemma_mul_nonzero;

        self.is_disjoint(other);
    }

    /// A `PointsTo<[T]>` is all valid or all empty,
    /// so a sequence with any empty element gives an empty slice permission.
    pub proof fn as_slice_pt(tracked &self) -> (tracked out: &PointsTo<[T]>)
        requires
            self.wf(),
        ensures
            out.ptr() == self.ptr(),
            out.bytes() == self.bytes(),
            self.is_valid() ==> out.typed_value().is_valid() && out.value() == self.seq_value(),
            !self.is_valid() ==> out.typed_value().is_empty(),
            out.wf(),
    {
        broadcast use group_vstd_default, abs_decode_slice;

        let n = self.len();
        let s = size_of::<T>() as int;
        let tracked pt_untyped = self.as_untyped();
        let tracked elems = self.borrow_typed_values(0, n);
        let tracked typed_value = TypedValue::<[T]>::from_elems_ref(elems);
        self.bytes_len();
        match typed_value {
            TypedValue::Valid(b) => {
                let tracked value: &[T] = b;
                assert forall|i: int| 0 <= i < n implies #[trigger] self[i].is_valid() by {
                    assert(elems[i].is_valid());
                }
                self.bytes_decode();
                assert forall|i: int| 0 <= i < value@.len() implies abs_decode::<T>(
                    pt_untyped.bytes().subrange(i * s, (i + 1) * s),
                    &#[trigger] value@[i],
                ) by {}
                PointsTo::<[T]>::from_untyped_with_value_ref(pt_untyped, value)
            },
            TypedValue::Empty => PointsTo::<[T]>::from_untyped_ref(pt_untyped, n as usize),
        }
    }

    /// Mutably borrows the underlying `PointsToUntyped` permissions of all of `perms`,
    /// joined into a single `PointsToUntyped`, and the typed value of each,
    /// where the elements sit at consecutive addresses from `base`.
    /// Each element's final typed value is the final value of its borrowed typed value.
    /// If the joined permission keeps its pointers and length,
    /// each element keeps its pointer, holds its part of the joined permission's final bytes,
    /// and is well-formed if its final typed value satisfies its validity constraints.
    proof fn raw_parts_mut(tracked perms: &mut Seq<PointsTo<T>>, base: *mut T) -> (tracked (
        pt_untyped,
        typed_values,
    ): (&mut PointsToUntyped, Seq<&mut TypedValue<T>>))
        requires
            base@.addr != 0,
            ptr_addr_in_bounds(base),
            forall|i: int|
                0 <= i < perms.len() ==> {
                    &&& #[trigger] perms[i].wf()
                    &&& perms[i].ptr()@.addr == base@.addr + i * size_of::<T>()
                    &&& perms[i].ptr()@.provenance == base@.provenance
                },
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: base@.addr,
                    provenance: base@.provenance,
                    metadata: (old(perms).len() * size_of::<T>()) as usize,
                },
            ),
            pt_untyped.bytes() == Self::bytes_inner(*old(perms)),
            pt_untyped.wf(),
            typed_values.len() == old(perms).len(),
            final(perms).len() == old(perms).len(),
            forall|i: int|
                #![trigger typed_values[i]]
                0 <= i < typed_values.len() ==> {
                    &&& *typed_values[i] == old(perms)[i].typed_value()
                    &&& final(perms)[i].typed_value() == *final(typed_values[i])
                },
            PointsToUntyped::ptrs_len_same(*pt_untyped, *final(pt_untyped)) ==> {
                &&& Self::bytes_inner(*final(perms)) == final(pt_untyped).bytes()
                &&& forall|i: int|
                    #![trigger final(perms)[i]]
                    0 <= i < final(perms).len() ==> {
                        &&& final(perms)[i].ptr() == old(perms)[i].ptr()
                        &&& final(perms)[i].bytes() == final(pt_untyped).bytes().subrange(
                            i * size_of::<T>(),
                            (i + 1) * size_of::<T>(),
                        )
                        &&& final(perms)[i].valid_value() ==> final(perms)[i].wf()
                    }
            },
        decreases perms.len(),
    {
        broadcast use group_vstd_default;

        if perms.len() == 0 {
            let tracked empty = PointsToUntyped::zero_sized(
                ptr_mut_from_data::<()>(
                    PtrData { addr: base@.addr, provenance: base@.provenance, metadata: () },
                ),
            );
            (crate::vstd::modes::tracked_static_mut_ref(empty), Seq::tracked_empty())
        } else {
            let s = size_of::<T>() as int;
            let old_perms = *perms;
            let perms_ref = perms;
            let k = perms.len() - 1;
            assert(old_perms[k].wf());
            let tracked (init, last) = perms.tracked_split_borrow_mut(k);
            let init_ref = init;
            assert forall|i: int| 0 <= i < init.len() implies {
                &&& #[trigger] init[i].wf()
                &&& init[i].ptr()@.addr == base@.addr + i * s
                &&& init[i].ptr()@.provenance == base@.provenance
            } by {}

            // The prefix
            let tracked (a, mut typed_values) = Self::raw_parts_mut(init, base);
            let a_ref = a;

            // The last element
            let tracked elt = last.tracked_borrow_mut(0);
            let tracked unaligned = elt.as_unaligned_mut();
            let tracked (b, typed_value) = unaligned.as_raw_parts_mut();
            assert(k * s + s == old_perms.len() * s) by (nonlinear_arith)
                requires
                    k == old_perms.len() - 1,
            ;
            let tracked joined = PointsToUntyped::join_mut(a, b);
            let joined_ref = joined;
            typed_values.tracked_push(typed_value);

            // Final values
            assert(PointsToUntyped::ptrs_len_same(*joined_ref, *final(joined_ref)) ==> {
                &&& Self::bytes_inner(*final(perms_ref)) == final(joined_ref).bytes()
                &&& forall|i: int|
                    #![trigger final(perms_ref)[i]]
                    0 <= i < final(perms_ref).len() ==> {
                        &&& final(perms_ref)[i].ptr() == old_perms[i].ptr()
                        &&& final(perms_ref)[i].bytes() == final(joined_ref).bytes().subrange(
                            i * s,
                            (i + 1) * s,
                        )
                        &&& final(perms_ref)[i].valid_value() ==> final(perms_ref)[i].wf()
                    }
            }) by {
                if PointsToUntyped::ptrs_len_same(*joined_ref, *final(joined_ref)) {
                    assert((*final(perms_ref)).drop_last() =~= *final(init_ref));
                    assert forall|i: int| 0 <= i < final(perms_ref).len() implies {
                        &&& #[trigger] final(perms_ref)[i].ptr() == old_perms[i].ptr()
                        &&& final(perms_ref)[i].bytes() == final(joined_ref).bytes().subrange(
                            i * s,
                            (i + 1) * s,
                        )
                        &&& final(perms_ref)[i].valid_value() ==> final(perms_ref)[i].wf()
                    } by {
                        if i < k {
                            assert(0 <= i * s <= (i + 1) * s <= k * s) by (nonlinear_arith)
                                requires
                                    0 <= i,
                                    i + 1 <= k,
                                    s >= 0,
                            ;
                        }
                    }
                }
            }
            (joined, typed_values)
        }
    }

    /// As for `as_slice_pt`, a sequence with any empty element gives an empty slice permission.
    /// When the borrow ends,
    /// a valid slice value of the same length is distributed back to the elements;
    /// otherwise every element ends empty
    /// (the values of any valid elements are dropped).
    /// If the slice permission keeps its pointers and length,
    /// with its value still satisfying its validity constraints (`ptrs_len_same_valid_value`),
    /// the sequence holds its bytes and is well-formed.
    pub proof fn as_slice_pt_mut(tracked &mut self) -> (tracked out: &mut PointsTo<[T]>)
        requires
            self.wf(),
        ensures
    // Initially: as for `as_slice_pt`.

            out.ptr() == old(self).ptr(),
            out.bytes() == old(self).bytes(),
            old(self).is_valid() ==> out.typed_value().is_valid() && out.value() == old(
                self,
            ).seq_value(),
            !old(self).is_valid() ==> out.typed_value().is_empty(),
            out.wf(),
            // Finally: the pointer, length and typed values, unconditionally.
            final(self).ptr() == old(self).ptr(),
            final(self).len() == old(self).len(),
            final(out).typed_value().is_valid() && final(out).value().len() == old(self).len()
                ==> final(self).is_valid() && final(self).seq_value() == final(out).value(),
            !(final(out).typed_value().is_valid() && final(out).value().len() == old(self).len())
                ==> final(self).is_fully_empty(),
            // Criteria necessary for re-establishing invariants
            // (the bytes too, since `join_mut` ties them back only under `ptrs_len_same`).
            <PointsTo<[T]> as PTTypedValue>::ptrs_len_same_valid_value(*out, *final(out)) ==> {
                &&& final(self).bytes() == final(out).bytes()
                &&& final(self).wf()
            },
    {
        broadcast use group_vstd_default, abs_decode_slice;

        let old_self = *self;
        let self_ref = self;
        let n = self.len();
        let s = size_of::<T>() as int;
        self.bytes_len();
        self.bytes_decode();
        let base = self.thin_ptr();
        let tracked perms = self.tracked_seq_pt_mut();
        let perms_ref = perms;
        let tracked (pt_untyped, typed_values) = Self::raw_parts_mut(perms, base);
        let elems = typed_values;
        let tracked typed_value = TypedValue::<[T]>::from_elems_mut(typed_values);
        let tracked unaligned = PointsToUnaligned::<[T]>::from_raw_parts_mut(
            pt_untyped,
            typed_value,
            n as usize,
        );

        // The elements' typed values
        assert forall|i: int| 0 <= i < n implies *#[trigger] elems[i]
            == old_self.seq_typed_value()[i] && *elems[i] == old_self[i].typed_value() by {
            old_self.typed_value_equiv(i);
        }

        // The slice permission is well-formed
        if unaligned.typed_value().is_valid() {
            let value = unaligned.typed_value().value_ref();
            assert forall|i: int| 0 <= i < value@.len() implies abs_decode::<T>(
                unaligned.bytes().subrange(i * s, (i + 1) * s),
                &#[trigger] value@[i],
            ) by {
                assert(elems[i].is_valid());
            }
            assert forall|i: int| 0 <= i < n implies #[trigger] old_self[i].is_valid() by {
                assert(elems[i].is_valid());
            }
        }
        let tracked out = unaligned.as_aligned_mut();
        let out_ref = out;

        // Final values
        let new_self = *final(self_ref);
        assert forall|i: int| 0 <= i < n implies #[trigger] new_self[i].typed_value()
            == *final(elems[i]) by {
            assert(new_self[i] == final(perms_ref)[i]);
        }
        if final(out_ref).typed_value().is_valid() && final(out_ref).value().len() == n {
            assert(new_self.seq_value() =~= final(out_ref).value());
        }
        if <PointsTo<[T]> as PTTypedValue>::ptrs_len_same_valid_value(*out_ref, *final(out_ref)) {
            let final_unaligned = final(out_ref).pt_unaligned();
            final_unaligned.bytes_decode();
            assert forall|i: int| #![trigger new_self[i]] 0 <= i < n implies new_self[i].wf()
                && new_self[i].wf_basic() by {
                assert(new_self[i] == final(perms_ref)[i]);
                if final_unaligned.typed_value().is_valid() {
                    assert(abs_decode::<T>(
                        final_unaligned.bytes().subrange(i * s, (i + 1) * s),
                        &final_unaligned.value()[i],
                    ));
                }
            }
        }
        out
    }
}

// Not in `group_vstd_default`.
// While porting, code that needs these lemmas may need an explicit `broadcast use`.
pub broadcast group group_points_to_collections_lemmas {
    SeqPointsTo::lemma_ptrs_len_same_valid_value,
}

} // verus!
