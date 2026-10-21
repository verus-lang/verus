#![allow(unused_imports)]

use super::*;

verus! {

broadcast use {
    crate::vstd::raw_ptr_final::ptr_model::group_raw_ptr_axioms,
    crate::vstd::layout::group_layout_axioms,
    crate::vstd::seq::group_seq_axioms,
};

impl<T: ?Sized, P: PTProperties + FixedSize> PTProperties for SeqPointsTo<T, P> {
    /// Non-nullness is guaranteed by the invariant.
    proof fn is_nonnull(tracked &self) {
    }

    /// If the size is non-zero, the length must be nonzero.
    /// Then this follows from the `provenance_not_none` property of an individual `P`.
    proof fn provenance_not_none(tracked &self) {
        self.seq_pt.tracked_borrow(0).size_eq_const_size();
        self.seq_pt.tracked_borrow(0).provenance_not_none();
    }

    proof fn ptr_bounds(tracked &self) {
        if self.len() > 0 {
            self.seq_pt.tracked_borrow(self.len() - 1).ptr_bounds();
            self.seq_pt.tracked_borrow(self.len() - 1).size_eq_const_size();
            crate::vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                P::const_size() as int,
                (self.len() - 1) as int,
                1,
            );
        }
    }

    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    ) {
        let self_addr = self.ptr()@.addr as int;
        let other_addr = other.ptr()@.addr as int;
        let csize = P::const_size() as int;
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
            crate::vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(csize, len - 1, 1);
        } else {
            // `other` starts strictly inside `self`'s range: find the element `k`
            // whose byte range contains `other`'s start address, and derive a
            // contradiction from the fact that it can't possibly be disjoint from
            // `other` (since `other`'s own start address lies within it).
            let k = (other_addr - self_addr) / csize;
            crate::vstd::arithmetic::div_mod::lemma_fundamental_div_mod(other_addr - self_addr, csize);
            crate::vstd::arithmetic::div_mod::lemma_remainder(other_addr - self_addr, csize);
            crate::vstd::arithmetic::div_mod::lemma_multiply_divide_lt(
                other_addr - self_addr,
                csize,
                len,
            );
            crate::vstd::arithmetic::div_mod::lemma_div_pos_is_pos(other_addr - self_addr, csize);
            self.seq_pt.tracked_borrow_mut(k).size_eq_const_size();
            self.seq_pt.tracked_borrow_mut(k).is_disjoint(other);
        }
    }

    /// `new` has the same pointer and length as `old`, and each element of `new` keeps the
    /// corresponding element of `old`'s pointer and satisfies its `ptrs_len_same_valid`.
    open spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& new.len() == old.len()
        &&& forall|i: int|
            #![trigger new[i]]
            0 <= i < new.len() ==> P::ptrs_len_same_valid(old[i], new[i]) && new[i].ptr()
                == old[i].ptr()
    }

    /// Each element stays `wf_basic` by the element type's `stays_wf_basic`.
    proof fn stays_wf_basic(old: Self, new: Self) {
        assert forall|i: int| 0 <= i < new.len() implies #[trigger] new[i].wf_basic() by {
            P::stays_wf_basic(old[i], new[i]);
        }
    }
}

impl PointsToUntyped {
    /// If `old` is well-formed and `new` has the same pointers and length
    /// (`ptrs_len_same_valid`), then `new` is well-formed.
    pub proof fn stays_wf(old: Self, new: Self)
        requires
            old.wf(),
            Self::ptrs_len_same_valid(old, new),
        ensures
            new.wf(),
    {
        Self::stays_wf_basic(old, new);
    }

    /// If `old` and `new` are both well-formed with the same pointer, then `new` keeps `old`'s
    /// pointers and length.
    pub broadcast proof fn lemma_ptrs_len_same_valid_untyped(old: Self, new: Self)
        requires
            old.wf(),
            new.wf(),
            new.ptr() == old.ptr(),
        ensures
            #[trigger] Self::ptrs_len_same_valid(old, new),
    {
        assert forall|j: int| 0 <= j < new.len() implies #[trigger] new[j].ptr() == old[j].ptr() by {
            assert(new[j].ptr()@.addr == old[j].ptr()@.addr);
        }
    }

    /// If `T` is zero sized, then we can construct a `PointsToUntyped` from any non-null pointer.
    /// The range of memory pointed to by this permission will be empty.
    pub proof fn zero_sized<T>(ptr: *mut T) -> (tracked perm: Self)
        requires
            ptr@.addr != 0,
            size_of::<T>() == 0,
            ptr_addr_in_bounds(ptr),
        ensures
            perm.ptr()@.addr == ptr@.addr,
            perm.ptr()@.provenance == ptr@.provenance,
            perm.bytes().len() == size_of::<T>(),
            perm.wf(),
    {
        broadcast use group_vstd_default;

        let byte_ptr: *mut [u8] = ptr_mut_from_data(
            PtrData::<[u8]> { addr: ptr@.addr, provenance: ptr@.provenance, metadata: 0 },
        );
        SeqPointsTo { seq_pt: Seq::tracked_empty(), ptr: Ghost(byte_ptr) }
    }

    /// Specializes `is_disjoint` to the case when the other permission is a `PointsToUntyped`.
    pub proof fn is_disjoint_untyped(tracked &mut self, tracked other: &PointsToUntyped)
        requires
            self.len() != 0,
            other.len() != 0,
            self.wf(),
            other.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + final(self).len() <= other.ptr() as int || other.ptr() as int
                + other.len() <= final(self).ptr() as int,
    {
        broadcast use group_vstd_default;

        assert(self.len() == self.size());
        assert(other.size() == other.len() * other.seq_pt()[0].size());
        self.is_disjoint(other);
    }

    /// Splits the `PointsToUntyped` into two permissions at the index boundary `mid`.
    /// The first covers bytes `[0, mid)` and the second covers bytes `[mid, len)`.
    pub proof fn split(tracked self, mid: nat) -> (tracked (first, second): (Self, Self))
        requires
            0 <= mid <= self.len(),
            self.wf(),
        ensures
            first.seq_pt() == self.seq_pt().take(mid as int),
            second.seq_pt() == self.seq_pt().skip(mid as int),
            first.bytes() == self.bytes().take(mid as int),
            second.bytes() == self.bytes().skip(mid as int),
            first.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: mid as usize,
                },
            ),
            second.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: (self.ptr()@.addr + mid) as usize,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() - mid) as usize,
                },
            ),
            first.wf(),
            second.wf(),
    {
        broadcast use group_vstd_default;

        if self.len() != 0 {
            self.provenance_not_none();
            self.ptr_bounds();
        }

        let tracked mut seq_pt = self.seq_pt;
        let tracked other = seq_pt.tracked_skip(mid as int);

        let tracked first = SeqPointsTo {
            seq_pt: seq_pt,
            ptr: Ghost(
                ptr_mut_from_data::<[u8]>(
                    PtrData {
                        addr: self.ptr()@.addr,
                        provenance: self.ptr()@.provenance,
                        metadata: mid as usize,
                    },
                ),
            ),
        };
        let tracked second = SeqPointsTo {
            seq_pt: other,
            ptr: Ghost(
                ptr_mut_from_data::<[u8]>(
                    PtrData {
                        addr: (self.ptr()@.addr + mid) as usize,
                        provenance: self.ptr()@.provenance,
                        metadata: (self.len() - mid) as usize,
                    },
                ),
            ),
        };
        (first, second)
    }

    /// Splits a shared borrow of a `PointsToUntyped` into shared borrows of bytes `[0, mid)` and
    /// `[mid, len)`. This is the shared-borrow analogue of `split`.
    pub proof fn split_ref(tracked &self, mid: nat) -> (tracked (first, second): (&Self, &Self))
        requires
            0 <= mid <= self.len(),
            self.wf(),
        ensures
            first.seq_pt() == self.seq_pt().take(mid as int),
            second.seq_pt() == self.seq_pt().skip(mid as int),
            first.bytes() == self.bytes().take(mid as int),
            second.bytes() == self.bytes().skip(mid as int),
            first.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: mid as usize,
                },
            ),
            second.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: (self.ptr()@.addr + mid) as usize,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() - mid) as usize,
                },
            ),
            first.wf(),
            second.wf(),
    {
        broadcast use group_vstd_default;

        if self.len() != 0 {
            self.provenance_not_none();
            self.ptr_bounds();
        }
        let p1 = ptr_mut_from_data::<[u8]>(
            PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: mid as usize,
            },
        );
        let p2 = ptr_mut_from_data::<[u8]>(
            PtrData {
                addr: (self.ptr()@.addr + mid) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (self.len() - mid) as usize,
            },
        );
        let tracked s1 = self.seq_pt.tracked_borrow_subrange(0, mid as int);
        let tracked s2 = self.seq_pt.tracked_borrow_subrange(mid as int, self.len() as int);
        let tracked first = shr_ref_struct_wrap(
            s1,
            &Self { seq_pt: *s1, ptr: Ghost(p1) },
            "",
            "seq_pt",
        );
        let tracked second = shr_ref_struct_wrap(
            s2,
            &Self { seq_pt: *s2, ptr: Ghost(p2) },
            "",
            "seq_pt",
        );
        (first, second)
    }

    // Commented out along with the `wrap_mut` axiom (on the generic `SeqPointsTo` impl),
    // which this was proved from; the soundness of `wrap_mut` is still under consideration.
    // /// Splits a mutable borrow of a `PointsToUntyped` into mutable borrows of bytes `[0, mid)` and
    // /// `[mid, len)`. This is the mutable-borrow analogue of `split`.
    // ///
    // /// If both halves stay well-formed with the same pointers, then `self` is also still
    // /// well-formed with the same pointer, holding the halves' final permissions concatenated.
    // pub proof fn split_mut(tracked &mut self, mid: nat) -> (tracked (first, second): (
    //     &mut Self,
    //     &mut Self,
    // ))
    //     requires
    //         0 <= mid <= self.len(),
    //         self.wf(),
    //     ensures
    //         first.seq_pt() == old(self).seq_pt().take(mid as int),
    //         second.seq_pt() == old(self).seq_pt().skip(mid as int),
    //         first.bytes() == old(self).bytes().take(mid as int),
    //         second.bytes() == old(self).bytes().skip(mid as int),
    //         first.ptr() == ptr_mut_from_data::<[u8]>(
    //             PtrData {
    //                 addr: old(self).ptr()@.addr,
    //                 provenance: old(self).ptr()@.provenance,
    //                 metadata: mid as usize,
    //             },
    //         ),
    //         second.ptr() == ptr_mut_from_data::<[u8]>(
    //             PtrData {
    //                 addr: (old(self).ptr()@.addr + mid) as usize,
    //                 provenance: old(self).ptr()@.provenance,
    //                 metadata: (old(self).len() - mid) as usize,
    //             },
    //         ),
    //         first.wf(),
    //         second.wf(),
    //         // Criteria necessary for re-establishing invariants
    //         ({
    //             &&& final(first).wf()
    //             &&& final(first).ptr() == first.ptr()
    //             &&& final(second).wf()
    //             &&& final(second).ptr() == second.ptr()
    //         }) ==> {
    //             &&& final(self).wf()
    //             &&& final(self).ptr() == old(self).ptr()
    //             &&& final(self).seq_pt() == final(first).seq_pt() + final(second).seq_pt()
    //             &&& final(self).bytes() == final(first).bytes() + final(second).bytes()
    //         },
    // {
    //     let old_self = *self;
    //     if old_self.len() != 0 {
    //         self.provenance_not_none();
    //         self.ptr_bounds();
    //     }
    //     let p1 = ptr_mut_from_data::<[u8]>(
    //         PtrData {
    //             addr: old_self.ptr()@.addr,
    //             provenance: old_self.ptr()@.provenance,
    //             metadata: mid as usize,
    //         },
    //     );
    //     let p2 = ptr_mut_from_data::<[u8]>(
    //         PtrData {
    //             addr: (old_self.ptr()@.addr + mid) as usize,
    //             provenance: old_self.ptr()@.provenance,
    //             metadata: (old_self.len() - mid) as usize,
    //         },
    //     );
    //     let tracked (s1, s2) = self.seq_pt.tracked_split_borrow_mut(mid as int);
    //     let tracked first = Self::wrap_mut(s1, p1);
    //     let tracked second = Self::wrap_mut(s2, p2);
    //     (first, second)
    // }

    /// Concatenates `PointsToUntyped` permissions `self` and `other`,
    /// provided their pointers have the same provenance
    /// and `other`'s pointer starts at the end of `self`'s range.
    pub proof fn join(tracked self, tracked other: Self) -> (tracked joined: Self)
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
    {
        broadcast use group_vstd_default;

        if self.len() != 0 {
            self.provenance_not_none();
            self.ptr_bounds();
        }
        if other.len() != 0 {
            other.provenance_not_none();
            other.ptr_bounds();
        }
        let tracked mut seq_pt = self.seq_pt;
        seq_pt.tracked_add(other.seq_pt);

        let tracked joined = SeqPointsTo {
            seq_pt: seq_pt,
            ptr: Ghost(
                ptr_mut_from_data::<[u8]>(
                    PtrData {
                        addr: self.ptr()@.addr,
                        provenance: self.ptr()@.provenance,
                        metadata: (self.len() + other.len()) as usize,
                    },
                ),
            ),
        };
        joined
    }
}

impl<T> PTProperties for PointsToUnaligned<T> {
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
    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    ) {
        self.pt_untyped.is_disjoint(other);
    }

    /// `new` has the same pointer and the same underlying `PointsToUntyped` pointers and length as
    /// `old`, and `new`'s bytes still decode to `new`'s value if `new` has a valid `TypedValue`.
    open spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUntyped::ptrs_len_same_valid(old.pt_untyped(), new.pt_untyped())
        &&& new.is_valid() ==> abs_decode::<T>(new.bytes(), &new.value())
    }

    /// Delegates to `PointsToUntyped::stays_wf` for the underlying bytes.
    proof fn stays_wf_basic(old: Self, new: Self) {
        PointsToUntyped::stays_wf(old.pt_untyped(), new.pt_untyped());
    }
}

impl<T> PointsToUnaligned<T> {
    /// If `old` is well-formed and `new` has the same pointers and length and still satisfies
    /// decode validity (`ptrs_len_same_valid`), then `new` is well-formed.
    pub proof fn stays_wf(old: Self, new: Self)
        requires
            old.wf(),
            Self::ptrs_len_same_valid(old, new),
        ensures
            new.wf(),
    {
        Self::stays_wf_basic(old, new);
    }

    /// Convert PointsToUnaligned to an aligned PointsTo.
    /// Requires the pointer address to be properly aligned.
    ///
    /// Ensures pointer locations remain the same, and memory
    /// initializations states remain the same.
    pub proof fn into_aligned(tracked self) -> (tracked perm: PointsTo<T>)
        requires
            self.wf(),
            self.ptr()@.addr as int % align_of::<T>() as int == 0,
        ensures
            perm@ == self@,
            perm.wf(),
    {
        broadcast use layout_of_sized;

        PointsTo { pt_unaligned: self }
    }

    /// Borrow an unaligned PointsToUnaligned as an aligned PointsTo.
    /// Requires the pointer address to be properly aligned.
    ///
    /// Ensures pointer locations remain the same, and memory
    /// initializations states remain the same.
    pub proof fn as_aligned(tracked &self) -> (tracked perm: &PointsTo<T>)
        requires
            self.wf(),
            self.ptr()@.addr as int % align_of::<T>() as int == 0,
        ensures
            perm@ == self@,
            perm.wf(),
    {
        shr_ref_struct_wrap(self, &PointsTo { pt_unaligned: *self }, "", "pt_unaligned")
    }

    /// If `T` is zero sized, then we can construct an uninitialized `PointsToUnaligned<T>`
    /// from any non-null pointer whose address (and, if known, provenance) is otherwise valid.
    /// The range of memory pointed to by this permission will be empty.
    pub proof fn zero_sized(ptr: *mut T) -> (tracked perm: Self)
        requires
            ptr@.addr != 0,
            size_of::<T>() == 0,
            ptr_addr_in_bounds(ptr),
        ensures
            perm.ptr()@.addr == ptr@.addr,
            perm.ptr()@.provenance == ptr@.provenance,
            perm.is_empty(),
            perm.bytes().len() == size_of::<T>(),
            perm.wf(),
    {
        let tracked untyped: PointsToUntyped = PointsToUntyped::zero_sized(ptr);
        PointsToUnaligned {
            val: TypedValue::Empty,
            pt_untyped: untyped,
            metadata: Ghost(ptr@.metadata),
        }
    }

    /// Specializes `is_disjoint` to the case when the other permission is a `PointsToUnaligned<S>`.
    pub proof fn is_disjoint_unaligned<S>(tracked &mut self, tracked other: &PointsToUnaligned<S>)
        requires
            size_of::<T>() != 0,
            size_of::<S>() != 0,
            self.wf(),
            other.wf(),
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

impl<T> PTProperties for PointsToUnaligned<[T]> {
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
    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    ) {
        self.pt_untyped.is_disjoint(other);
    }

    /// `new` has the same pointer (so the same metadata) as `old`,
    /// and the same underlying `PointsToUntyped` pointers and length.
    /// If `new` is valid, its slice has `old`'s number of elements
    /// (the length doesn't change, even if the typed value does),
    /// and `new`'s bytes decode to it.
    open spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUntyped::ptrs_len_same_valid(old.pt_untyped(), new.pt_untyped())
        &&& new.is_valid() ==> {
            &&& new.typed_value().value()@.len() == old.metadata()
            &&& abs_decode::<[T]>(new.bytes(), new.typed_value().value())
        }
    }

    /// Delegates to `PointsToUntyped::stays_wf` for the underlying bytes.
    proof fn stays_wf_basic(old: Self, new: Self) {
        PointsToUntyped::stays_wf(old.pt_untyped(), new.pt_untyped());
    }
}

impl<T> PTProperties for PointsTo<T> {
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
    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    ) {
        self.pt_unaligned.is_disjoint(other);
    }

    /// `new` has the same pointer as `old`, and they satisfy the `PointsToUnaligned` requirements
    /// for preserving well-formed-ness.
    open spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUnaligned::<T>::ptrs_len_same_valid(old.pt_unaligned(), new.pt_unaligned())
    }

    /// Delegates to `PointsToUnaligned::stays_wf`.
    proof fn stays_wf_basic(old: Self, new: Self) {
        PointsToUnaligned::<T>::stays_wf(old.pt_unaligned(), new.pt_unaligned());
    }
}

impl<T> PTProperties for PointsTo<[T]> {
    /// Non-nullness follows from the underlying `PointsToUnaligned`'s invariant,
    /// since `self.ptr()` and `self.pt_unaligned().ptr()` are the same pointer.
    proof fn is_nonnull(tracked &self) {
        self.pt_unaligned.is_nonnull();
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
    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    ) {
        self.pt_unaligned.is_disjoint(other);
    }

    /// `new` has the same pointer as `old`, and they satisfy the `PointsToUnaligned` requirements
    /// for preserving well-formed-ness.
    open spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUnaligned::<[T]>::ptrs_len_same_valid(old.pt_unaligned(), new.pt_unaligned())
    }

    /// Delegates to `PointsToUnaligned`'s `stays_wf_basic`.
    proof fn stays_wf_basic(old: Self, new: Self) {
        PointsToUnaligned::<[T]>::stays_wf_basic(old.pt_unaligned(), new.pt_unaligned());
    }
}

impl<T> PointsTo<T> {
    /// If `old` is well-formed and `new` has the same pointers and length and still satisfies
    /// decode validity (`ptrs_len_same_valid`), then `new` is well-formed.
    pub proof fn stays_wf(old: Self, new: Self)
        requires
            old.wf(),
            Self::ptrs_len_same_valid(old, new),
        ensures
            new.wf(),
    {
        Self::stays_wf_basic(old, new);
    }

    /// If `old` and `new` are both well-formed with the same pointer, then `new` keeps `old`'s
    /// underlying pointers and length, and still satisfies decode validity.
    pub broadcast proof fn lemma_ptrs_len_same_valid(old: Self, new: Self)
        requires
            old.wf(),
            new.wf(),
            new.ptr() == old.ptr(),
        ensures
            #[trigger] Self::ptrs_len_same_valid(old, new),
    {
        let old_u = old.pt_unaligned().pt_untyped();
        let new_u = new.pt_unaligned().pt_untyped();
        assert forall|j: int| 0 <= j < new_u.len() implies #[trigger] new_u[j].ptr() == old_u[j].ptr()
            by {
            assert(new_u[j].ptr()@.addr == old_u[j].ptr()@.addr);
            assert(new_u[j].ptr()@.provenance == old_u[j].ptr()@.provenance);
        }
    }

    /// A `PointsTo<T>` is always aligned.
    pub proof fn is_aligned(tracked &self)
        requires
            self.wf(),
        ensures
            self.ptr()@.addr as nat % align_of::<T>() == 0,
    {
    }

    /// From a non-null, aligned pointer to a zero-sized type, we can construct an
    /// uninitialized `PointsTo<T>`. The memory range pointed to by this pointer will be empty.
    pub proof fn zero_sized(ptr: *mut T) -> (tracked perm: PointsTo<T>)
        requires
            ptr@.addr != 0,
            ptr@.addr as nat % align_of::<T>() == 0,
            ptr_addr_in_bounds(ptr),
            size_of::<T>() == 0,
        ensures
            perm.ptr() == ptr,
            perm.is_empty(),
            perm.bytes().len() == size_of::<T>(),
            perm.wf(),
    {
        let tracked pt_unaligned = PointsToUnaligned::<T>::zero_sized(ptr);
        PointsTo { pt_unaligned }
    }

    /// Specializes `is_disjoint` to the case when the other permission is a `PointsTo<S>`.
    pub proof fn is_disjoint_pointsto<S>(tracked &mut self, tracked other: &PointsTo<S>)
        requires
            size_of::<T>() != 0,
            size_of::<S>() != 0,
            self.wf(),
            other.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + size_of::<T>() <= other.ptr() as int || other.ptr() as int
                + size_of::<S>() <= final(self).ptr() as int,
    {
        self.size_eq_const_size();
        other.size_eq_const_size();
        self.is_disjoint(other);
    }

    /// Convert an aligned `PointsTo` to an unaligned `PointsToUnaligned`.
    /// This is always safe since aligned is stricter than unaligned.
    ///
    /// Ensures pointer locations remain the same, and memory
    /// initializations states remain the same.
    pub proof fn into_unaligned(tracked self) -> (tracked perm: PointsToUnaligned<T>)
        requires
            self.wf(),
        ensures
            perm@ == self@,
            perm.wf(),
    {
        self.pt_unaligned
    }

    /// Borrow an aligned `PointsTo` as an unaligned `PointsToUnaligned`.
    /// This is always safe since aligned is stricter than unaligned.
    ///
    /// Ensures pointer locations remain the same, and memory
    /// initializations states remain the same.
    pub proof fn as_unaligned(tracked &self) -> (tracked perm: &PointsToUnaligned<T>)
        requires
            self.wf(),
        ensures
            perm@ == self@,
            perm.wf(),
    {
        &self.pt_unaligned
    }

    /// If the memory is valid, then the bytes must decode into the given value in memory.
    pub broadcast proof fn bytes_decode(&self)
        requires
            self.wf(),
        ensures
            self.is_valid() ==> #[trigger] abs_decode::<T>(self.bytes(), &self.value()),
            self.bytes().len() == size_of::<T>(),
    {
    }

    /// Converts a `PointsTo<T>` into a `PointsToUntyped`, an untyped permission to the same
    /// underlying bytes, together with the `TypedValue<T>` that `self` held.
    /// (Use `into_untyped` instead if you don't need the typed value.)
    ///
    /// The abstract bytes remain the same. This preserves the typed contents in memory on a
    /// roundtrip (see `PointsTo::from_untyped_with_value`).
    /// Note that this means provenance is not lost, which matches Rust's semantics for
    /// casting/transmuting in-memory values.
    ///
    /// Returning the `tracked TypedValue<T>` prohibits creating permission-carrying types out of
    /// thin air, i.e. in the case where `T` is a type that stores/represents a permission
    /// (e.g., shared references).
    pub proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, typed_value): (
        PointsToUntyped,
        TypedValue<T>,
    ))
        requires
            self.wf(),
        ensures
            self.bytes() == pt_untyped.bytes(),
            self.ptr()@.addr == pt_untyped.ptr()@.addr,
            self.ptr()@.provenance == pt_untyped.ptr()@.provenance,
            pt_untyped.wf(),
            pt_untyped.len() == size_of::<T>(),
            typed_value == self.typed_value(),
    {
        broadcast use group_vstd_default;

        let tracked PointsTo { pt_unaligned } = self;
        let tracked PointsToUnaligned { val, pt_untyped, metadata: _ } = pt_unaligned;
        (pt_untyped, val)
    }

    /// Creates a `PointsTo<T>` from a `PointsToUntyped` with the same provenance
    /// and a ptr corresponding to the range of the `PointsToUntyped`.
    /// The resulting `PointsTo<T>` will be empty (uninitialized).
    /// (Use `from_untyped_with_value` instead if you want to supply a value.)
    pub proof fn from_untyped(tracked pt_untyped: PointsToUntyped) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            pt_untyped.ptr()@.addr as int % align_of::<T>() as int == 0,
            pt_untyped.len() == size_of::<T>(),
        ensures
            out.ptr() == pt_untyped.ptr() as *mut T,
            out.bytes() == pt_untyped.bytes(),
            out.is_empty(),
            out.wf(),
    {
        broadcast use group_vstd_default;

        PointsTo {
            pt_unaligned: PointsToUnaligned {
                val: TypedValue::Empty,
                pt_untyped,
                metadata: Ghost(()),
            },
        }
    }

    /// Creates a valid `PointsTo<T>` holding `value` from a `PointsToUntyped`, provided that its
    /// abstract bytes can be decoded into `value`, its length is `size_of::<T>()`,
    /// and its pointer is aligned to `T`.
    ///
    /// The abstract bytes remain the same. This preserves the typed contents in memory on a
    /// roundtrip (see `PointsTo::into_untyped_with_typed_value`).
    /// Note that this means provenance is not lost, which matches Rust's semantics for
    /// casting/transmuting in-memory values.
    ///
    /// Requiring the `tracked value` prohibits creating permission-carrying types out of thin
    /// air, in the case where `T` is a type that stores/represents a permission
    /// (e.g., shared references).
    pub proof fn from_untyped_with_value(tracked pt_untyped: PointsToUntyped, tracked value: T) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            pt_untyped.ptr()@.addr as int % align_of::<T>() as int == 0,
            pt_untyped.len() == size_of::<T>(),
            abs_decode::<T>(pt_untyped.bytes(), &value),
        ensures
            out.ptr() == pt_untyped.ptr() as *mut T,
            out.bytes() == pt_untyped.bytes(),
            out.is_valid(),
            out.value() == value,
            out.wf(),
    {
        let tracked mut out = Self::from_untyped(pt_untyped);
        out.put(value);
        out
    }

    /// Creates a `PointsToUntyped` from a `PointsTo<T>` with the same provenance
    /// and a range corresponding to the address of the `PointsTo<T>` and size of `T`.
    /// If there is any value stored in memory, it is dropped.
    pub proof fn into_untyped(tracked self) -> (tracked pt_untyped: PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() as *mut T == self.ptr(),
            pt_untyped.len() == size_of::<T>(),
            pt_untyped.bytes() == self.bytes(),
            pt_untyped.wf(),
    {
        broadcast use group_vstd_default;

        let tracked PointsTo { pt_unaligned } = self;
        let tracked PointsToUnaligned { val: _, pt_untyped, metadata: _ } = pt_unaligned;
        pt_untyped
    }

    /// Creates a reference to a `PointsToUntyped` from a reference to a `PointsTo<T>` with the same
    /// provenance and a range corresponding to the address of the `PointsTo<T>` and size of `T`.
    pub proof fn as_untyped(tracked &self) -> (tracked pt_untyped: &PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() as *mut T == self.ptr(),
            pt_untyped.len() == size_of::<T>(),
            pt_untyped.bytes() == self.bytes(),
            pt_untyped.wf(),
    {
        broadcast use group_vstd_default;

        self.pt_unaligned.tracked_pt_untyped()
    }

    /// Creates a mutable reference to a `PointsToUntyped` from a mutable reference to a `PointsTo<T>`
    /// with the same provenance and a range corresponding to the address of the `PointsTo<T>` and
    /// size of `T`. If this permission carries any typed value, it is dropped here.
    /// (call `take` first if you want to save the value.)
    pub proof fn as_untyped_mut(tracked &mut self) -> (tracked pt_untyped: &mut PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() as *mut T == old(self).ptr(),
            pt_untyped.len() == size_of::<T>(),
            pt_untyped.bytes() == old(self).bytes(),
            pt_untyped.wf(),
            final(self).ptr() == final(pt_untyped).ptr() as *mut T,
            final(self).bytes() == final(pt_untyped).bytes(),
            final(self).is_empty(),
            // Criteria necessary for re-establishing invariants
            PointsToUntyped::ptrs_len_same_valid(*pt_untyped, *final(pt_untyped)) ==> final(self).wf(),
    {
        broadcast use group_vstd_default;

        self.pt_unaligned.val = TypedValue::Empty;
        &mut self.pt_unaligned.pt_untyped
    }

    /// This takes a borrow of the `T` from the `TypedValue<T>` on `self`.
    pub proof fn borrow_value(tracked &self) -> tracked &T
        requires
            self.wf(),
            self.is_valid(),
        returns
            self.value(),
    {
        match &self.pt_unaligned.val {
            TypedValue::Valid(b) => b,
            TypedValue::Empty => proof_from_false(),
        }
    }

    /// This moves the `T` out from the `TypedValue<T>` on `self`, leaving `self` empty.
    pub proof fn take(tracked &mut self) -> (tracked val: T)
        requires
            self.wf(),
            self.is_valid(),
        ensures
            val == old(self).value(),
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).is_empty(),
            final(self).wf(),
    {
        let tracked mut tmp = TypedValue::Empty;
        crate::vstd::modes::tracked_swap(&mut tmp, &mut self.pt_unaligned.val);
        match tmp {
            TypedValue::Valid(b) => b.get(),
            TypedValue::Empty => proof_from_false(),
        }
    }

    /// Consumes the `T` and puts it in the `TypedValue<T>` for `self`.
    pub proof fn put(tracked &mut self, tracked val: T)
        requires
            self.wf(),
            abs_decode::<T>(self.bytes(), &val),
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).is_valid(),
            final(self).value() == val,
            final(self).wf(),
    {
        self.pt_unaligned.val = TypedValue::Valid(Tracked(val));
    }

    /// Copies the `T` and puts it in the `TypedValue<T>` for `self`, given that `T` is `Copy`.
    pub proof fn copy(tracked &mut self, tracked val: &T) where T: Copy
        requires
            self.wf(),
            abs_decode::<T>(self.bytes(), val),
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).is_valid(),
            final(self).value() == *val,
            final(self).wf(),
    {
        self.put(*val);
    }

    /// This takes a borrow of the `TypedValue<T>` on `self`.
    pub proof fn borrow_typed_value(tracked &self) -> tracked &TypedValue<T>
        requires
            self.wf(),
        returns
            self.typed_value(),
    {
        &self.pt_unaligned.val
    }

    /// This moves the `TypedValue<T>` out from `self`, leaving `self` empty.
    pub proof fn take_typed_value(tracked &mut self) -> (tracked val: TypedValue<T>)
        requires
            self.wf(),
        ensures
            val == old(self).typed_value(),
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).is_empty(),
            final(self).wf(),
    {
        let tracked mut tmp = TypedValue::Empty;
        crate::vstd::modes::tracked_swap(&mut tmp, &mut self.pt_unaligned.val);
        tmp
    }

    /// Consumes the `TypedValue<T>` and puts it in `self`.
    pub proof fn put_typed_value(tracked &mut self, tracked val: TypedValue<T>)
        requires
            self.wf(),
            val.is_valid() ==> abs_decode::<T>(self.bytes(), &val.value()),
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value() == val,
            final(self).wf(),
    {
        self.pt_unaligned.val = val;
    }

    /// Copies the `TypedValue<T>` and puts it in `self`, given that `T` is `Copy`.
    pub proof fn copy_typed_value(tracked &mut self, tracked val: &TypedValue<T>) where T: Copy
        requires
            self.wf(),
            val.is_valid() ==> abs_decode::<T>(self.bytes(), &val.value()),
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value() == *val,
            final(self).wf(),
    {
        self.put_typed_value(val.tracked_copy());
    }
}

// The functions of the typed `SeqPointsTo` that touch its fields.
impl<T> SeqPointsTo<T, PointsTo<T>> {
    /// Returns a `tracked` reference to the underlying `Seq<PointsTo<T>>`,
    /// given `tracked &self`.
    pub proof fn tracked_seq_pt(tracked &self) -> (tracked ret: &Seq<PointsTo<T>>)
        requires
            self.wf(),
        ensures
            ret == self.seq_pt(),
            forall|i: int| 0 <= i < ret.len() ==> #[trigger] ret[i].wf(),
    {
        assert forall|i: int| 0 <= i < self.seq_pt().len() implies #[trigger] self.seq_pt()[i].wf() by {
            assert(self[i].wf_basic());
        }
        &self.seq_pt
    }

    /// Returns a `tracked` mutable reference to the underlying `Seq<PointsTo<T>>`,
    /// given `tracked &mut self`. `self.ptr` will remain unchanged.
    ///
    /// Provided that this mutable reference is not used to change the sequence length
    /// or any of the `PointsTo<T>` pointers, the invariant will be preserved.
    pub proof fn tracked_seq_pt_mut(tracked &mut self) -> (tracked ret: &mut Seq<PointsTo<T>>)
        requires
            self.wf(),
        ensures
            *ret == old(self).seq_pt(),
            final(self).seq_pt() == *final(ret),
            old(self).ptr() == final(self).ptr(),
            // Criteria necessary for re-establishing invariants
            Self::ptrs_len_same_valid(*old(self), *final(self)) ==> final(self).wf(),
    {
        broadcast use group_vstd_default;

        &mut self.seq_pt
    }

    /// Returns a `tracked` mutable reference to the `PointsTo<T>` permission at index `i`,
    /// given `tracked &mut self`. `self.ptr()` will remain unchanged.
    ///
    /// Provided that this mutable reference is not used to change the pointer at index `i`,
    /// the invariant will be preserved.
    pub proof fn index_mut(tracked &mut self, i: int) -> (tracked ret: &mut PointsTo<T>)
        requires
            self.wf(),
            0 <= i < self.len(),
        ensures
            final(self).ptr() == old(self).ptr(),
            *ret == old(self).seq_pt()[i],
            final(self).seq_pt() == old(self).seq_pt().update(i, *final(ret)),
            // Criteria necessary for re-establishing invariants
            PointsTo::<T>::ptrs_len_same_valid(*ret, *final(ret)) ==> final(self).wf(),
    {
        self.seq_pt.tracked_borrow_mut(i)
    }

    /// Constructs a `SeqPointsTo` from a sequence of well-formed `PointsTo<T>` permissions and a pointer,
    /// provided that the pointer is aligned, non-null, and in bounds of its provenance,
    /// and the pointer of each permission is at the expected offset from the given pointer.
    pub proof fn from_seq(tracked r: Seq<PointsTo<T>>, ptr: *mut T) -> (tracked s: Self)
        requires
            forall|i: int| 0 <= i < r.len() ==> #[trigger] r[i].wf(),
            forall|i: int|
                #![trigger r[i].ptr()@.provenance]
                #![trigger r[i].ptr()@.addr]
                0 <= i < r.len() ==> {
                    &&& r[i].ptr()@.provenance == ptr@.provenance
                    &&& r[i].ptr()@.addr == ptr@.addr + i * size_of::<T>()
                },
            ptr@.addr != 0,
            ptr@.addr as nat % align_of::<T>() == 0,
            ptr_addr_in_bounds(ptr),
        ensures
            s.seq_pt() == r,
            s.ptr() == ptr,
            s.wf(),
    {
        let tracked s = SeqPointsTo { seq_pt: r, ptr: Ghost(ptr) };
        assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i].wf_basic() by {
            assert(r[i].wf());
        }
        s
    }

    /// Given an aligned and non-null pointer,
    /// it is always possible to construct a `SeqPointsTo` with an empty sequence of permissions.
    pub proof fn empty(ptr: *mut T) -> (tracked spt: Self)
        requires
            ptr@.addr != 0,
            ptr@.addr as nat % align_of::<T>() == 0,
            ptr_addr_in_bounds(ptr),
        ensures
            spt.seq_pt() == Seq::<PointsTo<T>>::empty(),
            spt.ptr() == ptr,
            spt.len() == 0,
            spt.wf(),
    {
        broadcast use group_vstd_default;

        SeqPointsTo { seq_pt: Seq::tracked_empty(), ptr: Ghost(ptr) }
    }

    /// Consumes this `SeqPointsTo`, returning the underlying `Seq<PointsTo<T>>`.
    pub proof fn into_seq(tracked self) -> (tracked r: Seq<PointsTo<T>>)
        requires
            self.wf(),
        ensures
            r == self.seq_pt(),
            forall|i: int| 0 <= i < r.len() ==> #[trigger] r[i].wf(),
    {
        assert forall|i: int| 0 <= i < self.seq_pt().len() implies #[trigger] self.seq_pt()[i].wf() by {
            assert(self[i].wf_basic());
        }
        self.seq_pt
    }

    /// Given that the subrange is within bounds, it is always possible to borrow a permission
    /// to just that subrange.
    pub proof fn subrange(tracked &self, start_index: nat, len: nat) -> (tracked sub: &Self)
        requires
            self.wf(),
            start_index + len <= self.len(),
        ensures
            sub.wf(),
            sub.ptr() == ptr_mut_from_data::<T>(
                PtrData {
                    addr: ((self.ptr()@.addr + start_index * size_of::<T>()) as usize),
                    provenance: self.ptr()@.provenance,
                    metadata: (),
                },
            ),
            sub.seq_pt() == self.seq_pt().subrange(start_index as int, (start_index + len) as int),
    {
        broadcast use group_vstd_default;

        let sub_ptr = ptr_mut_from_data::<T>(
            PtrData {
                addr: ((self.ptr()@.addr + start_index * size_of::<T>()) as usize),
                provenance: self.ptr()@.provenance,
                metadata: (),
            },
        );
        // `sub_ptr` is non-null, in bounds and aligned (same reasoning as in `split`)
        if self.len() != 0 && size_of::<T>() != 0 {
            assert(self.len() * size_of::<T>() != 0) by (nonlinear_arith)
                requires
                    self.len() != 0,
                    size_of::<T>() != 0,
            ;
            self.provenance_not_none();
            self.ptr_bounds();
            assert(start_index * size_of::<T>() <= self.len() * size_of::<T>())
                by (nonlinear_arith)
                requires
                    start_index <= self.len(),
            ;
            assert((self.ptr()@.addr + start_index * size_of::<T>()) as nat % align_of::<T>() == 0)
                by {
                broadcast use
                    crate::vstd::arithmetic::div_mod::lemma_mul_mod_noop_right,
                    crate::vstd::arithmetic::div_mod::lemma_add_mod_noop,
                ;

            }
        }

        let tracked seq_pt = self.seq_pt.tracked_borrow_subrange(
            start_index as int,
            (start_index + len) as int,
        );
        let tracked sub = shr_ref_struct_wrap(
            seq_pt,
            &Self { seq_pt: *seq_pt, ptr: Ghost(sub_ptr) },
            "",
            "seq_pt",
        );

        // Each element sits at the expected offset from `sub_ptr`
        assert forall|i: int| 0 <= i < sub.len() implies #[trigger] sub[i].ptr()@.addr
            == sub.ptr()@.addr + i * size_of::<T>() by {
            assert(self.ptr()@.addr + (i + start_index) * size_of::<T>() == self.ptr()@.addr
                + start_index * size_of::<T>() + i * size_of::<T>()) by (nonlinear_arith);
        }
        sub
    }

    /// Returns a mutable reference to the sub-permission covering indices `[i, j)`.
    /// The sub-permission has the same provenance, and its pointer is offset from `self.ptr()`
    /// by `i * size_of::<T>()`.
    ///
    /// Provided that the mutable reference is not used to change the pointer or length of the
    /// sub-permission, and that it is still well-formed, `self` is also still well-formed,
    /// with the sub-sequence of permissions replaced by the final sub-permission's.
    pub axiom fn subrange_mut(tracked &mut self, i: nat, j: nat) -> (tracked r: &mut Self)
        requires
            self.wf(),
            0 <= i <= j <= self.len(),
        ensures
            r.wf(),
            r.ptr() == ptr_mut_from_data::<T>(
                PtrData {
                    addr: ((old(self).ptr()@.addr + i * size_of::<T>()) as usize),
                    provenance: old(self).ptr()@.provenance,
                    metadata: (),
                },
            ),
            r.seq_pt() == old(self).seq_pt().subrange(i as int, j as int),
            // Criteria necessary for re-establishing invariants
            final(r).wf() && final(r).ptr() == r.ptr() && final(r).len() == r.len() ==> {
                &&& final(self).wf()
                &&& final(self).ptr() == old(self).ptr()
                &&& final(self).seq_pt() == old(self).seq_pt().subrange(0, i as int)
                    + final(r).seq_pt() + old(self).seq_pt().subrange(
                    j as int,
                    old(self).len() as int,
                )
            },
    ;
}

pub broadcast group group_points_to_lemmas {
    SeqPointsTo::lemma_ptrs_len_same_valid_untyped,
    PointsTo::lemma_ptrs_len_same_valid,
}

} // verus!
