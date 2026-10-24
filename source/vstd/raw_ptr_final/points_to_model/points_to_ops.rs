#![allow(unused_imports)]

use super::*;

verus! {

broadcast use {
    crate::vstd::raw_ptr_final::ptr_model::group_raw_ptr_axioms,
    crate::vstd::layout::group_layout_axioms,
    crate::vstd::seq::group_seq_axioms,
};

impl<T, P: PTProperties<A = T>> PTProperties for SeqPointsTo<T, P> {
    /// Non-nullness is guaranteed by the invariant.
    proof fn is_nonnull(tracked &self) {
    }

    /// If the sequence is nonempty, this follows from the last element's `ptr_bounds`.
    /// Otherwise, `wf_basic`'s provenance clause guarantees it.
    proof fn ptr_bounds(tracked &self) {
        if self.len() > 0 {
            self.seq_pt.tracked_borrow(self.len() - 1).ptr_bounds();
            crate::vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                P::size(()) as int,
                (self.len() - 1) as int,
                1,
            );
        }
    }

    /// If the size is non-zero, the length must be nonzero.
    /// Then this follows from the `provenance_not_none` property of an individual `P`.
    proof fn provenance_not_none(tracked &self) {
        let n = self.len();
        let s = P::size(());
        assert(n != 0 && s != 0) by (nonlinear_arith)
            requires
                n * s != 0,
        ;
        self.seq_pt.tracked_borrow(0).provenance_not_none();
    }

    /// Finds the element whose range contains `other`'s start address
    /// (or the first or last element, if `other` starts outside `self`'s range),
    /// and uses that element's `is_disjoint`.
    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    ) {
        let self_addr = self.ptr()@.addr as int;
        let other_addr = other.ptr()@.addr as int;
        let csize = P::size(()) as int;
        let len = self.len() as int;
        assert(len != 0 && csize != 0) by (nonlinear_arith)
            requires
                len * csize != 0,
        ;

        if other_addr < self_addr {
            // `other` starts strictly before `self`'s whole range: since element 0
            // starts exactly where `self` does, its disjointness from `other` is
            // exactly the disjointness we need for the whole array.
            self.seq_pt.tracked_borrow_mut(0).is_disjoint(other);
            assert(self.seq_pt =~= old(self).seq_pt);
        } else if other_addr >= self_addr + len * csize {
            // `other` starts at or after `self`'s whole range ends: the last
            // element ends exactly where `self` does, so its disjointness from
            // `other` gives us what we need.
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
            self.seq_pt.tracked_borrow_mut(k).is_disjoint(other);
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

    /// Mutably borrows the permission at index `i`, leaving the pointer unchanged.
    pub proof fn index_mut(tracked &mut self, i: int) -> (tracked ret: &mut P)
        requires
            0 <= i < self.len(),
        ensures
            *ret == old(self)[i],
            final(self).seq_pt() == old(self).seq_pt().update(i, *final(ret)),
            final(self).ptr() == old(self).ptr(),
            old(self).wf_basic() && P::ptrs_len_same(*ret, *final(ret)) && final(ret).ptr() == ret.ptr() ==> final(self).wf_basic(),
    {
        let old_self = *self;
        let tracked ret = self.seq_pt.tracked_borrow_mut(i);
        let ret_ref = ret;
        if old_self.wf_basic() && P::ptrs_len_same(*ret_ref, *final(ret_ref))
            && final(ret_ref).ptr() == ret_ref.ptr() {
            P::stays_wf_basic(*ret_ref, *final(ret_ref));
        }
        ret
    }

    /// Creates a `SeqPointsTo` from a sequence of permissions at consecutive offsets from `ptr`.
    pub proof fn from_seq(tracked perms: Seq<P>, ptr: *mut T) -> (tracked out: Self)
        requires
            forall|i: int| 0 <= i < perms.len() ==> #[trigger] perms[i].wf_basic(),
            forall|i: int| 0 <= i < perms.len() ==> {
                &&& (#[trigger] perms[i]).ptr()@.provenance == ptr@.provenance
                &&& perms[i].ptr()@.addr == ptr@.addr + i * P::size(())
            },
            ptr@.addr != 0,
            ptr_addr_in_bounds(ptr),
            perms.len() <= usize::MAX,
        ensures
            out.seq_pt() == perms,
            out.ptr() as *mut T == ptr,
            out.wf_basic(),
    {
        let slice_ptr = ptr_mut_from_data::<[T]>(
            PtrData { addr: ptr@.addr, provenance: ptr@.provenance, metadata: perms.len() as usize },
        );
        let tracked out = SeqPointsTo { seq_pt: perms, ptr: Ghost(slice_ptr) };
        assert forall|i: int| 0 <= i < out.len() implies {
            &&& #[trigger] out[i].ptr()@.provenance == out.ptr()@.provenance
            &&& out[i].ptr()@.addr == out.ptr()@.addr + i * P::size(())
            &&& out[i].wf_basic()
        } by {
            assert(out[i] == perms[i]);
        }
        out
    }

    /// Creates an empty sequence at `ptr`.
    pub proof fn empty(ptr: *mut T) -> (tracked out: Self)
        requires
            ptr@.addr != 0,
            ptr_addr_in_bounds(ptr),
        ensures
            out.seq_pt() == Seq::<P>::empty(),
            out.ptr() as *mut T == ptr,
            out.wf_basic(),
    {
        Self::from_seq(Seq::tracked_empty(), ptr)
    }

    /// Consumes this `SeqPointsTo`, returning the underlying `Seq<P>`.
    pub proof fn into_seq(tracked self) -> (tracked perms: Seq<P>)
        returns
            self.seq_pt(),
    {
        self.seq_pt
    }

    /// Splits into the first `mid` permissions and the rest.
    pub proof fn split_basic(tracked self, mid: nat) -> (tracked (first, second): (Self, Self))
        requires
            self.wf_basic(),
            mid <= self.len(),
        ensures
            first.seq_pt() == self.seq_pt().take(mid as int),
            second.seq_pt() == self.seq_pt().skip(mid as int),
            first.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: mid as usize,
            }),
            second.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: (self.ptr()@.addr + mid * P::size(())) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (self.len() - mid) as usize,
            }),
            first.wf_basic(),
            second.wf_basic(),
    {
        let old_self = self;
        let n = self.len();
        let s = P::size(());
        if n * s != 0 {
            self.provenance_not_none();
            self.ptr_bounds();
        }
        assert(mid * s <= n * s) by (nonlinear_arith)
            requires
                mid <= n,
        ;
        let p1 = ptr_mut_from_data::<[T]>(
            PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: mid as usize,
            },
        );
        let p2 = ptr_mut_from_data::<[T]>(
            PtrData {
                addr: (self.ptr()@.addr + mid * s) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (n - mid) as usize,
            },
        );

        let tracked mut seq_pt = self.seq_pt;
        let tracked other = seq_pt.tracked_skip(mid as int);
        let tracked first = SeqPointsTo { seq_pt: seq_pt, ptr: Ghost(p1) };
        let tracked second = SeqPointsTo { seq_pt: other, ptr: Ghost(p2) };

        assert forall|i: int| 0 <= i < first.len() implies {
            &&& #[trigger] first[i].ptr()@.provenance == first.ptr()@.provenance
            &&& first[i].ptr()@.addr == first.ptr()@.addr + i * s
            &&& first[i].wf_basic()
        } by {
            assert(first[i] == old_self[i]);
        }
        assert forall|i: int| 0 <= i < second.len() implies {
            &&& #[trigger] second[i].ptr()@.provenance == second.ptr()@.provenance
            &&& second[i].ptr()@.addr == second.ptr()@.addr + i * s
            &&& second[i].wf_basic()
        } by {
            assert(second[i] == old_self[i + mid]);
            assert(old_self.ptr()@.addr + (i + mid) * s == old_self.ptr()@.addr + mid * s + i * s)
                by (nonlinear_arith);
        }
        (first, second)
    }

    /// Concatenates two sequences, provided that `other` starts where `self` ends
    /// and they have the same provenance.
    pub proof fn join_basic(tracked self, tracked other: Self) -> (tracked joined: Self)
        requires
            self.wf_basic(),
            other.wf_basic(),
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len() * P::size(()),
            P::size(()) == 0 ==> self.len() + other.len() <= usize::MAX,
        ensures
            joined.seq_pt() == self.seq_pt() + other.seq_pt(),
            joined.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: (self.len() + other.len()) as usize,
            }),
            joined.wf_basic(),
    {
        let old_self = self;
        let old_other = other;
        let s = P::size(());
        // For non-zero-sized permissions, the joined length fits in a `usize`,
        // since `other`'s range ends within its provenance.
        if s != 0 && other.len() != 0 {
            let a = self.len();
            let b = other.len();
            assert(b * s != 0) by (nonlinear_arith)
                requires
                    b != 0,
                    s != 0,
            ;
            other.provenance_not_none();
            other.ptr_bounds();
            assert(a + b <= (a + b) * s && (a + b) * s == a * s + b * s) by (nonlinear_arith)
                requires
                    s != 0,
            ;
        }
        let p = ptr_mut_from_data::<[T]>(
            PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: (self.len() + other.len()) as usize,
            },
        );

        let tracked mut seq_pt = self.seq_pt;
        seq_pt.tracked_add(other.seq_pt);
        let tracked joined = SeqPointsTo { seq_pt: seq_pt, ptr: Ghost(p) };

        assert forall|i: int| 0 <= i < joined.len() implies {
            &&& #[trigger] joined[i].ptr()@.provenance == joined.ptr()@.provenance
            &&& joined[i].ptr()@.addr == joined.ptr()@.addr + i * s
            &&& joined[i].wf_basic()
        } by {
            if i < old_self.len() {
                assert(joined[i] == old_self[i]);
            } else {
                assert(joined[i] == old_other[i - old_self.len()]);
                assert(old_self.ptr()@.addr + old_self.len() * s + (i - old_self.len()) * s
                    == old_self.ptr()@.addr + i * s) by (nonlinear_arith);
            }
        }
        joined
    }

    /// Borrows the sub-sequence of `len` permissions starting at `start`.
    pub proof fn subrange_basic(tracked &self, start: nat, len: nat) -> (tracked sub: &Self)
        requires
            self.wf_basic(),
            start + len <= self.len(),
        ensures
            sub.seq_pt() == self.seq_pt().subrange(start as int, (start + len) as int),
            sub.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: (self.ptr()@.addr + start * P::size(())) as usize,
                provenance: self.ptr()@.provenance,
                metadata: len as usize,
            }),
            sub.wf_basic(),
    {
        let n = self.len();
        let s = P::size(());
        if n * s != 0 {
            self.provenance_not_none();
            self.ptr_bounds();
        }
        assert(start * s <= n * s) by (nonlinear_arith)
            requires
                start <= n,
        ;
        let sub_ptr = ptr_mut_from_data::<[T]>(
            PtrData {
                addr: (self.ptr()@.addr + start * s) as usize,
                provenance: self.ptr()@.provenance,
                metadata: len as usize,
            },
        );

        let tracked seq_pt = self.seq_pt.tracked_borrow_subrange(
            start as int,
            (start + len) as int,
        );
        let tracked sub = shr_ref_struct_wrap(
            seq_pt,
            &Self { seq_pt: *seq_pt, ptr: Ghost(sub_ptr) },
            "",
            "seq_pt",
        );

        assert forall|i: int| 0 <= i < sub.len() implies {
            &&& #[trigger] sub[i].ptr()@.provenance == sub.ptr()@.provenance
            &&& sub[i].ptr()@.addr == sub.ptr()@.addr + i * s
            &&& sub[i].wf_basic()
        } by {
            assert(sub[i] == self[i + start]);
            assert(self.ptr()@.addr + (i + start) * s == self.ptr()@.addr + start * s + i * s)
                by (nonlinear_arith);
        }
        sub
    }
}

impl PointsToUntyped {
    /// If `old` is well-formed
    /// and `new` has the same pointers and length (`ptrs_len_same`),
    /// then `new` is well-formed.
    pub proof fn stays_wf(old: Self, new: Self)
        requires
            old.wf(),
            Self::ptrs_len_same(old, new),
        ensures
            new.wf(),
    {
        Self::stays_wf_basic(old, new);
    }

    /// If `old` and `new` are both well-formed with the same pointer,
    /// then `new` keeps `old`'s pointers and length.
    pub broadcast proof fn lemma_ptrs_len_same_untyped(old: Self, new: Self)
        requires
            old.wf(),
            new.wf(),
            new.ptr() == old.ptr(),
        ensures
            #[trigger] Self::ptrs_len_same(old, new),
    {
        assert forall|j: int| 0 <= j < new.len() implies #[trigger] new[j].ptr() == old[j].ptr() by {
            assert(new[j].ptr()@.addr == old[j].ptr()@.addr);
        }
    }

    /// If `T` is zero sized,
    /// then we can construct a `PointsToUntyped` from any non-null `*mut T`
    /// whose address is within bounds of its provenance.
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
            final(self).ptr()@.addr + final(self).len() <= other.ptr()@.addr
                || other.ptr()@.addr + other.len() <= final(self).ptr()@.addr,
    {
        broadcast use group_vstd_default;

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

        let old_self = self;
        let tracked (first, second) = self.split_basic(mid);
        assert(first.bytes() =~= old_self.bytes().take(mid as int));
        assert(second.bytes() =~= old_self.bytes().skip(mid as int));
        (first, second)
    }

    /// Splits a shared borrow of a `PointsToUntyped`
    /// into shared borrows of bytes `[0, mid)` and `[mid, len)`.
    /// This is the shared-borrow analogue of `split`.
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

        let tracked first = self.subrange_basic(0, mid);
        let tracked second = self.subrange_basic(mid, (self.len() - mid) as nat);
        assert(first.seq_pt() =~= self.seq_pt().take(mid as int));
        assert(second.seq_pt() =~= self.seq_pt().skip(mid as int));
        assert(first.bytes() =~= self.bytes().take(mid as int));
        assert(second.bytes() =~= self.bytes().skip(mid as int));
        (first, second)
    }

    /// Splits a mutable borrow of a `PointsToUntyped`
    /// into mutable borrows of bytes `[0, mid)` and `[mid, len)`.
    /// This is the mutable-borrow analogue of `split`.
    ///
    /// The final pointer stays the same,
    /// and `self`'s final bytes and `seq_pt` are the concatenation
    /// of `first` and `second`'s final bytes and `seq_pt`.
    /// If both halves keep their pointers and lengths (`ptrs_len_same`),
    /// then `final(self)` is also still well-formed.
    pub proof fn split_mut(tracked &mut self, mid: nat) -> (tracked (first, second): (
        &mut Self,
        &mut Self,
    ))
        requires
            0 <= mid <= self.len(),
            self.wf(),
        ensures
            first.seq_pt() == old(self).seq_pt().take(mid as int),
            second.seq_pt() == old(self).seq_pt().skip(mid as int),
            first.bytes() == old(self).bytes().take(mid as int),
            second.bytes() == old(self).bytes().skip(mid as int),
            first.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: old(self).ptr()@.addr,
                    provenance: old(self).ptr()@.provenance,
                    metadata: mid as usize,
                },
            ),
            second.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: (old(self).ptr()@.addr + mid) as usize,
                    provenance: old(self).ptr()@.provenance,
                    metadata: (old(self).len() - mid) as usize,
                },
            ),
            first.wf(),
            second.wf(),
            final(self).ptr() == old(self).ptr(),
            final(self).seq_pt() == final(first).seq_pt() + final(second).seq_pt(),
            final(self).bytes() == final(first).bytes() + final(second).bytes(),
            // Criteria necessary for re-establishing invariants
            Self::ptrs_len_same(*first, *final(first)) && Self::ptrs_len_same(*second, *final(second))
                ==> final(self).wf(),
    {
        broadcast use group_vstd_default;

        let old_self = *self;
        let self_ref = self;
        if old_self.len() != 0 {
            self.provenance_not_none();
            self.ptr_bounds();
        }
        let p1 = ptr_mut_from_data::<[u8]>(
            PtrData {
                addr: old_self.ptr()@.addr,
                provenance: old_self.ptr()@.provenance,
                metadata: mid as usize,
            },
        );
        let p2 = ptr_mut_from_data::<[u8]>(
            PtrData {
                addr: (old_self.ptr()@.addr + mid) as usize,
                provenance: old_self.ptr()@.provenance,
                metadata: (old_self.len() - mid) as usize,
            },
        );
        let tracked (s1, s2) = self.seq_pt.tracked_split_borrow_mut(mid as int);
        let tracked first = Self::from_seq_mut(s1, p1);
        let tracked second = Self::from_seq_mut(s2, p2);
        let first_ref = first;
        let second_ref = second;

        // The halves are well-formed
        assert forall|i: int| 0 <= i < first_ref.len() implies {
            &&& #[trigger] first_ref[i].ptr()@.provenance == first_ref.ptr()@.provenance
            &&& first_ref[i].ptr()@.addr == first_ref.ptr()@.addr + i * PointsToByte::size(())
        } by {
            assert(first_ref[i] == old_self[i]);
        }
        assert forall|i: int| 0 <= i < second_ref.len() implies {
            &&& #[trigger] second_ref[i].ptr()@.provenance == second_ref.ptr()@.provenance
            &&& second_ref[i].ptr()@.addr == second_ref.ptr()@.addr + i * PointsToByte::size(())
        } by {
            assert(second_ref[i] == old_self[i + mid]);
        }
        assert(first_ref.bytes() =~= old_self.bytes().take(mid as int));
        assert(second_ref.bytes() =~= old_self.bytes().skip(mid as int));

        // Final values
        let new_self = *final(self_ref);
        assert(new_self.bytes() =~= final(first_ref).bytes() + final(second_ref).bytes());
        if Self::ptrs_len_same(*first_ref, *final(first_ref)) && Self::ptrs_len_same(
            *second_ref,
            *final(second_ref),
        ) {
            assert forall|i: int| 0 <= i < new_self.len() implies {
                &&& #[trigger] new_self[i].ptr()@.provenance == new_self.ptr()@.provenance
                &&& new_self[i].ptr()@.addr == new_self.ptr()@.addr + i * PointsToByte::size(())
            } by {
                if i < mid {
                    assert(new_self[i] == final(first_ref)[i]);
                } else {
                    assert(new_self[i] == final(second_ref)[i - mid]);
                }
            }
        }
        (first, second)
    }

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

        let old_self = self;
        let old_other = other;
        let tracked joined = self.join_basic(other);
        assert(joined.bytes() =~= old_self.bytes() + old_other.bytes());
        joined
    }
}

// Interim: `ptrs_len_same` is today's `ptrs_len_same_valid`,
// which also has the decode clause, since the interim `wf_basic` has it.
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
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUntyped::ptrs_len_same(old.pt_untyped(), new.pt_untyped())
        &&& new.is_valid() ==> abs_decode::<T>(new.bytes(), &new.value())
    }

    /// Delegates to `PointsToUntyped::stays_wf` for the underlying bytes.
    proof fn stays_wf_basic(old: Self, new: Self) {
        PointsToUntyped::stays_wf(old.pt_untyped(), new.pt_untyped());
    }
}

// Interim: these move to the trait impls (`PTValueOps`, `PTSizedValue`)
// and the generic aligned/unaligned conversions.
impl<T> PointsToUnaligned<T> {
    /// If `old` is well-formed and `new` has the same pointers and length and still satisfies
    /// decode validity (`ptrs_len_same`), then `new` is well-formed.
    pub proof fn stays_wf(old: Self, new: Self)
        requires
            old.wf(),
            Self::ptrs_len_same(old, new),
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
        self.is_disjoint(other);
    }
}

// Interim: `ptrs_len_same` is today's `ptrs_len_same_valid`,
// which also has the decode and length clauses, since the interim `wf_basic` has them.
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
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUntyped::ptrs_len_same(old.pt_untyped(), new.pt_untyped())
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

// Interim: per type, until the generic `PointsTo` impls.
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
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUnaligned::<T>::ptrs_len_same(old.pt_unaligned(), new.pt_unaligned())
    }

    /// Delegates to `PointsToUnaligned::stays_wf`.
    proof fn stays_wf_basic(old: Self, new: Self) {
        PointsToUnaligned::<T>::stays_wf(old.pt_unaligned(), new.pt_unaligned());
    }
}

// Interim: per type, until the generic `PointsTo` impls.
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
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUnaligned::<[T]>::ptrs_len_same(old.pt_unaligned(), new.pt_unaligned())
    }

    /// Delegates to `PointsToUnaligned`'s `stays_wf_basic`.
    proof fn stays_wf_basic(old: Self, new: Self) {
        PointsToUnaligned::<[T]>::stays_wf_basic(old.pt_unaligned(), new.pt_unaligned());
    }
}

// Interim: these move to the trait impls (`PTValueOps`, `PTSizedValue`)
// and the generic aligned/unaligned conversions.
impl<T> PointsTo<T> {
    /// If `old` is well-formed and `new` has the same pointers and length and still satisfies
    /// decode validity (`ptrs_len_same`), then `new` is well-formed.
    pub proof fn stays_wf(old: Self, new: Self)
        requires
            old.wf(),
            Self::ptrs_len_same(old, new),
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
            #[trigger] Self::ptrs_len_same(old, new),
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
            PointsToUntyped::ptrs_len_same(*pt_untyped, *final(pt_untyped)) ==> final(self).wf(),
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

// Interim: an axiom until it is proved from `from_seq_mut` (M5),
// with the typed `SeqPointsTo` impl's final contract.
impl<T> SeqPointsTo<T, PointsTo<T>> {
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
            r.ptr() as *mut T == ptr_mut_from_data::<T>(
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
    SeqPointsTo::lemma_ptrs_len_same_untyped,
    PointsTo::lemma_ptrs_len_same_valid,
}

} // verus!
