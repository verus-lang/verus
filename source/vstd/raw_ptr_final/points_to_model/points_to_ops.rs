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
        } else if other_addr >= self_addr + len * csize {
            // `other` starts at or after `self`'s whole range ends: the last
            // element ends exactly where `self` does, so its disjointness from
            // `other` gives us what we need.
            self.seq_pt.tracked_borrow_mut(len - 1).is_disjoint(other);
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
        assert(self.seq_pt =~= old(self).seq_pt);
    }
}

impl<T, P: PTProperties<A = T>> SeqPointsTo<T, P> {
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
        SeqPointsTo { seq_pt: perms, ptr: Ghost(slice_ptr) }
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

        assert forall|i: int| 0 <= i < second.len() implies {
            &&& #[trigger] second[i].ptr()@.provenance == second.ptr()@.provenance
            &&& second[i].ptr()@.addr == second.ptr()@.addr + i * s
            &&& second[i].wf_basic()
        } by {
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
        let p = ptr_mut_from_data::<[T]>(
            PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: (self.len() + other.len()) as usize,
            },
        );
        self.lemma_join_wf_basic(&other, SeqPointsTo { seq_pt: self.seq_pt + other.seq_pt, ptr: Ghost(p) });

        let tracked mut seq_pt = self.seq_pt;
        seq_pt.tracked_add(other.seq_pt);
        SeqPointsTo { seq_pt: seq_pt, ptr: Ghost(p) }
    }

    /// A permission made of `self`'s permissions followed by `other`'s,
    /// starting at `self`'s pointer, is well-formed under `join_basic`'s requirements.
    proof fn lemma_join_wf_basic(tracked &self, tracked other: &Self, joined: Self)
        requires
            self.wf_basic(),
            other.wf_basic(),
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len() * P::size(()),
            P::size(()) == 0 ==> self.len() + other.len() <= usize::MAX,
            joined.seq_pt() == self.seq_pt() + other.seq_pt(),
            joined.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: (self.len() + other.len()) as usize,
            }),
        ensures
            joined.wf_basic(),
    {
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

        assert forall|i: int| 0 <= i < joined.len() implies {
            &&& #[trigger] joined[i].ptr()@.provenance == joined.ptr()@.provenance
            &&& joined[i].ptr()@.addr == joined.ptr()@.addr + i * s
            &&& joined[i].wf_basic()
        } by {
            if i >= self.len() {
                assert(self.ptr()@.addr + self.len() * s + (i - self.len()) * s
                    == self.ptr()@.addr + i * s) by (nonlinear_arith);
            }
        }
    }

    /// Borrows the sub-sequence of permissions in `[start, end)`.
    pub proof fn subrange_basic(tracked &self, start: nat, end: nat) -> (tracked sub: &Self)
        requires
            self.wf_basic(),
            start <= end <= self.len(),
        ensures
            sub.seq_pt() == self.seq_pt().subrange(start as int, end as int),
            sub.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: (self.ptr()@.addr + start * P::size(())) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (end - start) as usize,
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
                metadata: (end - start) as usize,
            },
        );

        let tracked seq_pt = self.seq_pt.tracked_borrow_subrange(start as int, end as int);
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
        self.split_basic(mid)
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
        (self.subrange_basic(0, mid), self.subrange_basic(mid, self.len()))
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
        let old_self = *self;
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
        self.join_basic(other)
    }

    /// Joins shared borrows of two `PointsToUntyped` permissions into a shared borrow of a
    /// single `PointsToUntyped`, under the same conditions as `join`.
    pub proof fn join_ref<'a>(tracked &'a self, tracked other: &'a Self) -> (tracked joined: &'a Self)
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
        let p = ptr_mut_from_data::<[u8]>(
            PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: (self.len() + other.len()) as usize,
            },
        );
        let tracked seq_pt = self.seq_pt.tracked_add_borrow(&other.seq_pt);
        let tracked joined = shr_ref_struct_wrap(
            seq_pt,
            &Self { seq_pt: *seq_pt, ptr: Ghost(p) },
            "",
            "seq_pt",
        );
        self.lemma_join_wf_basic(other, *joined);
        joined
    }

    /// Joins mutable borrows of two `PointsToUntyped` permissions into a mutable borrow of a
    /// single `PointsToUntyped`, under the same conditions as `join`.
    ///
    /// If the joined permission keeps its pointers and length, then so do `self` and `other`, and
    /// their final byte permissions concatenate to the joined permission's final ones.
    pub proof fn join_mut<'a>(tracked &'a mut self, tracked other: &'a mut Self) -> (tracked joined:
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
    {
        let old_self = *self;
        let old_other = *other;
        let p = ptr_mut_from_data::<[u8]>(
            PtrData {
                addr: old_self.ptr()@.addr,
                provenance: old_self.ptr()@.provenance,
                metadata: (old_self.len() + old_other.len()) as usize,
            },
        );
        self.lemma_join_wf_basic(other, Self { seq_pt: old_self.seq_pt + old_other.seq_pt, ptr: Ghost(p) });

        let tracked s1 = self.tracked_seq_pt_mut();
        let tracked s2 = other.tracked_seq_pt_mut();
        let tracked seq_pt = s1.tracked_add_borrow_mut(s2);
        Self::from_seq_mut(seq_pt, p)
    }
}

impl<T> PTProperties for PointsToUnaligned<T> {
    /// Non-nullness follows from the underlying `PointsToUntyped`'s invariant,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn is_nonnull(tracked &self) {
        self.pt_untyped.is_nonnull();
    }

    /// Delegates to the underlying `PointsToUntyped`'s `ptr_bounds`,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn ptr_bounds(tracked &self) {
        self.pt_untyped.ptr_bounds();
    }

    /// Delegates to the underlying `PointsToUntyped`'s `provenance_not_none`,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
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
}

impl<T> PTProperties for PointsToUnaligned<[T]> {
    /// Non-nullness follows from the underlying `PointsToUntyped`'s invariant,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn is_nonnull(tracked &self) {
        self.pt_untyped.is_nonnull();
    }

    /// Delegates to the underlying `PointsToUntyped`'s `ptr_bounds`,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn ptr_bounds(tracked &self) {
        self.pt_untyped.ptr_bounds();
    }

    /// Delegates to the underlying `PointsToUntyped`'s `provenance_not_none`,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
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
}

impl<T> PTValueOps for PointsToUnaligned<T> {
    // zero_sized, borrow, into_untyped, from_untyped: the trait's default bodies.

    /// Borrows the `val` field.
    proof fn borrow_typed_value(tracked &self) -> tracked &TypedValue<T> {
        &self.val
    }

    /// Swaps `Empty` into the `val` field.
    proof fn take_typed_value(tracked &mut self) -> (tracked v: TypedValue<T>) {
        let tracked mut v = TypedValue::Empty;
        crate::vstd::modes::tracked_swap(&mut v, &mut self.val);
        v
    }

    /// Replaces the `val` field.
    proof fn put_typed_value(tracked &mut self, tracked v: TypedValue<T>) {
        self.val = v;
    }

    /// Splits into well-formed `pt_untyped` and `val` fields.
    proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, v): (PointsToUntyped, TypedValue<T>)) {
        (self.pt_untyped, self.val)
    }

    /// Builds the struct from its well-formed fields.
    proof fn from_untyped_with_typed_value(
        tracked pt_untyped: PointsToUntyped,
        tracked typed_value: TypedValue<T>,
        metadata: (),
    ) -> (tracked out: Self) {
        PointsToUnaligned { val: typed_value, pt_untyped, metadata: Ghost(metadata) }
    }

    /// Borrows the `pt_untyped` field.
    proof fn as_untyped(tracked &self) -> (tracked pt_untyped: &PointsToUntyped) {
        &self.pt_untyped
    }

    /// Mutably borrows the `pt_untyped` field, setting the `val` field to `Empty`.
    proof fn as_untyped_mut(tracked &mut self) -> (tracked pt_untyped: &mut PointsToUntyped) {
        self.val = TypedValue::Empty;
        &mut self.pt_untyped
    }
}

impl<T> PTValueOps for PointsToUnaligned<[T]> {
    // zero_sized, borrow, into_untyped, from_untyped: the trait's default bodies.

    /// Borrows the `val` field.
    proof fn borrow_typed_value(tracked &self) -> tracked &TypedValue<[T]> {
        &self.val
    }

    /// Swaps `Empty` into the `val` field.
    proof fn take_typed_value(tracked &mut self) -> (tracked v: TypedValue<[T]>) {
        let tracked mut v = TypedValue::Empty;
        crate::vstd::modes::tracked_swap(&mut v, &mut self.val);
        v
    }

    /// Replaces the `val` field.
    proof fn put_typed_value(tracked &mut self, tracked v: TypedValue<[T]>) {
        self.val = v;
    }

    /// Splits into well-formed `pt_untyped` and `val` fields.
    proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, v): (PointsToUntyped, TypedValue<[T]>)) {
        (self.pt_untyped, self.val)
    }

    /// Builds the struct from its well-formed fields.
    proof fn from_untyped_with_typed_value(
        tracked pt_untyped: PointsToUntyped,
        tracked typed_value: TypedValue<[T]>,
        metadata: usize,
    ) -> (tracked out: Self) {
        PointsToUnaligned { val: typed_value, pt_untyped, metadata: Ghost(metadata) }
    }

    /// Borrows the `pt_untyped` field.
    proof fn as_untyped(tracked &self) -> (tracked pt_untyped: &PointsToUntyped) {
        &self.pt_untyped
    }

    /// Mutably borrows the `pt_untyped` field, setting the `val` field to `Empty`.
    proof fn as_untyped_mut(tracked &mut self) -> (tracked pt_untyped: &mut PointsToUntyped) {
        self.val = TypedValue::Empty;
        &mut self.pt_untyped
    }
}

impl<T> PTSizedValue for PointsToUnaligned<T> {
    // take, put, copy, copy_typed_value, from_untyped_with_value: the trait's default bodies.

    /// Trivial, since a `PointsToUnaligned` has no alignment requirement.
    proof fn lemma_satisfies_alignment_offset(addr: usize, i: nat) {
    }

    /// Trivial, since `additional_validity_constraints` is always `true` for a `Sized` value.
    proof fn lemma_additional_validity_constraints(value: &T) {
    }
}

impl<T> PointsToUnaligned<T> {
    /// Specializes `is_disjoint` to the case when the other permission is a `PointsToUnaligned<S>`.
    pub proof fn is_disjoint_unaligned<S>(tracked &mut self, tracked other: &PointsToUnaligned<S>)
        requires
            size_of::<T>() != 0,
            size_of::<S>() != 0,
            self.wf(),
            other.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + size_of::<T>() <= other.ptr()@.addr
                || other.ptr()@.addr + size_of::<S>() <= final(self).ptr()@.addr,
    {
        self.is_disjoint(other);
    }
}

impl<T: ?Sized> PTProperties for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    /// Non-nullness follows from the underlying `PointsToUnaligned`'s invariant,
    /// since `self.ptr()` is `self.pt_unaligned().ptr()`.
    proof fn is_nonnull(tracked &self) {
        self.pt_unaligned.is_nonnull();
    }

    /// Delegates to the underlying `PointsToUnaligned`'s `ptr_bounds`,
    /// since `self.ptr()` is `self.pt_unaligned().ptr()`.
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
}

impl<T: ?Sized> PTValueOps for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    // zero_sized, borrow, into_untyped, from_untyped: the trait's default bodies.

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn borrow_typed_value(tracked &self) -> tracked &TypedValue<T> {
        self.pt_unaligned.borrow_typed_value()
    }

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn take_typed_value(tracked &mut self) -> (tracked v: TypedValue<T>) {
        self.pt_unaligned.take_typed_value()
    }

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn put_typed_value(tracked &mut self, tracked v: TypedValue<T>) {
        self.pt_unaligned.put_typed_value(v);
    }

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, v): (PointsToUntyped, TypedValue<T>)) {
        self.pt_unaligned.into_untyped_with_typed_value()
    }

    /// Wraps the `PointsToUnaligned` built from the same parts.
    /// (`satisfies_alignment` includes `PointsToUnaligned`'s, which its `from_untyped_with_typed_value` requires.)
    proof fn from_untyped_with_typed_value(
        tracked pt_untyped: PointsToUntyped,
        tracked typed_value: TypedValue<T>,
        metadata: Metadata<T>,
    ) -> (tracked out: Self) {
        let tracked pt_unaligned = PointsToUnaligned::<T>::from_untyped_with_typed_value(
            pt_untyped,
            typed_value,
            metadata,
        );
        PointsTo { pt_unaligned }
    }

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn as_untyped(tracked &self) -> (tracked pt_untyped: &PointsToUntyped) {
        self.pt_unaligned.as_untyped()
    }

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn as_untyped_mut(tracked &mut self) -> (tracked pt_untyped: &mut PointsToUntyped) {
        self.pt_unaligned.as_untyped_mut()
    }
}

impl<T> PTSizedValue for PointsTo<T> {
    // take, put, copy, copy_typed_value, from_untyped_with_value: the trait's default bodies.

    /// Offsetting a pointer by multiples of `size_of::<T>()` preserves its alignment to `T`,
    /// since `size_of::<T>()` is a multiple of `align_of::<T>()`.
    proof fn lemma_satisfies_alignment_offset(addr: usize, i: nat) {
        let a = align_of::<T>() as int;
        let s = size_of::<T>() as int;
        assert(spec_align_of_val::<T>(arbitrary()) == a);
        crate::vstd::arithmetic::div_mod::lemma_fundamental_div_mod(s, a);
        crate::vstd::arithmetic::mul::lemma_mul_is_associative(i as int, s / a, a);
        crate::vstd::arithmetic::div_mod::lemma_mod_multiples_basic(i * (s / a), a);
        crate::vstd::arithmetic::div_mod::lemma_add_mod_noop(addr as int, i * s, a);
    }

    /// Trivial, since `additional_validity_constraints` is `PointsToUnaligned<T>`'s, which is always `true`.
    proof fn lemma_additional_validity_constraints(value: &T) {
    }
}

impl<T> PointsTo<T> {
    /// A `PointsTo<T>` is always aligned.
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
            other.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + size_of::<T>() <= other.ptr()@.addr
                || other.ptr()@.addr + size_of::<S>() <= final(self).ptr()@.addr,
    {
        self.is_disjoint(other);
    }
}

impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    /// Converts to a `PointsTo<T>`, given that the address is aligned.
    pub proof fn into_aligned(tracked self) -> (tracked out: PointsTo<T>)
        requires
            self.wf(),
            <PointsTo<T> as PTTypedValue>::satisfies_alignment(self.ptr()@.addr),
        ensures
            out.pt_unaligned() == self,
            out.wf(),
    {
        PointsTo { pt_unaligned: self }
    }

    /// Borrows as a `PointsTo<T>`, given that the address is aligned.
    pub proof fn as_aligned(tracked &self) -> (tracked out: &PointsTo<T>)
        requires
            self.wf(),
            <PointsTo<T> as PTTypedValue>::satisfies_alignment(self.ptr()@.addr),
        ensures
            out.pt_unaligned() == *self,
            out.wf(),
    {
        shr_ref_struct_wrap(self, &PointsTo { pt_unaligned: *self }, "", "pt_unaligned")
    }

    /// Mutably borrows as a `PointsTo<T>`, given that the address is aligned.
    /// `final(self)` is the final `PointsTo<T>`'s underlying `PointsToUnaligned<T>`.
    /// If the final `PointsTo<T>` satisfies `ptrs_len_same_valid_value` with the original,
    /// `self` is well-formed afterwards.
    pub proof fn as_aligned_mut(tracked &mut self) -> (tracked out: &mut PointsTo<T>)
        requires
            self.wf(),
            <PointsTo<T> as PTTypedValue>::satisfies_alignment(self.ptr()@.addr),
        ensures
            out.pt_unaligned() == *old(self),
            out.wf(),
            *final(self) == final(out).pt_unaligned(),
            <PointsTo<T> as PTTypedValue>::ptrs_len_same_valid_value(*out, *final(out)) ==> final(self).wf(),
    {
        let tracked out = PointsTo::from_unaligned_mut(self);
        let out_ref = out;
        if <PointsTo<T> as PTTypedValue>::ptrs_len_same_valid_value(*out_ref, *final(out_ref)) {
            <PointsToUnaligned<T> as PTTypedValue>::stays_wf(
                out_ref.pt_unaligned(),
                final(out_ref).pt_unaligned(),
            );
        }
        out
    }
}

impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    /// Converts to a `PointsToUnaligned<T>`.
    pub proof fn into_unaligned(tracked self) -> (tracked out: PointsToUnaligned<T>)
        requires
            self.wf(),
        ensures
            out == self.pt_unaligned(),
            out.wf(),
    {
        self.pt_unaligned
    }

    /// Borrows as a `PointsToUnaligned<T>`.
    pub proof fn as_unaligned(tracked &self) -> (tracked out: &PointsToUnaligned<T>)
        requires
            self.wf(),
        ensures
            *out == self.pt_unaligned(),
            out.wf(),
    {
        &self.pt_unaligned
    }

    /// Mutably borrows the underlying `PointsToUnaligned<T>`.
    /// `final(self)` holds the final `PointsToUnaligned<T>`.
    /// If the final unaligned permission preserves the pointer
    /// and satisfies `ptrs_len_same_valid_value` with it,
    /// `self` is well-formed afterwards.
    pub proof fn as_unaligned_mut(tracked &mut self) -> (tracked out: &mut PointsToUnaligned<T>)
        requires
            self.wf(),
        ensures
            *out == old(self).pt_unaligned(),
            out.wf(),
            final(self).pt_unaligned() == *final(out),
            final(out).ptr() == out.ptr() && PointsToUnaligned::<T>::ptrs_len_same_valid_value(*out, *final(out))
                ==> final(self).wf(),
    {
        let tracked out = &mut self.pt_unaligned;
        let out_ref = out;
        if PointsToUnaligned::<T>::ptrs_len_same_valid_value(*out_ref, *final(out_ref)) {
            PointsToUnaligned::<T>::stays_wf(*out_ref, *final(out_ref));
        }
        out
    }
}

impl<T> PointsToUnaligned<[T]> {
    /// The number of elements in the slice (the pointer's metadata).
    #[verifier::inline]
    pub open spec fn len(self) -> nat {
        self.ptr()@.metadata as nat
    }

    /// Borrows the permission to the element at index `i`.
    /// If the slice permission is empty, so is the element's.
    pub proof fn borrow_index(tracked &self, i: int) -> (tracked out: &PointsToUnaligned<T>)
        requires
            self.wf(),
            0 <= i < self.len(),
        ensures
            out.ptr() == ptr_mut_from_data::<T>(PtrData {
                addr: (self.ptr()@.addr + i * size_of::<T>()) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (),
            }),
            out.bytes() == self.bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
            self.typed_value().is_valid() ==> {
                &&& out.typed_value().is_valid()
                &&& out.typed_value().value() == self.typed_value().value_ref()@[i]
            },
            self.typed_value().is_empty() ==> out.typed_value().is_empty(),
            out.wf(),
    {
        broadcast use crate::vstd::type_representation::abs_decode_slice;

        let s = size_of::<T>() as int;
        let n = self.len() as int;
        crate::vstd::arithmetic::mul::lemma_mul_inequality(i + 1, n, s);
        crate::vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(s, i, 1);
        crate::vstd::arithmetic::mul::lemma_mul_nonnegative(i, s);

        // The element's bytes
        let tracked (_, tail) = self.pt_untyped.split_ref((i * s) as nat);
        let tracked (elem, _) = tail.split_ref(s as nat);
        assert(elem.bytes() =~= self.bytes().subrange(i * s, (i + 1) * s));

        // The element's typed value
        let tracked typed_value: &TypedValue<T> = match &self.val {
            TypedValue::Valid(b) => {
                let tracked v: &[T] = b;
                TypedValue::valid_ref(crate::vstd::slice::tracked_slice_index(v, i))
            },
            TypedValue::Empty => &TypedValue::Empty,
        };
        PointsToUnaligned::<T>::from_raw_parts_ref(elem, typed_value, ())
    }

    /// Borrows a `&PointsToUntyped` as a `&PointsToUnaligned<[T]>`
    /// with an empty typed value of length `len`,
    /// provided that the length matches the bytes.
    pub proof fn from_untyped_ref<'a>(tracked pt_untyped: &'a PointsToUntyped, len: usize) -> (tracked out: &'a Self)
        requires
            pt_untyped.wf(),
            pt_untyped.len() == len * size_of::<T>(),
        ensures
            out.ptr()@ == (PtrData { addr: pt_untyped.ptr()@.addr, provenance: pt_untyped.ptr()@.provenance, metadata: len }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value().is_empty(),
            out.wf(),
    {
        let tracked typed_value: &'a TypedValue<[T]> = &TypedValue::Empty;
        PointsToUnaligned::<[T]>::from_raw_parts_ref(pt_untyped, typed_value, len)
    }

    /// Borrows a `&PointsToUntyped` and `tracked &[T]` as a `&PointsToUnaligned<[T]>`
    /// with a valid typed value set to `value`,
    /// provided that the bytes decode to the value.
    pub proof fn from_untyped_with_value_ref<'a>(tracked pt_untyped: &'a PointsToUntyped, tracked value: &'a [T])
        -> (tracked out: &'a Self)
        requires
            pt_untyped.wf(),
            abs_decode::<[T]>(pt_untyped.bytes(), value),
        ensures
            out.ptr()@ == (PtrData { addr: pt_untyped.ptr()@.addr, provenance: pt_untyped.ptr()@.provenance, metadata: value@.len() as usize }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value().is_valid(),
            out.typed_value().value_ref() == value,
            out.wf(),
    {
        broadcast use crate::vstd::slice::group_slice_axioms, crate::vstd::type_representation::abs_decode_slice;

        assert(value@.len() == crate::vstd::slice::spec_slice_len(value));
        let tracked typed_value = TypedValue::valid_ref(value);
        PointsToUnaligned::<[T]>::from_raw_parts_ref(pt_untyped, typed_value, value@.len() as usize)
    }
}

impl<T> PointsTo<[T]> {
    /// The number of elements in the slice (the pointer's metadata).
    #[verifier::inline]
    pub open spec fn len(self) -> nat {
        self.ptr()@.metadata as nat
    }

    /// Borrows the permission to the element at index `i`.
    /// If the slice permission is empty, so is the element's.
    pub proof fn borrow_index(tracked &self, i: int) -> (tracked out: &PointsTo<T>)
        requires
            self.wf(),
            0 <= i < self.len(),
        ensures
            out.ptr() == ptr_mut_from_data::<T>(PtrData {
                addr: (self.ptr()@.addr + i * size_of::<T>()) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (),
            }),
            out.bytes() == self.bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
            self.typed_value().is_valid() ==> {
                &&& out.typed_value().is_valid()
                &&& out.typed_value().value() == self.typed_value().value_ref()@[i]
            },
            self.typed_value().is_empty() ==> out.typed_value().is_empty(),
            out.wf(),
    {
        let tracked elem = self.pt_unaligned.borrow_index(i);
        let addr = self.ptr()@.addr;
        // The element's address doesn't overflow:
        // if it's not zero-sized, its first byte is in `self`'s bytes.
        let s = size_of::<T>() as int;
        assert(addr + i * s <= usize::MAX) by {
            if s > 0 {
                let u = self.pt_unaligned();
                let bytes = u.pt_untyped();
                crate::vstd::arithmetic::mul::lemma_mul_strict_inequality(i, self.len() as int, s);
                assert(bytes[i * s].ptr()@.addr == addr + i * s);
            } else {
                assert(i * s == 0) by (nonlinear_arith)
                    requires
                        s == 0,
                ;
            }
        }
        PointsTo::<T>::lemma_satisfies_alignment_offset(addr, i as nat);
        elem.as_aligned()
    }

    /// Borrows a `&PointsToUntyped` as a `&PointsTo<[T]>`
    /// with an empty typed value of length `len`,
    /// provided that the length matches the bytes and the `PointsToUntyped`'s pointer is aligned.
    pub proof fn from_untyped_ref<'a>(tracked pt_untyped: &'a PointsToUntyped, len: usize) -> (tracked out: &'a Self)
        requires
            pt_untyped.wf(),
            pt_untyped.len() == len * size_of::<T>(),
            Self::satisfies_alignment(pt_untyped.ptr()@.addr),
        ensures
            out.ptr()@ == (PtrData { addr: pt_untyped.ptr()@.addr, provenance: pt_untyped.ptr()@.provenance, metadata: len }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value().is_empty(),
            out.wf(),
    {
        PointsToUnaligned::<[T]>::from_untyped_ref(pt_untyped, len).as_aligned()
    }

    /// Borrows a `&PointsToUntyped` and `tracked &[T]` as a `&PointsTo<[T]>`
    /// with a valid typed value set to `value`,
    /// provided that the bytes decode to the value and the `PointsToUntyped`'s pointer is aligned.
    pub proof fn from_untyped_with_value_ref<'a>(tracked pt_untyped: &'a PointsToUntyped, tracked value: &'a [T])
        -> (tracked out: &'a Self)
        requires
            pt_untyped.wf(),
            abs_decode::<[T]>(pt_untyped.bytes(), value),
            Self::satisfies_alignment(pt_untyped.ptr()@.addr),
        ensures
            out.ptr()@ == (PtrData { addr: pt_untyped.ptr()@.addr, provenance: pt_untyped.ptr()@.provenance, metadata: value@.len() as usize }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value().is_valid(),
            out.typed_value().value_ref() == value,
            out.wf(),
    {
        PointsToUnaligned::<[T]>::from_untyped_with_value_ref(pt_untyped, value).as_aligned()
    }
}

pub broadcast group group_points_to_lemmas {
    SeqPointsTo::lemma_ptrs_len_same_untyped,
    PTTypedValue::lemma_ptrs_len_same_valid_value,
}

} // verus!
