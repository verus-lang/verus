#![allow(unused_imports)]

use super::points_to_model::*;
use super::ptr_model::*;
use crate::vstd::group_vstd_default;
use crate::vstd::layout::{self, *};
use crate::vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::vstd::type_representation::*;

verus! {

broadcast use {
    crate::vstd::raw_ptr_final::ptr_model::group_raw_ptr_axioms,
    layout::group_layout_axioms,
    crate::vstd::seq::group_seq_axioms,
};

/// The interface for a `SeqPointsTo<T, PointsTo<T>>` permission,
/// which represents permission to access a contiguous sequence of memory locations,
/// each aligned to `T` and possibly holding a valid value of type `T`.
/// We track the pointer to the start of that memory, along with the
/// `PointsTo<T>` permission for each element.
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

// Interim: today's typed impl, adapted to the `*mut [T]` pointer,
// with `split`, `join` and `subrange` as wrappers over the structural functions.
// Its contracts are replaced by the approved ones when this impl is approved.
impl<T> SeqPointsTo<T, PointsTo<T>> {
    /// The pointer to the first element, without the length.
    pub open spec fn thin_ptr(self) -> *mut T {
        self.ptr() as *mut T
    }

    /// In addition to the well-formed-ness properties which must hold of every `SeqPointsTo`,
    /// the `*mut T` pointer must be aligned to `T`.
    pub open spec fn wf(self) -> bool {
        &&& self.wf_basic()
        &&& self.ptr()@.addr as nat % align_of::<T>() == 0
    }

    /// A "flattened" view of the abstract bytes.
    /// Because the abstract bytes do not change across casting/transmuting, it is often more
    /// convenient to have a single flattened view of the bytes that is the same as for `PointsTo<[T]>`.
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        Self::bytes_inner(self.seq_pt())
    }

    pub open spec fn bytes_inner(perms: Seq<PointsTo<T>>) -> Seq<AbstractByte> {
        perms.fold_left(Seq::empty(), |acc: Seq<AbstractByte>, elt: PointsTo<T>| acc + elt.bytes())
    }

    /// The (possibly-valid) typed value of each element, as a sequence.
    pub open spec fn seq_typed_value(self) -> Seq<TypedValue<T>> {
        self.seq_pt().map(|i: int, pt: PointsTo<T>| pt.typed_value())
    }

    /// Returns `true` if all of the permission's associated memory is valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_valid(&self) -> bool {
        forall|i| 0 <= i < self.len() ==> #[trigger] self[i].is_valid()
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
        Seq::new(self.len(), |i| self[i].value())
    }

    /// Returns `true` if all of the permission's associated memory in the given subrange is valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_valid_subrange(&self, start_index: int, len: nat) -> bool {
        &&& 0 <= start_index <= start_index + len <= self.len()
        &&& forall|i: int| start_index <= i < start_index + len ==> #[trigger] self[i].is_valid()
    }

    /// Given that the subrange is valid, returns the underlying values in that subrange as a sequence.
    #[verifier::inline]
    pub open spec fn value_subrange(&self, start_index: int, len: nat) -> Seq<T>
        recommends
            self.is_valid_subrange(start_index, len),
    {
        Seq::new(len, |i: int| self[start_index + i].value())
    }

    /// If `old` is well-formed and `new` has the same pointers and length, with each element
    /// still satisfying decode validity (`ptrs_len_same`), then `new` is well-formed.
    pub proof fn stays_wf(old: Self, new: Self)
        requires
            old.wf(),
            Self::ptrs_len_same(old, new),
        ensures
            new.wf(),
    {
        Self::stays_wf_basic(old, new);
    }

    /// If `old` and `new` are both well-formed with the same pointer and length, then each element
    /// of `new` keeps the corresponding element of `old`'s pointers and length, and still
    /// satisfies decode validity.
    pub broadcast proof fn lemma_ptrs_len_same_valid(old: Self, new: Self)
        requires
            old.wf(),
            new.wf(),
            new.ptr() == old.ptr(),
            new.len() == old.len(),
        ensures
            #[trigger] Self::ptrs_len_same(old, new),
    {
        assert forall|i: int| 0 <= i < new.len() implies PointsTo::<T>::ptrs_len_same(
            old[i],
            #[trigger] new[i],
        ) by {
            PointsTo::<T>::lemma_ptrs_len_same_valid(old[i], new[i]);
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
        broadcast use group_vstd_default;

    }

    /// We can construct a `SeqPointsTo` with `length`-many `PointsTo` permissions,
    /// provided that `T` is zero-sized and that the pointer is non-null and aligned.
    pub proof fn zero_sized(ptr: *mut T, length: nat) -> (tracked spt: Self)
        requires
            ptr@.addr != 0,
            ptr@.addr as nat % align_of::<T>() == 0,
            ptr_addr_in_bounds(ptr),
            size_of::<T>() == 0,
            length <= usize::MAX,
        ensures
            forall|i| #![auto] 0 <= i < spt.len() ==> spt[i].is_empty(),
            spt.thin_ptr() == ptr,
            spt.len() == length,
            spt.wf(),
    {
        Self::empty(ptr).zero_sized_helper(length, length)
    }

    proof fn zero_sized_helper(tracked self, remaining: nat, total: nat) -> (tracked spt: Self)
        requires
            self.ptr()@.addr != 0,
            self.ptr()@.addr as nat % align_of::<T>() == 0,
            size_of::<T>() == 0,
            self.len() + remaining == total,
            total <= usize::MAX,
            forall|i| #![auto] 0 <= i < self.len() ==> self[i].is_empty(),
            self.wf(),
            self.ptr()@.provenance.is_some() ==> {
                &&& self.ptr()@.addr as int >= self.ptr()@.provenance.unwrap().start_addr()
                &&& self.ptr()@.addr <= self.ptr()@.provenance.unwrap().start_addr()
                    + self.ptr()@.provenance.unwrap().alloc_len()
            },
        ensures
            spt.thin_ptr() == self.thin_ptr(),
            spt.len() == total,
            forall|i| #![auto] 0 <= i < spt.len() ==> spt[i].is_empty(),
            spt.wf(),
        decreases remaining,
    {
        broadcast use group_vstd_default;

        if remaining == 0 {
            self
        } else {
            let ghost_self = self;
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
                if i < ghost_self.len() {
                    assert(perms[i] == ghost_self[i]);
                }
            }
            let tracked mut_spt = Self::from_seq(perms, ptr);

            mut_spt.zero_sized_helper((remaining - 1) as nat, total)
        }
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
        broadcast use crate::vstd::type_representation::encode_decode_len;

        if perms.len() > 0 {
            Self::bytes_len_helper(perms.drop_last());
            assert(perms.last() == perms[perms.len() - 1]);
            assert(perms[perms.len() - 1].wf());
            assert(perms.last().wf());
            assert(perms.last().wf_basic());
            assert(perms.last().pt_unaligned().wf());
            assert(perms.last().pt_unaligned().wf_basic());
            assert(perms.last().bytes().len() == size_of::<T>());
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

            assert(perms.last() == perms[perms.len() - 1]);
            assert(perms.drop_last() == perms.subrange(0, perms.len() - 1));
            assert(Self::bytes_inner(perms) == Self::bytes_inner(perms.subrange(0, perms.len() - 1))
                + perms[perms.len() - 1].bytes());
            assert(perms.subrange(split, perms.len() as int).last() == perms[perms.len() - 1]);
            assert(perms.subrange(split, perms.len() as int).drop_last() == perms.subrange(
                split,
                perms.len() - 1,
            ));
            assert(Self::bytes_inner(perms.subrange(split, perms.len() as int))
                == Self::bytes_inner(perms.subrange(split, perms.len() - 1)) + perms[perms.len()
                - 1].bytes());

            Self::bytes_len_helper(perms.subrange(0, split));
            Self::bytes_len_helper(perms.subrange(split, perms.len() as int));
            assert(perms.subrange(split, perms.len() as int).len() == perms.len() - split);
            assert(Self::bytes_inner(perms.subrange(0, perms.len() - 1).subrange(0, split)).len()
                == Self::bytes_inner(perms.subrange(0, split)).len());
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
        broadcast use group_vstd_default;

        Self::bytes_len_helper(self.seq_pt());

        Self::bytes_subrange(self.seq_pt(), i + 1);
        Self::bytes_subrange(self.seq_pt().subrange(0, i + 1), i);
        assert(self.seq_pt()[i] == self.seq_pt().subrange(0, i + 1).subrange(i, i + 1)[0]);
        self.bytes().lemma_slice_of_slice(
            0,
            (i + 1) * size_of::<T>(),
            i * size_of::<T>(),
            (i + 1) * size_of::<T>(),
        );
    }

    /// If `sub` holds the permissions in `[start, end)` of `self`, then its abstract bytes are
    /// the subrange `[start * size_of::<T>(), end * size_of::<T>())` of `self`'s abstract bytes.
    pub proof fn bytes_subrange_equiv(&self, sub: Self, start: int, end: int)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
            sub.seq_pt() == self.seq_pt().subrange(start, end),
        ensures
            sub.bytes() == self.bytes().subrange(start * size_of::<T>(), end * size_of::<T>()),
    {
        broadcast use group_vstd_default;

        let perms = self.seq_pt();
        assert forall|i: int| 0 <= i < perms.len() implies #[trigger] perms[i].wf() by {
            assert(self[i].wf_basic());
        }
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
            self.typed_value_equiv(len - 1);
        }
    }

    /// For all positions in this sequence, the abstract bytes for that position can be decoded into the value in memory at that position.
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

    /// Converts a `SeqPointsTo<T, PointsTo<T>>` into a `PointsToUntyped` covering the same bytes,
    /// together with the `TypedValue<T>` of each element.
    /// (Use `into_untyped` instead if you don't need the typed values.)
    ///
    /// The resulting `PointsToUntyped` has the same address and provenance and a length of
    /// `self.len() * size_of::<T>()`, and preserves the abstract bytes.
    /// The returned `tracked typed_value` holds the typed contents from this memory,
    /// which can later be used to convert the `pt_untyped` permission back to a typed permission
    /// (see `SeqPointsTo::from_untyped_with_typed_value`).
    pub proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, typed_value): (
        PointsToUntyped,
        Seq<TypedValue<T>>,
    ))
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
        broadcast use group_vstd_default;

        let ghost_self = self;
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
            assert(pt_untyped.bytes() =~= self.bytes());
            (pt_untyped, Seq::tracked_empty())
        } else {
            let tracked mut seq_pt = self.into_seq();
            let tracked last = seq_pt.tracked_pop();
            assert forall|i: int| 0 <= i < seq_pt.len() implies {
                &&& #[trigger] seq_pt[i].ptr()@.addr == ghost_self.ptr()@.addr + i * size_of::<T>()
                &&& seq_pt[i].ptr()@.provenance == ghost_self.ptr()@.provenance
            } by {
                assert(seq_pt[i] == ghost_self[i]);
            }
            let tracked head = Self::from_seq(seq_pt, ghost_self.thin_ptr());
            let ghost_head = head;
            let ghost_last = last;
            let tracked (head_u8, mut head_typed_value) = head.into_untyped_with_typed_value();
            let tracked (last_u8, last_typed_value) = last.into_untyped_with_typed_value();
            head_typed_value.tracked_push(last_typed_value);
            let tracked pt_untyped = head_u8.join(last_u8);

            ghost_self.bytes_len();

            assert(head_typed_value =~= ghost_self.seq_typed_value()) by {
                assert forall|i: int| 0 <= i < ghost_self.len() implies head_typed_value[i]
                    == #[trigger] ghost_self.seq_typed_value()[i] by {
                    if i < ghost_self.len() - 1 {
                        assert(ghost_head[i] == ghost_self[i]);
                    } else {
                        assert(ghost_last == ghost_self[i]);
                    }
                }
            }
            (pt_untyped, head_typed_value)
        }
    }

    /// Creates a `PointsToUntyped` from a `SeqPointsTo<T, PointsTo<T>>` with the same address and
    /// provenance and a length of `self.len() * size_of::<T>()`.
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

    /// Creates a `SeqPointsTo<T, PointsTo<T>>` of length `len` from a `PointsToUntyped` with the
    /// same provenance and a ptr corresponding to the range of the `PointsToUntyped`.
    /// The resulting permission will be empty (uninitialized).
    /// (Use `from_untyped_with_typed_value` instead if you want to supply typed values.)
    pub proof fn from_untyped(tracked pt_untyped: PointsToUntyped, len: usize) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            pt_untyped.ptr()@.addr as nat % align_of::<T>() == 0,
            pt_untyped.len() == len * size_of::<T>(),
        ensures
            out.ptr()@.addr == pt_untyped.ptr()@.addr,
            out.ptr()@.provenance == pt_untyped.ptr()@.provenance,
            out.len() == len,
            out.bytes() == pt_untyped.bytes(),
            out.is_fully_empty(),
            out.wf(),
    {
        broadcast use group_vstd_default;

        let tracked mut out = Self::from_untyped_with_typed_value(
            pt_untyped,
            len,
            Seq::tracked_empty(),
        );
        // `from_untyped_with_typed_value` says nothing about the validity of elements past the
        // supplied `typed_value`, so empty all of them.
        let before = out;
        let tracked _taken = out.take_typed_value_subrange(0, len as int);
        assert(out.seq_typed_value().len() == before.seq_typed_value().len());
        assert(out.len() == len);
        assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i].is_empty() by {
            out.typed_value_equiv(i);
            assert(out.seq_typed_value()[i] == TypedValue::<T>::Empty);
        }
        out
    }

    /// Creates a `SeqPointsTo<T, PointsTo<T>>` of length `capacity` from a `PointsToUntyped`,
    /// with the first `typed_value.len()` elements holding the given typed values,
    /// under the following conditions:
    ///
    /// (1) The pointer's address is aligned to `T`.
    ///
    /// (2) The length is exactly `capacity * size_of::<T>()`.
    ///
    /// (3) For each valid element in `typed_value`, the corresponding abstract bytes for the
    ///     `PointsToUntyped` can be decoded into its value. `typed_value` may contain empty
    ///     elements (these are ignored for purposes of decoding) and can be a prefix of the total
    ///     `capacity` (in which case, the remaining memory is all logically uninitialized).
    ///
    /// The abstract bytes remain the same. This preserves the typed contents in memory on a
    /// roundtrip (see `SeqPointsTo::into_untyped_with_typed_value`).
    pub proof fn from_untyped_with_typed_value(
        tracked pt_untyped: PointsToUntyped,
        capacity: usize,
        tracked typed_value: Seq<TypedValue<T>>,
    ) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            pt_untyped.ptr()@.addr as nat % align_of::<T>() == 0,
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
            forall|i: int| 0 <= i < typed_value.len() ==> (#[trigger] out[i]).typed_value() == typed_value[i],
            out.wf(),
        decreases capacity,
    {
        broadcast use group_vstd_default;

        let ghost_untyped = pt_untyped;

        if capacity == 0 {
            assert(capacity * size_of::<T>() == 0) by (nonlinear_arith)
                requires
                    capacity == 0,
            ;
            let tracked out = Self::empty(pt_untyped.ptr() as *mut T);
            assert(out.bytes() =~= pt_untyped.bytes());
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
            assert(((pt_untyped.ptr()@.addr + (capacity - 1) as nat * size_of::<T>()) as nat
                % align_of::<T>() == 0)) by {
                broadcast use
                    crate::vstd::arithmetic::div_mod::lemma_mul_mod_noop_right,
                    crate::vstd::arithmetic::div_mod::lemma_add_mod_noop,
                    layout_of_sized,
                ;

            }
            // Split into "head" and "tail", where tail is the last element's bytes
            let tracked (head, tail) = pt_untyped.split(
                ((capacity - 1) as nat * size_of::<T>()) as nat,
            );
            assert(tail.len() + (capacity - 1) as nat * size_of::<T>() == capacity
                * size_of::<T>());
            assert(tail.len() == size_of::<T>()) by (nonlinear_arith)
                requires
                    tail.len() + (capacity - 1) as nat * size_of::<T>() == capacity * size_of::<T>(),
                    capacity > 0,
            ;
            if size_of::<T>() == 0 {
                assert((capacity - 1) as nat * size_of::<T>() == 0) by (nonlinear_arith)
                    requires
                        size_of::<T>() == 0,
                ;
            }
            assert(tail.ptr()@.addr == ghost_untyped.ptr()@.addr + (capacity - 1) as nat
                * size_of::<T>());

            // Convert the tail into a typed permission holding the last typed value, if supplied
            let ghost_tail = tail;
            let tracked mut tail_pt = PointsTo::<T>::from_untyped(tail);
            let tracked mut head_typed_value = typed_value;
            if typed_value.len() == capacity {
                let tracked last = head_typed_value.tracked_pop();
                let i = (capacity - 1) as int;
                assert(last == typed_value[i]);
                assert(tail_pt.bytes() =~= ghost_untyped.bytes().subrange(
                    i * size_of::<T>(),
                    (i + 1) * size_of::<T>(),
                ));
                tail_pt.put_typed_value(last);
            }
            let tail_ptr = tail_pt.ptr();
            let tail_bytes = tail_pt.bytes();
            assert(tail_bytes == ghost_tail.bytes());
            let tracked mut tail_seq = Seq::tracked_empty();
            tail_seq.tracked_push(tail_pt);
            assert forall|i: int| 0 <= i < tail_seq.len() implies #[trigger] tail_seq[i].ptr()@.addr
                == tail_ptr@.addr + i * size_of::<T>() by {
                assert(i == 0);
                assert(0 * size_of::<T>() == 0) by (nonlinear_arith);
            }
            let tracked tail_typed = Self::from_seq(tail_seq, tail_ptr);

            // Invoke the inductive hypothesis on the head
            assert forall|i: int|
                0 <= i < head_typed_value.len() && head_typed_value[i].is_valid() implies #[trigger] abs_decode::<
                T,
            >(
                head.bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
                &head_typed_value[i].value(),
            ) by {
                assert(0 <= i * size_of::<T>() <= (i + 1) * size_of::<T>() <= (capacity
                    - 1) as nat * size_of::<T>()) by (nonlinear_arith)
                    requires
                        0 <= i < capacity - 1,
                ;
                ghost_untyped.bytes().lemma_slice_of_slice(
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
            assert(ghost_untyped.bytes().take(
                ((capacity - 1) as nat * size_of::<T>()) as int,
            ) + ghost_untyped.bytes().skip(((capacity - 1) as nat * size_of::<T>()) as int)
                =~= ghost_untyped.bytes());
            out
        }
    }

    /// Borrows the underlying `PointsToUntyped` permissions of the first `n` permissions,
    /// joined into a single `PointsToUntyped`.
    proof fn untyped_ref_join(tracked &self, n: nat) -> (tracked raw: &PointsToUntyped)
        requires
            self.wf(),
            n <= self.len(),
        ensures
            raw.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (n * size_of::<T>()) as usize,
                },
            ),
            raw.bytes() == Self::bytes_inner(self.seq_pt().take(n as int)),
            raw.wf(),
        decreases n,
    {
        broadcast use group_vstd_default;

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

    /// Creates a reference to a `PointsToUntyped` from a reference to a `SeqPointsTo<T, PointsTo<T>>`,
    /// with the same address and provenance, a length of `self.len() * size_of::<T>()`,
    /// and the same abstract bytes.
    pub proof fn as_untyped(tracked &self) -> (tracked raw: &PointsToUntyped)
        requires
            self.wf(),
        ensures
            raw.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() * size_of::<T>()) as usize,
                },
            ),
            raw.bytes() == self.bytes(),
            raw.wf(),
    {
        broadcast use group_vstd_default;

        self.untyped_ref_join(self.len())
    }

    /// Mutably borrows the underlying `PointsToUntyped` permissions of all of `perms`, joined into
    /// a single `PointsToUntyped`, where the elements sit at consecutive addresses from `base`.
    /// If the result keeps its pointers and length, then each permission ends up empty and
    /// well-formed, and the permissions' bytes are the result's final bytes.
    proof fn untyped_mut_join(tracked perms: &mut Seq<PointsTo<T>>, base: *mut T) -> (tracked raw:
        &mut PointsToUntyped)
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
            raw.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: base@.addr,
                    provenance: base@.provenance,
                    metadata: (old(perms).len() * size_of::<T>()) as usize,
                },
            ),
            raw.bytes() == Self::bytes_inner(*old(perms)),
            raw.wf(),
            final(perms).len() == old(perms).len(),
            forall|i: int| 0 <= i < final(perms).len() ==> #[trigger] final(perms)[i].is_empty(),
            PointsToUntyped::ptrs_len_same(*raw, *final(raw)) ==> {
                &&& forall|i: int|
                    #![trigger final(perms)[i]]
                    0 <= i < final(perms).len() ==> {
                        &&& final(perms)[i].wf()
                        &&& final(perms)[i].ptr() == old(perms)[i].ptr()
                    }
                &&& Self::bytes_inner(*final(perms)) == final(raw).bytes()
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
            } by {
                assert(init[k] == old_perms[k]);
            }

            // The prefix, joined
            let tracked a = Self::untyped_mut_join(init, base);

            // The last element
            let tracked b = last1.tracked_borrow_mut(0).as_untyped_mut();

            assert(i * size_of::<T>() + size_of::<T>() == old_perms.len() * size_of::<T>())
                by (nonlinear_arith)
                requires
                    i == old_perms.len() - 1,
            ;
            let tracked raw = PointsToUntyped::join_mut(a, b);
            let raw_ref = raw;

            // Final values
            if PointsToUntyped::ptrs_len_same(*raw_ref, *final(raw_ref)) {
                assert((*final(perms_ref)).drop_last() =~= *final(init_ref));            }
            raw
        }
    }

    /// Creates a mutable reference to a `PointsToUntyped` from a mutable reference to a
    /// `SeqPointsTo<T, PointsTo<T>>`, with the same address and provenance and a length of
    /// `self.len() * size_of::<T>()`. If this permission carries any typed values, they are dropped here.
    pub proof fn as_untyped_mut(tracked &mut self) -> (tracked raw: &mut PointsToUntyped)
        requires
            self.wf(),
        ensures
            raw.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: old(self).ptr()@.addr,
                    provenance: old(self).ptr()@.provenance,
                    metadata: (old(self).len() * size_of::<T>()) as usize,
                },
            ),
            raw.bytes() == old(self).bytes(),
            raw.wf(),
            final(self).ptr() == old(self).ptr(),
            final(self).len() == old(self).len(),
            final(self).is_fully_empty(),
            // Criteria necessary for re-establishing invariants
            PointsToUntyped::ptrs_len_same(*raw, *final(raw)) ==> ({
                &&& final(self).bytes() == final(raw).bytes()
                &&& final(self).wf()
            }),
    {
        broadcast use group_vstd_default;

        let base = self.thin_ptr();
        let old_self = *self;
        let self_ref = self;
        let tracked perms = self.tracked_seq_pt_mut();
        let tracked raw = Self::untyped_mut_join(perms, base);
        let raw_ref = raw;

        // Final values
        if PointsToUntyped::ptrs_len_same(*raw_ref, *final(raw_ref)) {
            let new_self = *final(self_ref);
            assert forall|i: int| 0 <= i < new_self.len() implies PointsTo::<
                T,
            >::ptrs_len_same(old_self[i], #[trigger] new_self[i]) by {
                PointsTo::<T>::lemma_ptrs_len_same_valid(old_self[i], new_self[i]);
            }
        }
        raw
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
        broadcast use group_vstd_default;

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
        broadcast use group_vstd_default;

        let tracked val = self.borrow_typed_values(start, (end - start) as nat);
        val
    }

    /// Copies the `TypedValue<T>`s out of a sequence of shared references, given that `T` is `Copy`.
    proof fn copy_typed_values(tracked val: Seq<&TypedValue<T>>) -> (tracked out: Seq<
        TypedValue<T>,
    >) where T: Copy
        ensures
            out == val.map_values(|r: &TypedValue<T>| *r),
        decreases val.len(),
    {
        broadcast use group_vstd_default;

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
        broadcast use group_vstd_default;

        let tracked copied = Self::copy_typed_values(val);
        self.put_typed_value_subrange(start, copied);
    }

    /// This moves a subrange of the `TypedValue<T>`s out from `self`, leaving that subrange empty.
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
        broadcast use group_vstd_default;

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

    /// The flattened abstract bytes depend only on the abstract bytes of each individual permission.
    proof fn bytes_inner_ext(a: Seq<PointsTo<T>>, b: Seq<PointsTo<T>>)
        requires
            a.len() == b.len(),
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].bytes() == b[i].bytes(),
        ensures
            Self::bytes_inner(a) == Self::bytes_inner(b),
        decreases a.len(),
    {
        broadcast use group_vstd_default;

        if a.len() > 0 {
            Self::bytes_inner_ext(a.drop_last(), b.drop_last());
        }
    }

    /// Consumes the `Seq<T>` and puts it in the specified subrange of the `TypedValue<T>`s for `self`.
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
            final(self).is_valid_subrange(start, val.len()),
            final(self).value_subrange(start, val.len()) == val,
            forall|i: int|
                0 <= i < old(self).len() && !(start <= i < start + val.len())
                    ==> #[trigger] final(self).seq_typed_value()[i] == old(self).seq_typed_value()[i],
            final(self).wf(),
        decreases val.len(),
    {
        broadcast use group_vstd_default;

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

    /// Consumes the `Seq<TypedValue<T>>` and puts it in the specified subrange of the
    /// `TypedValue<T>`s for `self`.
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
            final(self).seq_typed_value() == old(self).seq_typed_value().update_subrange_with(start, val),
            final(self).wf(),
        decreases val.len(),
    {
        broadcast use group_vstd_default;

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

    /// Copies the first `n` values out of a shared reference to a sequence, given that `T` is `Copy`.
    proof fn copy_values(tracked val: &Seq<T>, n: nat) -> (tracked out: Seq<T>) where T: Copy
        requires
            n <= val.len(),
        ensures
            out == val.take(n as int),
        decreases n,
    {
        broadcast use group_vstd_default;

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
            final(self).is_valid_subrange(start, val.len()),
            final(self).value_subrange(start, val.len()) == val,
            forall|i: int|
                0 <= i < old(self).len() && !(start <= i < start + val.len())
                    ==> #[trigger] final(self).seq_typed_value()[i] == old(self).seq_typed_value()[i],
            final(self).wf(),
    {
        broadcast use group_vstd_default;

        let tracked copied = Self::copy_values(val, val.len());
        assert(copied =~= *val);
        self.put_subrange(start, copied);
    }

    /// This moves a subrange of the values out from `self`, leaving that subrange empty.
    pub proof fn take_subrange(tracked &mut self, start: int, end: int) -> (tracked val: Seq<T>)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
            self.is_valid_subrange(start, (end - start) as nat),
        ensures
            val == old(self).value_subrange(start, (end - start) as nat),
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).seq_typed_value() == old(self).seq_typed_value().update_subrange_with(
                start,
                Seq::new((end - start) as nat, |i: int| TypedValue::Empty),
            ),
            final(self).wf(),
        decreases end - start,
    {
        broadcast use group_vstd_default;

        if start == end {
            Seq::tracked_empty()
        } else {
            let old_self = *self;

            // Take the last value in the range out of the element at `end - 1`
            let tracked elt = self.index_mut(end - 1);
            let tracked taken = elt.take();

            // The bytes of the whole sequence are unchanged
            Self::bytes_inner_ext(old_self.seq_pt(), self.seq_pt());

            // Take the rest of the range out of the preceding elements
            let tracked mut val = self.take_subrange(start, end - 1);
            val.tracked_push(taken);

            val
        }
    }

    /// Takes a borrow of each of the `n` (valid) values starting at index `start`.
    proof fn borrow_values(tracked &self, start: int, n: nat) -> (tracked val: Seq<&T>)
        requires
            self.wf(),
            self.is_valid_subrange(start, n),
        ensures
            val.len() == n,
            forall|i: int| 0 <= i < n ==> *#[trigger] val[i] == self[start + i].value(),
        decreases n,
    {
        broadcast use group_vstd_default;

        if n == 0 {
            Seq::tracked_empty()
        } else {
            let tracked mut val = self.borrow_values(start, (n - 1) as nat);
            let j = start + n - 1;
            let tracked last = self.tracked_seq_pt().tracked_borrow(j).borrow_value();
            val.tracked_push(last);
            val
        }
    }

    /// This takes a borrow of each of the values in a subrange of `self`.
    pub proof fn borrow_value_subrange(tracked &self, start: int, end: int) -> (tracked val: Seq<&T>)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
            self.is_valid_subrange(start, (end - start) as nat),
        ensures
            val.map_values(|r: &T| *r) == self.value_subrange(start, (end - start) as nat),
    {
        broadcast use group_vstd_default;

        let tracked val = self.borrow_values(start, (end - start) as nat);
        val
    }

    // Commented out along with `PointsTo::borrow_mut`, which these depend on.
    // /// Takes a mutable borrow of the `T` in each of the (valid) permissions in `perms`.
    // proof fn borrow_mut_values(tracked perms: &mut Seq<PointsTo<T>>) -> (tracked ret: Seq<&mut T>)
    //     requires
    //         forall|i: int|
    //             0 <= i < perms.len() ==> #[trigger] perms[i].wf() && perms[i].is_valid(),
    //     ensures
    //         ret.len() == old(perms).len(),
    //         final(perms).len() == old(perms).len(),
    //         forall|i: int|
    //             #![trigger ret[i]]
    //             #![trigger final(perms)[i]]
    //             0 <= i < ret.len() ==> {
    //                 &&& *ret[i] == old(perms)[i].value()
    //                 &&& final(perms)[i].is_valid()
    //                 &&& final(perms)[i].ptr() == old(perms)[i].ptr()
    //                 &&& final(perms)[i].value() == *final(ret[i])
    //                 &&& PointsTo::<T>::ptrs_len_same_valid(old(perms)[i], final(perms)[i])
    //                 &&& final(perms)[i].wf()
    //             },
    //         forall|i: int|
    //             #![trigger final(perms)[i]]
    //             0 <= i < final(perms).len() ==> final(perms)[i].ptr() == old(perms)[i].ptr(),
    //     decreases perms.len(),
    // {
    //     if perms.len() == 0 {
    //         Seq::tracked_empty()
    //     } else {
    //         let old_perms = *perms;
    //         let perms_ref = perms;
    //         assert(old_perms[0].wf() && old_perms[0].is_valid());
    //         let tracked (first, rest) = perms.tracked_split_borrow_mut(1);
    //         assert(first[0] == old_perms[0]);
    //         let tracked elt = first.tracked_borrow_mut(0);
    //         let elt_ref = elt;
    //         let tracked v = elt.borrow_mut();
    //         assert forall|i: int| 0 <= i < rest.len() implies #[trigger] rest[i].wf()
    //             && rest[i].is_valid() by {
    //             assert(rest[i] == old_perms[i + 1]);
    //             assert(old_perms[i + 1].wf());
    //         }
    //         let rest_ref = rest;
    //         let tracked mut ret = Self::borrow_mut_values(rest);
    //         let ret_rest = ret;
    //         ret.tracked_insert(0, v);
    //         assert(final(perms_ref)[0] == *final(elt_ref));
    //         assert forall|i: int| 0 < i < ret.len() implies #[trigger] ret[i] == ret_rest[i - 1]
    //             && final(perms_ref)[i] == final(rest_ref)[i - 1] && old_perms[i] == old_perms.skip(
    //             1,
    //         )[i - 1] by {}
    //         ret
    //     }
    // }
    //
    // /// This takes a mutable borrow of each of the values in a subrange of `self`.
    // pub proof fn borrow_mut_subrange(tracked &mut self, start: int, end: int) -> (tracked ret: Seq<
    //     &mut T,
    // >)
    //     requires
    //         self.wf(),
    //         0 <= start <= end <= self.len(),
    //         self.is_valid_subrange(start, (end - start) as nat),
    //     ensures
    //         ret.len() == end - start,
    //         ret.map_values(|r: &mut T| *r) == old(self).value_subrange(
    //             start,
    //             (end - start) as nat,
    //         ),
    //         final(self).ptr() == old(self).ptr(),
    //         final(self).seq_typed_value() == old(self).seq_typed_value().update_subrange_with(
    //             start,
    //             Seq::new(ret.len(), |i: int| TypedValue::Valid(Tracked(*final(ret[i])))),
    //         ),
    //         Self::ptrs_len_same_valid(*old(self), *final(self)),
    //         final(self).wf(),
    // {
    //     let old_self = *self;
    //     let self_ref = self;
    //     let tracked sub = self.seq_pt.tracked_borrow_subrange_mut(start, end);
    //     let sub_ref = sub;
    //     assert forall|i: int| 0 <= i < sub.len() implies #[trigger] sub[i].wf()
    //         && sub[i].is_valid() by {
    //         assert(old_self[start + i].wf_basic());
    //     }
    //     let tracked ret = Self::borrow_mut_values(sub);
    //
    //     let new_self = *final(self_ref);
    //     assert(new_self.seq_pt() == old_self.seq_pt().subrange(0, start) + *final(sub_ref)
    //         + old_self.seq_pt().subrange(end, old_self.len() as int));
    //     assert forall|i: int| 0 <= i < new_self.len() implies {
    //         &&& (start <= i < end ==> #[trigger] new_self[i] == final(sub_ref)[i - start])
    //         &&& (!(start <= i < end) ==> new_self[i] == old_self[i])
    //     } by {}
    //
    //     assert(ret.map_values(|r: &mut T| *r) =~= old_self.value_subrange(
    //         start,
    //         (end - start) as nat,
    //     ));
    //     assert(new_self.seq_typed_value() =~= old_self.seq_typed_value().update_subrange_with(
    //         start,
    //         Seq::new(ret.len(), |i: int| TypedValue::Valid(Tracked(*final(ret[i])))),
    //     )) by {
    //         assert forall|i: int| 0 <= i < new_self.len() implies new_self.seq_typed_value()[i]
    //             == old_self.seq_typed_value().update_subrange_with(
    //             start,
    //             Seq::new(ret.len(), |i: int| TypedValue::Valid(Tracked(*final(ret[i])))),
    //         )[i] by {
    //             if start <= i < end {
    //                 assert(ret[i - start] == ret[i - start]);
    //             }
    //         }
    //     }
    //
    //     // Re-establishing invariants
    //     assert forall|i: int| 0 <= i < new_self.len() implies {
    //         &&& PointsTo::<T>::ptrs_len_same_valid(old_self[i], #[trigger] new_self[i])
    //         &&& new_self[i].wf()
    //     } by {
    //         assert(old_self[i].wf_basic());
    //         if start <= i < end {
    //             assert((*sub_ref)[i - start] == old_self[i]);
    //             assert(new_self[i] == final(sub_ref)[i - start]);
    //         } else {
    //             assert(new_self[i] == old_self[i]);
    //         }
    //     }
    //     assert(new_self.wf_basic());
    //     ret
    // }

    /// Splits the `SeqPointsTo` into two permissions at the index boundary `mid`.
    pub proof fn split(tracked self, mid: nat) -> (tracked (first, second): (Self, Self))
        requires
            0 <= mid <= self.len(),
            self.wf(),
        ensures
            first.seq_pt() == self.seq_pt().take(mid as int),
            second.seq_pt() == self.seq_pt().skip(mid as int),
            first.bytes() == self.bytes().take(mid as int * size_of::<T>()),
            second.bytes() == self.bytes().skip(mid as int * size_of::<T>()),
            first.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: mid as usize,
            }),
            second.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: (self.ptr()@.addr + mid * size_of::<T>()) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (self.len() - mid) as usize,
            }),
            first.wf(),
            second.wf(),
    {
        broadcast use group_vstd_default;

        if self.len() != 0 && size_of::<T>() != 0 {
            assert(self.len() * size_of::<T>() != 0) by (nonlinear_arith)
                requires
                    self.len() != 0,
                    size_of::<T>() != 0,
            ;
            self.provenance_not_none();
            self.ptr_bounds();
        }
        let ghost_self = self;

        let tracked (first, second) = self.split_basic(mid);

        Self::bytes_subrange(ghost_self.seq_pt(), mid as int);

        if ghost_self.len() == 0 || size_of::<T>() == 0 {
            assert(mid * size_of::<T>() == 0) by (nonlinear_arith)
                requires
                    mid == 0 || size_of::<T>() == 0,
            ;
        } else {
            assert(mid * size_of::<T>() <= ghost_self.len() * size_of::<T>()) by (nonlinear_arith)
                requires
                    mid <= ghost_self.len(),
            ;
            assert((ghost_self.ptr()@.addr + mid * size_of::<T>()) as nat % align_of::<T>() == 0)
                by {
                broadcast use
                    crate::vstd::arithmetic::div_mod::lemma_mul_mod_noop_right,
                    crate::vstd::arithmetic::div_mod::lemma_add_mod_noop,
                    layout_of_sized,
                ;

            }
        }
        (first, second)
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
            joined.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: (self.len() + other.len()) as usize,
            }),
            joined.seq_pt() == self.seq_pt() + other.seq_pt(),
            joined.bytes() == self.bytes() + other.bytes(),
            joined.wf(),
    {
        broadcast use group_vstd_default;

        let ghost_self = self;
        let ghost_other = other;

        let tracked joined = self.join_basic(other);

        Self::bytes_subrange(joined.seq_pt(), ghost_self.len() as int);
        assert(joined.seq_pt().subrange(0, ghost_self.len() as int) =~= ghost_self.seq_pt());
        assert(joined.seq_pt().subrange(ghost_self.len() as int, joined.len() as int)
            =~= ghost_other.seq_pt());
        joined
    }

    /// Given that the subrange is within bounds, it is always possible to borrow a permission
    /// to just that subrange.
    pub proof fn subrange(tracked &self, start_index: nat, len: nat) -> (tracked sub: &Self)
        requires
            self.wf(),
            start_index + len <= self.len(),
        ensures
            sub.wf(),
            sub.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: (self.ptr()@.addr + start_index * size_of::<T>()) as usize,
                provenance: self.ptr()@.provenance,
                metadata: len as usize,
            }),
            sub.seq_pt() == self.seq_pt().subrange(start_index as int, (start_index + len) as int),
    {
        broadcast use group_vstd_default;

        // The subrange's address is aligned (same reasoning as in `split`)
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
        } else {
            assert(start_index * size_of::<T>() == 0) by (nonlinear_arith)
                requires
                    self.len() == 0 || size_of::<T>() == 0,
                    start_index <= self.len(),
            ;
        }
        self.subrange_basic(start_index, len)
    }

    /// Specializes `is_disjoint` to the case when the other permission is a `SeqPointsTo<S, PointsTo<S>>`.
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
}

// Not in `group_vstd_default`.
// While porting, code that needs these lemmas may need an explicit `broadcast use`.
pub broadcast group group_points_to_collections_lemmas {
    SeqPointsTo::lemma_ptrs_len_same_valid,
}

} // verus!
