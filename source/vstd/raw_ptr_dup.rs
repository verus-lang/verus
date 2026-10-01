// Kept for reference for when I can go back to using type_invariant
// impl<T: ?Sized> PointsTo<T> {
//     /// Guarantee that the `PointsTo` points to an aligned address.
//     /// See: <https://doc.rust-lang.org/reference/behavior-considered-undefined.html#r-undefined.validity.reference-box>
//     /// See: <https://doc.rust-lang.org/std/ptr/index.html#alignment>
//     #[verifier::type_invariant]
//     pub closed spec fn inv(self) -> bool {
//         let v: &T = arbitrary();
//         self.inner.ptr()@.addr as int % spec_align_of_val::<T>(v) as int == 0
//     }
// }

impl<T> PointsTo<[T]> {
    /// The sequence of (possibly uninitialized) memory that this permission gives access to.
    /// Delegates to the underlying `PointsToUnaligned<[T]>`.
    pub closed spec fn mem_contents_seq(&self) -> Seq<MemContents<T>> {
        self.inner.mem_contents_seq()
    }

    /// The length of the memory that this permission gives access to.
    #[verifier::inline]
    pub open spec fn len(self) -> nat {
        self.mem_contents_seq().len()
    }

    /// `[]` operator, synonymous with `index`.
    #[verifier::inline]
    pub open spec fn spec_index(self, index: nat) -> MemContents<T>
        recommends
            0 <= index < self.len(),
    {
        self.mem_contents_seq()[index as int]
    }

    /// Returns `true` if all of the permission's associated memory is initialized.
    #[verifier::inline]
    pub open spec fn is_init(&self) -> bool {
        self.is_init_subrange(0, self.mem_contents_seq().len())
    }

    /// Returns `true` if all of the permission's associated memory in the given subrange is initialized.
    #[verifier::inline]
    pub open spec fn is_init_subrange(&self, start_index: int, len: nat) -> bool {
        &&& 0 <= start_index <= start_index + len <= self.mem_contents_seq().len()
        &&& forall|i|
            start_index <= i < start_index + len ==> self.mem_contents_seq().index(i).is_init()
    }

    /// Returns `true` if any part of the permission's associated memory is uninitialized.
    #[verifier::inline]
    pub open spec fn is_uninit(&self) -> bool {
        !self.is_init()
    }

    /// Returns `true` if all of the permission's associated memory is uninitialized.
    #[verifier::inline]
    pub open spec fn is_fully_uninit(&self) -> bool {
        forall|i|
            0 <= i < self.mem_contents_seq().len() ==> self.mem_contents_seq().index(i).is_uninit()
    }

    /// Returns a sequence where for each index,
    /// if the permission's associated memory at that index is initialized,
    /// the corresponding index in the sequence holds that value.
    /// Otherwise, the value at that index is meaningless.
    #[verifier::inline]
    pub open spec fn value(&self) -> Seq<T>
        recommends
            self.is_init(),
    {
        self.value_subrange(0, self.mem_contents_seq().len())
    }

    /// Returns a sequence where for each index in the given range,
    /// if the permission's associated memory at that index is initialized,
    /// the corresponding index in the sequence holds that value.
    /// Otherwise, the value at that index is meaningless.
    #[verifier::inline]
    pub open spec fn value_subrange(&self, start_index: int, len: nat) -> Seq<T>
        recommends
            0 <= start_index <= start_index + len <= self.mem_contents_seq().len(),
            self.is_init_subrange(start_index, len),
    {
        Seq::new(len, |i| self.mem_contents_seq().index(start_index + i).value())
    }

    /// Guarantee that the `PointsTo` points to a non-null address.
    ///
    /// Note that the size of a slice is given by the length * `size_of::<\T\>()`.
    /// <https://doc.rust-lang.org/reference/type-layout.html#slice-layout>
    pub proof fn is_nonnull(tracked &self)
        ensures
            self.ptr()@.addr != 0,
    {
        self.inner.is_nonnull();
    }

    /// A `PointsTo<[T]>` is always aligned to `T`.
    pub proof fn is_aligned(tracked &self)
        ensures
            self.ptr()@.addr as int % layout::align_of::<T>() as int == 0,
    {
        broadcast use group_layout_axioms;

        use_type_invariant(self);
    }

    /// The memory associated with a pointer should always be within bounds of its spatial provenance.
    pub proof fn ptr_bounds(tracked &self)
        requires
            self.ptr()@.provenance.is_some(),
        ensures
            self.ptr()@.provenance.data().start_addr() <= self.ptr()@.addr,
            self.ptr()@.addr + self.mem_contents_seq().len() * size_of::<T>()
                <= self.ptr()@.provenance.data().start_addr()
                + self.ptr()@.provenance.data().alloc_len(),
    {
        self.inner.ptr_bounds();
    }

    /// If the memory covered by this permission is not zero-sized,
    /// then the pointer's provenance is non-null.
    pub proof fn provenance_non_null(tracked &self)
        requires
            layout::size_of::<T>() * self.len() != 0,
        ensures
            self.ptr()@.provenance != Provenance::None,
    {
        self.inner.provenance_non_null();
    }

    /// Given that the subrange is within bounds, it is always possible to get a permission to just that subrange.
    pub proof fn subrange(tracked &self, start_index: nat, len: nat) -> (tracked sub_points_to:
        &Self)
        requires
            start_index + len <= self.mem_contents_seq().len(),
        ensures
            sub_points_to.ptr() == ptr_mut_from_data::<[T]>(
                PtrData {
                    addr: ((self.ptr()@.addr + start_index * size_of::<T>()) as usize),
                    provenance: self.ptr()@.provenance,
                    metadata: (len as usize),
                },
            ),
            sub_points_to.mem_contents_seq() == self.mem_contents_seq().subrange(
                start_index as int,
                start_index as int + len as int,
            ),
    {
        broadcast use {axiom_ptr_mut_from_data, group_layout_axioms, alloc_bound};

        let tracked unaligned_self_ref = self.as_unaligned();

        if start_index > 0 && size_of::<T>() > 0 {
            assert(self.mem_contents_seq().len() > 0);
            assert(self.mem_contents_seq().len() * size_of::<T>() != 0) by (nonlinear_arith)
                requires
                    self.mem_contents_seq().len() > 0,
                    size_of::<T>() > 0,
            ;
            unaligned_self_ref.provenance_non_null();
            unaligned_self_ref.ptr_bounds();
            assert(start_index * size_of::<T>() <= self.mem_contents_seq().len() * size_of::<T>())
                by (nonlinear_arith)
                requires
                    start_index <= self.mem_contents_seq().len(),
                    size_of::<T>() >= 0,
            ;
            assert(self.ptr()@.addr + start_index * size_of::<T>() <= usize::MAX as int + 1)
                by (nonlinear_arith)
                requires
                    self.ptr()@.addr <= usize::MAX as int + 1,
                    start_index == 0 || size_of::<T>() == 0 || (self.ptr()@.addr
                        + self.mem_contents_seq().len() * size_of::<T>()
                        <= self.ptr()@.provenance.data().start_addr()
                        + self.ptr()@.provenance.data().alloc_len()
                        && self.ptr()@.provenance.data().start_addr()
                        + self.ptr()@.provenance.data().alloc_len() <= usize::MAX as int + 1
                        && start_index * size_of::<T>() <= self.mem_contents_seq().len()
                        * size_of::<T>()),
            ;

        } else {
            assert(start_index * size_of::<T>() == 0) by (nonlinear_arith)
                requires
                    start_index == 0 || size_of::<T>() == 0,
                    start_index >= 0,
                    size_of::<T>() >= 0,
            ;
        }

        use_type_invariant(&*self);
        assert((self.ptr()@.addr + start_index * size_of::<T>()) as nat % align_of::<T>() == 0) by {
            broadcast use {lemma_mul_mod_noop_right, lemma_add_mod_noop, layout_of_sized};

        };

        let tracked unaligned_sub = self.inner.subrange(start_index, len);

        assert(unaligned_sub.ptr()@.addr as int % align_of::<T>() as int == 0) by {
            let exact_addr = self.ptr()@.addr + start_index * size_of::<T>();

            let expected_data = PtrData::<[T]> {
                addr: (exact_addr as usize),
                provenance: self.ptr()@.provenance,
                metadata: (len as usize),
            };
            assert(ptr_mut_from_data::<[T]>(expected_data)@ == expected_data);

            if exact_addr as int <= usize::MAX as int {
                assert((exact_addr as usize) as int == exact_addr as int);
            } else {
                assert(exact_addr as int == usize::MAX as int + 1);

                assert(arch_word_bits() == 64 ==> ((u64::MAX as int + 1) as usize) as int == 0)
                    by (bit_vector);
                assert(arch_word_bits() == 32 ==> ((u32::MAX as int + 1) as usize) as int == 0)
                    by (bit_vector);

                assert(((usize::MAX as int + 1) as usize) as int == 0);
                assert(0 as int % align_of::<T>() as int == 0);
            }
        };

        unaligned_sub.as_aligned()
    }

    /// We can cast a `[T]` permission to a `V` permission under the following conditions:
    ///
    /// (1) `T` and `V` are integer types where `V` is a power of 2
    /// and the bit encoding of a `V` can be viewed as
    /// the bit encoding for multiple `T`s
    /// (as defined precisely in the trait `CompatibleSmallerBaseFor<V>`).
    ///
    /// (2) Memory is initialized.
    ///
    /// (3) The pointer's address is aligned to `V`.
    ///
    /// (4) `self.value().len() * size_of::<T>() == size_of::<V>()`.
    pub proof fn cast_points_to<V>(tracked &self) -> (tracked points_to: &PointsTo<V>) where
        T: CompatibleSmallerBaseFor<V> + Integer,
        V: BasePow2 + Integer,

        requires
            self.is_init(),
            self.ptr()@.addr as int % align_of::<V>() as int == 0,
            self.value().len() * size_of::<T>() == size_of::<V>(),
        ensures
            points_to.ptr() == ptr_mut_from_data::<V>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (),
                },
            ),
            points_to.is_init(),
            points_to.value() as int == to_big_from_digits::<V, T>(self.value()).index(0),
    {
        broadcast use {axiom_ptr_mut_from_data, crate::vstd::group_vstd_default};

        let tracked ua = self.as_unaligned();
        let tracked pt_unaligned = ua.cast_points_to_unaligned::<V>();
        pt_unaligned.as_aligned()
    }

    /// Like `cast_points_to`, but does not require alignment,
    /// producing a `PointsToUnaligned<V>` instead of a `PointsTo<V>`.
    ///
    /// We can cast a `[T]` permission to an unaligned `V` permission under the following conditions:
    ///
    /// (1) `T` and `V` are integer types where `V` is a power of 2
    /// and the bit encoding of a `V` can be viewed as
    /// the bit encoding for multiple `T`s
    /// (as defined precisely in the trait `CompatibleSmallerBaseFor<V>`).
    ///
    /// (2) Memory is initialized.
    ///
    /// (3) `self.value().len() * size_of::<T>() == size_of::<V>()`.
    ///
    /// Note: unlike `cast_points_to`, there is no alignment precondition.
    /// Delegates to the underlying `PointsToUnaligned<[T]>`.
    pub proof fn cast_points_to_unaligned<V>(tracked &self) -> (tracked points_to:
        &PointsToUnaligned<V>) where T: CompatibleSmallerBaseFor<V> + Integer, V: BasePow2 + Integer
        requires
            self.is_init(),
            self.value().len() * size_of::<T>() == size_of::<V>(),
        ensures
            points_to.ptr() == ptr_mut_from_data::<V>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (),
                },
            ),
            points_to.is_init(),
            points_to.value() as int == to_big_from_digits::<V, T>(self.value()).index(0),
    {
        broadcast use crate::vstd::group_vstd_default;

        let tracked ua = self.as_unaligned();
        ua.cast_points_to_unaligned::<V>()
    }

    /// Guarantees that the memory ranges associated with two distinct, non-ZST permissions will not overlap,
    /// since you cannot have two permissions to the same memory.
    /// (`self` is an &mut reference to enforce distinctness,
    /// so you cannot pass the same PointsTo as both arguments.)
    /// Since both S and T are non-zero-sized, this implies the pointers have distinct addresses.
    ///
    /// Note: If either S or T is zero-sized, we get disjointness "for free" without having to call this axiom,
    /// since the empty memory range corresponding to a ZST cannot possibly intersect with any other memory.
    /// However, note that if one type is a ZST and the other is a non-ZST,
    /// the disjointness definition as stated here here does not hold,
    /// since the ZST pointer could be in the middle of the non-ZST's range.
    pub proof fn is_disjoint<S>(tracked &mut self, tracked other: &PointsTo<[S]>)
        requires
            size_of::<T>() * old(self).mem_contents_seq().len() != 0,
            size_of::<S>() * other.mem_contents_seq().len() != 0,
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + size_of::<T>() * final(self).mem_contents_seq().len()
                <= other.ptr() as int || other.ptr() as int + size_of::<S>()
                * other.mem_contents_seq().len() <= final(self).ptr() as int,
    {
        broadcast use layout_of_sized;

        use_type_invariant(&*self);
        self.inner.is_disjoint(&other.inner)
    }

    /// Convert an aligned `PointsTo<[\T\]>` to an unaligned `PointsToUnaligned<[\T\]>`.
    /// This is always safe since aligned is stricter than unaligned.
    ///
    /// De-axiomitized: simply returns the inner [`PointsToUnaligned<[T]>`](PointsToUnaligned).
    pub proof fn into_unaligned(tracked self) -> (tracked perm: PointsToUnaligned<[T]>)
        ensures
            perm.ptr() == self.ptr(),
            perm.mem_contents_seq() == self.mem_contents_seq(),
    {
        self.inner
    }

    /// Borrow an aligned `PointsTo<[\T\]>` as an unaligned `PointsToUnaligned<[\T\]>`.
    /// This is always safe since aligned is stricter than unaligned.
    ///
    /// De-axiomitized: simply borrows the inner `PointsToUnaligned<[\T\]>`.
    pub proof fn as_unaligned(tracked &self) -> (tracked perm: &PointsToUnaligned<[T]>)
        ensures
            perm.ptr() == self.ptr(),
            perm.mem_contents_seq() == self.mem_contents_seq(),
    {
        &self.inner
    }

    /// Invariant: For all elements in this slice of memory, the corresponding abstract bytes must decode into the value in memory.
    pub axiom fn abstract_bytes_decode(&self)
        ensures
            forall|i: int|
                0 <= i < self.mem_contents_seq().len() ==> {
                    &&& (#[trigger] self.mem_contents_seq()[i]).is_init() ==> abs_decode::<T>(
                        self.abstract_bytes().subrange(
                            i * layout::size_of::<T>(),
                            (i + 1) * layout::size_of::<T>(),
                        ),
                        &self.mem_contents_seq()[i].value(),
                    )
                    &&& self.mem_contents_seq()[i].is_uninit() ==> self.abstract_bytes().subrange(
                        i * layout::size_of::<T>(),
                        (i + 1) * layout::size_of::<T>(),
                    ).len() == size_of::<T>()
                },
            self.abstract_bytes().len() == self.mem_contents_seq().len() * layout::size_of::<T>(),
    ;

    /// We can always convert a `PointsTo<[T]>` into a `SeqPointsTo<T>` for the same pointer,
    /// whose elements are individual `PointsTo<T>` with the memory contents of the corresponding index.
    pub proof fn into_seq_pt(tracked self) -> (tracked s: SeqPointsTo<T>)
        ensures
            forall|i|
                #![trigger s[i].mem_contents()]
                #![trigger self.mem_contents_seq()[i as int]]
                #![trigger s[i].ptr()@.provenance]
                #![trigger s[i].ptr()@.addr]
                0 <= i < self.mem_contents_seq().len() ==> {
                    &&& s[i].mem_contents() == self.mem_contents_seq()[i as int]
                    &&& s[i].ptr()@.provenance == s.ptr()@.provenance
                    &&& s[i].ptr()@.addr == s.ptr()@.addr + i * layout::size_of::<T>()
                },
            s.ptr() == self.ptr() as *mut T,
            s.len() == self.mem_contents_seq().len(),
            s.abstract_bytes() == self.abstract_bytes(),
            s.wf(),
    {
        broadcast use layout_of_sized;
        broadcast use layout_of_slices;

        let ghost v: &[T] = arbitrary();
        assert(spec_align_of_val::<[T]>(v) == align_of::<T>());
        use_type_invariant(&self);
        self.inner.into_seq_pt()
    }

    /// Same as `into_seq_pt`, but for `&PointsTo<[T]>`.
    pub proof fn into_seq_pt_shared(tracked &self) -> (tracked s: &SeqPointsTo<T>)
        ensures
            forall|i|
                #![trigger s[i].mem_contents()]
                #![trigger self.mem_contents_seq()[i as int]]
                #![trigger s[i].ptr()@.provenance]
                #![trigger s[i].ptr()@.addr]
                0 <= i < self.mem_contents_seq().len() ==> {
                    &&& s[i].mem_contents() == self.mem_contents_seq()[i as int]
                    &&& s[i].ptr()@.provenance == s.ptr()@.provenance
                    &&& s[i].ptr()@.addr == s.ptr()@.addr + i * layout::size_of::<T>()
                },
            s.ptr() == self.ptr() as *mut T,
            s.len() == self.mem_contents_seq().len(),
            s.abstract_bytes() == self.abstract_bytes(),
            s.wf(),
    {
        broadcast use layout_of_sized;
        broadcast use layout_of_slices;

        let ghost v: &[T] = arbitrary();
        assert(spec_align_of_val::<[T]>(v) == align_of::<T>());
        use_type_invariant(self);
        self.inner.into_seq_pt_shared()
    }

    pub axiom fn tracked_borrow(tracked &self) -> (tracked r: &[T])
        requires
            self.is_init(),
        ensures
            (*r)@ == self.value(),
    ;

    pub axiom fn tracked_borrow_mut(tracked &mut self) -> (tracked r: &mut [T])
        requires
            self.is_init(),
        ensures
            (*r)@ == old(self).value(),
            mut_ref_ptr(r) == old(self).ptr(),
            //
            final(self).is_init(),
            final(self).ptr() == old(self).ptr(),
            final(self).value() == (*final(r))@,
    ;

    /// Creates a `PointsTo<T>` from a `PointsToUnaligned<[u8]>` from with the same provenance
    /// and a ptr corresponding to the range of the `PointsToUnaligned<[u8]>`.
    /// The resulting `PointsTo<T>` will be uninitialized.
    pub axiom fn from_untyped(tracked raw: PointsToUnaligned<[u8]>, len: usize) -> (tracked out:
        Self)
        requires
            raw.ptr()@.addr as int % layout::align_of::<T>() as int == 0,
            layout::size_of::<T>() * len == raw.ptr()@.metadata,
        ensures
            out.ptr()@.addr == raw.ptr()@.addr,
            out.ptr()@.provenance == raw.ptr()@.provenance,
            out.ptr()@.metadata == len,
            out.abstract_bytes() == raw.abstract_bytes(),
            out.is_fully_uninit(),
    ;

    /// Creates a reference to a `PointsToUnaligned<[u8]>` from a reference to a `PointsTo<V>` with the same provenance
    /// and a range corresponding to the address of the `PointsTo<V>`, size of `V`, and length of the pointer.
    pub axiom fn as_untyped(tracked &self) -> (tracked raw: &PointsToUnaligned<[u8]>)
        ensures
            self.ptr()@.addr == raw.ptr()@.addr,
            self.ptr()@.provenance == raw.ptr()@.provenance,
            self.ptr()@.metadata * layout::size_of::<T>() == raw.ptr()@.metadata,
            self.abstract_bytes() == raw.abstract_bytes(),
            raw.is_fully_uninit(),
    ;

    /// Creates a mutable reference to a `PointsToUnaligned<[u8]>` from a reference to a `PointsTo<[V]>` with the same provenance
    /// and a range corresponding to the address of the `PointsTo<[V]>`, size of `V`, and length of the pointer.
    /// If this permission carries any MemContents, they are dropped here.
    pub axiom fn as_untyped_mut(tracked &mut self) -> (tracked raw: &mut PointsToUnaligned<[u8]>)
        ensures
            old(self).ptr()@.addr == raw.ptr()@.addr,
            old(self).ptr()@.provenance == raw.ptr()@.provenance,
            old(self).ptr()@.metadata * layout::size_of::<T>() == raw.ptr()@.metadata,
            old(self).abstract_bytes() == raw.abstract_bytes(),
            raw.is_fully_uninit(),
            final(raw).ptr() == raw.ptr() ==> ({
                &&& final(self).ptr() == old(self).ptr()
                &&& final(self).abstract_bytes() == final(raw).abstract_bytes()
                &&& final(self).is_uninit()
            }),
    ;

    /// This takes a borrow of a subrange of the `MemContents<V>` out from `self`.
    pub axiom fn borrow_mem_contents_subrange(tracked &self, start: int, end: int) -> (tracked val:
        &Seq<MemContents<T>>)
        requires
            0 <= start <= end <= self.mem_contents_seq().len(),
        ensures
            val == self.mem_contents_seq().subrange(start, end),
    ;

    // TODO: could be proved with other low-level axioms and Seq tracked_ proof fns.
    pub axiom fn copy_mem_contents_subrange(
        tracked &mut self,
        start: int,
        tracked val: &Seq<MemContents<T>>,
    ) where T: Copy
        requires
            0 <= start <= start + val.len() <= old(self).mem_contents_seq().len(),
            forall|i|
                0 <= i < val.len() ==> {
                    (#[trigger] val[i]).is_init() ==> abs_decode::<T>(
                        old(self).abstract_bytes().subrange(
                            (start + i) * layout::size_of::<T>(),
                            (start + i + 1) * layout::size_of::<T>(),
                        ),
                        &val[i].value(),
                    )
                },
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).abstract_bytes() == old(self).abstract_bytes(),
            final(self).mem_contents_seq() == old(self).mem_contents_seq().update_subrange_with(
                start,
                *val,
            ),
    ;

    /// This moves a subrange of the `MemContents<V>` out from `self`.
    pub axiom fn take_mem_contents_subrange(
        tracked &mut self,
        start: int,
        end: int,
    ) -> (tracked val: Seq<MemContents<T>>)
        requires
            0 <= start <= end <= old(self).mem_contents_seq().len(),
        ensures
            val == old(self).mem_contents_seq().subrange(start, end),
            final(self).ptr() == old(self).ptr(),
            final(self).abstract_bytes() == old(self).abstract_bytes(),
            final(self).mem_contents_seq() == old(self).mem_contents_seq().update_subrange_with(
                start,
                Seq::new(end as nat, |i| MemContents::Uninit),
            ),
    ;

    // Consumes the `Seq<V>` and puts it in the specified subrange of the `MemContents<T>` for `self`.
    pub axiom fn put_subrange(tracked &mut self, start: int, tracked val: Seq<T>)
        requires
            0 <= start <= start + val.len() <= old(self).mem_contents_seq().len(),
            forall|i|
                0 <= i < val.len() ==> {
                    abs_decode::<T>(
                        old(self).abstract_bytes().subrange(
                            (start + i) * layout::size_of::<T>(),
                            (start + i + 1) * layout::size_of::<T>(),
                        ),
                        &val[i],
                    )
                },
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).abstract_bytes() == old(self).abstract_bytes(),
            final(self).mem_contents_seq() == old(self).mem_contents_seq().update_subrange_with(
                start,
                Seq::new(val.len(), |i| MemContents::Init(val[i])),
            ),
    ;

    // Consumes the `Seq<MemContents<V>>` and puts it in the specified subrange of the `MemContents<T>` for `self`.
    pub axiom fn put_mem_contents_subrange(
        tracked &mut self,
        start: int,
        tracked val: Seq<MemContents<T>>,
    )
        requires
            0 <= start <= start + val.len() <= old(self).mem_contents_seq().len(),
            forall|i|
                0 <= i < val.len() ==> {
                    (#[trigger] val[i]).is_init() ==> abs_decode::<T>(
                        old(self).abstract_bytes().subrange(
                            (start + i) * layout::size_of::<T>(),
                            (start + i + 1) * layout::size_of::<T>(),
                        ),
                        &val[i].value(),
                    )
                },
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).abstract_bytes() == old(self).abstract_bytes(),
            final(self).mem_contents_seq() == old(self).mem_contents_seq().update_subrange_with(
                start,
                val,
            ),
    ;
}

impl PointsTo<[u8]> {
    /// A `PointsTo<[u8]>` can be cast to an initialized `PointsTo<T>` when the abstract bytes can be
    /// decoded into the given `tracked typed_value` and the pointer for this permission is of the expected length.
    /// The resulting permission will take on the value in memory given by `typed_value`.
    ///
    /// The abstract bytes remain the same. This preserves the typed contents in memory on a roundtrip cast (see `PointsTo<T>::cast_to_untyped`).
    /// Note that this means provenance is not lost, which matches Rust's semantics for casting/transmuting in-memory values.
    ///
    /// The inclusion of `tracked typed_value` prohibits creating permission-carrying types out of thin air, in the case where `T` is a type that stores/represents a permission (e.g., shared references).
    pub proof fn cast_to_typed<T>(tracked self, tracked typed_value: T) -> (tracked dst: PointsTo<
        T,
    >)
        requires
            abs_decode::<T>(self.abstract_bytes(), &typed_value),
            layout::size_of::<T>() == self.ptr()@.metadata,
            self.ptr()@.addr as int % layout::align_of::<T>() as int == 0,
        ensures
            self.abstract_bytes() == dst.abstract_bytes(),
            dst.is_init(),
            dst.value() == typed_value,
            self.ptr() as *mut T == dst.ptr(),
    {
        broadcast use layout_of_sized, axiom_ptr_mut_from_data;

        let tracked mut perm = PointsTo::<T>::from_untyped(self.inner);
        perm.put(typed_value);
        perm
    }

    /// A `PointsTo<[u8]>` can always be cast to a logically uninitialized `PointsTo<T>`.
    /// The `mem_contents_seq()` on the resulting permission is uninitialized, meaning that the permission cannot
    /// be used to read `T` values from this memory.
    ///
    /// The abstract bytes remain the same.
    /// Note that this means provenance is not lost, which matches Rust's semantics for transmuting in-memory values.
    pub proof fn cast_to_typed_uninit<T>(tracked self) -> (tracked dst: PointsTo<T>)
        requires
            layout::size_of::<T>() == self.ptr()@.metadata,
            self.ptr()@.addr as int % layout::align_of::<T>() as int == 0,
        ensures
            self.abstract_bytes() == dst.abstract_bytes(),
            dst.mem_contents().is_uninit(),
            self.ptr() as *mut T == dst.ptr(),
    {
        broadcast use layout_of_sized, axiom_ptr_mut_from_data;

        PointsTo::<T>::from_untyped(self.inner)
    }

    /// Casts an initialized `&PointsTo<[u8]>` to an initialized `&PointsTo<str>`,
    /// where the resulting permission will take on the given `target` value in memory.
    /// Requires that it is possible to transmute between the pointed-to value of `self` and the provided value `target`.
    pub proof fn cast_to_str_shared<'a>(
        tracked &'a self,
        value: &[u8],
        tracked target: &str,
    ) -> (tracked ret: &'a PointsTo<str>)
        requires
            transmute_pre_points_to::<[u8], str>(value, target),
            self.is_init(),
            //require a separate argument for value since transmute_pre_points_to expects a &[u8] instead of a Seq<u8>
            self.value() == value@,
        ensures
            ret.is_init(),
            ret.value() == target,
            ret.ptr() == self.ptr() as *mut str,
    {
        broadcast use group_vstd_default, group_transmute_axioms, layout_of_slices, layout_of_str;

        use_type_invariant(self);

        self.abstract_bytes_decode();
        assert(value@.len() == self.abstract_bytes().len());
        assert forall|i: int| 0 <= i < self.mem_contents_seq().len() implies #[trigger] u8::decode(
            seq![self.abstract_bytes()[i]],
            value[i],
        ) by {
            assert(self.abstract_bytes().subrange(i * size_of::<u8>(), (i + 1) * size_of::<u8>())
                == seq![self.abstract_bytes()[i]]);
        }
        assert(EncodingU8Slice::decode(self.abstract_bytes(), value));
        assert(abs_decode::<[u8]>(self.abstract_bytes(), value));
        self.cast_to_str_shared_inner(value, target)
    }

    /// An initialized `&PointsTo<[u8]>` can always be cast to an initialized `&PointsTo<str>` provided that the resulting
    /// `str` value in memory can be decoded from the original permission's abstract bytes.
    /// The abstract bytes remain unchanged in the resulting permission.
    axiom fn cast_to_str_shared_inner<'a>(
        tracked &'a self,
        value: &[u8],
        tracked target: &str,
    ) -> (tracked ret: &'a PointsTo<str>)
        requires
            abs_decode::<str>(self.abstract_bytes(), target),
            self.is_init(),
            self.value() == value@,
            self.ptr()@.addr as int % layout::spec_align_of_val(value) as int == 0,
        ensures
            ret.is_init(),
            ret.value() == target,
            ret.ptr() == self.ptr() as *mut str,
            ret.abstract_bytes() == self.abstract_bytes(),
    ;
}

// PointsToUnaligned<[T]>: the unaligned slice permission that PointsTo<[T]> delegates to.
impl<T> PointsToUnaligned<[T]> {
    /// The sequence of (possibly uninitialized) memory that this permission gives access to.
    pub uninterp spec fn mem_contents_seq(&self) -> Seq<MemContents<T>>;

    /// Returns `true` if all of the permission's associated memory is initialized.
    #[verifier::inline]
    pub open spec fn is_init(&self) -> bool {
        self.is_init_subrange(0, self.mem_contents_seq().len() as int)
    }

    /// Returns `true` if all of the permission's associated memory in the given subrange is initialized.
    #[verifier::inline]
    pub open spec fn is_init_subrange(&self, start_index: int, len: int) -> bool
        recommends
            0 <= start_index <= start_index + len <= self.mem_contents_seq().len(),
    {
        forall|i|
            start_index <= i < start_index + len ==> self.mem_contents_seq().index(i).is_init()
    }

    /// Returns `true` if any part of the permission's associated memory is uninitialized.
    #[verifier::inline]
    pub open spec fn is_uninit(&self) -> bool {
        !self.is_init()
    }

    /// Returns `true` if all of the permission's associated memory is uninitialized.
    #[verifier::inline]
    pub open spec fn is_fully_uninit(&self) -> bool {
        forall|i|
            0 <= i < self.mem_contents_seq().len() ==> self.mem_contents_seq().index(i).is_uninit()
    }

    /// Returns a sequence where for each index in the given range,
    /// if the permission's associated memory at that index is initialized,
    /// the corresponding index in the sequence holds that value.
    /// Otherwise, the value at that index is meaningless.
    #[verifier::inline]
    pub open spec fn value_subrange(&self, start_index: int, len: nat) -> Seq<T>
        recommends
            0 <= start_index <= start_index + len <= self.mem_contents_seq().len(),
            self.is_init_subrange(start_index, len as int),
    {
        Seq::new(len, |i| self.mem_contents_seq().index(start_index + i).value())
    }

    /// Returns a sequence where for each index,
    /// if the permission's associated memory at that index is initialized,
    /// the corresponding index in the sequence holds that value.
    /// Otherwise, the value at that index is meaningless.
    #[verifier::inline]
    pub open spec fn value(&self) -> Seq<T>
        recommends
            self.is_init(),
    {
        self.value_subrange(0, self.mem_contents_seq().len())
    }

    /// Guarantee that the `PointsToUnaligned` points to a non-null address.
    ///
    /// Note that the size of a slice is given by the length * `size_of::<\T\>()`.
    /// <https://doc.rust-lang.org/reference/type-layout.html#slice-layout>
    pub axiom fn is_nonnull(tracked &self)
        ensures
            self.ptr()@.addr != 0,
    ;

    /// The memory associated with a pointer should always be within bounds of its spatial provenance.
    pub axiom fn ptr_bounds(tracked &self)
        requires
            self.ptr()@.provenance.is_some(),
        ensures
            self.ptr()@.provenance.data().start_addr() <= self.ptr()@.addr,
            self.ptr()@.addr + self.mem_contents_seq().len() * size_of::<T>()
                <= self.ptr()@.provenance.data().start_addr()
                + self.ptr()@.provenance.data().alloc_len(),
    ;

    /// If the memory covered by this permission is not zero-sized,
    /// then the pointer's provenance is non-null.
    pub axiom fn provenance_non_null(tracked &self)
        requires
            layout::size_of::<T>() * self.mem_contents_seq().len() != 0,
        ensures
            self.ptr()@.provenance != Provenance::None,
    ;

    /// Guarantees that the memory ranges associated with two distinct, non-ZST permissions will not overlap,
    /// since you cannot have two permissions to the same memory.
    /// (`self` is an &mut reference to enforce distinctness,
    /// so you cannot pass the same PointsTo as both arguments.)
    /// Since both S and T are non-zero-sized, this implies the pointers have distinct addresses.
    ///
    /// Note: If either S or T is zero-sized, we get disjointness "for free" without having to call this axiom,
    /// since the empty memory range corresponding to a ZST cannot possibly intersect with any other memory.
    /// However, note that if one type is a ZST and the other is a non-ZST,
    /// the disjointness definition as stated here here does not hold,
    /// since the ZST pointer could be in the middle of the non-ZST's range.
    pub axiom fn is_disjoint<S>(tracked &mut self, tracked other: &PointsToUnaligned<[S]>)
        requires
            size_of::<T>() * old(self).mem_contents_seq().len() != 0,
            size_of::<S>() * other.mem_contents_seq().len() != 0,
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + size_of::<T>() * final(self).mem_contents_seq().len()
                <= other.ptr() as int || other.ptr() as int + size_of::<S>()
                * other.mem_contents_seq().len() <= final(self).ptr() as int,
    ;

    /// Convert `PointsToUnaligned<[\T\]>` to an aligned `PointsTo<[\T\]>`.
    /// Requires the pointer address to be properly aligned.
    pub proof fn into_aligned(tracked self) -> (tracked perm: PointsTo<[T]>)
        requires
            self.ptr()@.addr as int % align_of::<T>() as int == 0,
        ensures
            perm.ptr() == self.ptr(),
            perm.mem_contents_seq() == self.mem_contents_seq(),
            perm.abstract_bytes() == self.abstract_bytes(),
    {
        broadcast use layout_of_sized;
        broadcast use layout_of_slices;

        let ghost v: &[T] = arbitrary();
        assert(spec_align_of_val::<[T]>(v) == align_of::<T>());
        assert(self.ptr()@.addr as int % spec_align_of_val::<[T]>(v) as int == 0);
        PointsTo { inner: self }
    }

    /// Borrow an unaligned `PointsToUnaligned<[\T\]>` as an aligned `PointsTo<[\T\]>`.
    /// Requires the pointer address to be properly aligned.
    ///
    /// Note: Currently an axiom since we don't have support for coercing equivalent references.
    pub axiom fn as_aligned(tracked &self) -> (tracked perm: &PointsTo<[T]>)
        requires
            self.ptr()@.addr as int % align_of::<T>() as int == 0,
        ensures
            perm.ptr() == self.ptr(),
            perm.mem_contents_seq() == self.mem_contents_seq(),
            perm.abstract_bytes() == self.abstract_bytes(),
    ;

    /// Mutably borrow an unaligned `PointsToUnaligned<[\T\]>` as an aligned `PointsTo<[\T\]>`.
    /// Requires the pointer address to be properly aligned.
    ///
    /// Note: Currently an axiom since we don't have support for coercing equivalent references.
    pub axiom fn as_aligned_mut(tracked &mut self) -> (tracked perm: &mut PointsTo<[T]>)
        requires
            old(self).ptr()@.addr as int % align_of::<T>() as int == 0,
        ensures
            perm.ptr() == old(self).ptr(),
            perm.mem_contents_seq() == old(self).mem_contents_seq(),
            perm.abstract_bytes() == old(self).abstract_bytes(),
            final(perm).ptr() == final(self).ptr(),
            final(perm).mem_contents_seq() == final(self).mem_contents_seq(),
            final(perm).abstract_bytes() == final(self).abstract_bytes(),
    ;

    // TODO - verify using as_untyped, as_typed axioms by reasoning about the encoding of integer types
    /// Like [`PointsTo<[T]>::cast_points_to_unaligned`], but on the unaligned version directly.
    ///
    /// We can cast a `[T]` permission to an unaligned `V` permission under the following conditions:
    ///
    /// (1) `T` and `V` are integer types where `V` is a power of 2
    /// and the bit encoding of a `V` can be viewed as
    /// the bit encoding for multiple `T`s
    /// (as defined precisely in the trait `CompatibleSmallerBaseFor<V>`).
    ///
    /// (2) Memory is initialized.
    ///
    /// (3) `self.value().len() * size_of::<T>() == size_of::<V>()`.
    ///
    /// Note: no alignment precondition.
    pub axiom fn cast_points_to_unaligned<V>(tracked &self) -> (tracked points_to:
        &PointsToUnaligned<V>) where T: CompatibleSmallerBaseFor<V> + Integer, V: BasePow2 + Integer
        requires
            self.is_init(),
            self.value().len() * size_of::<T>() == size_of::<V>(),
        ensures
            points_to.ptr() == ptr_mut_from_data::<V>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (),
                },
            ),
            points_to.is_init(),
            points_to.value() as int == to_big_from_digits::<V, T>(self.value()).index(0),
            points_to.abstract_bytes() == self.abstract_bytes(),
    ;

    /// Given that the subrange is within bounds, it is always possible to get a permission to just that subrange.
    pub axiom fn subrange(tracked &self, start_index: nat, len: nat) -> (tracked sub_points_to:
        &Self)
        requires
            start_index + len <= self.mem_contents_seq().len(),
        ensures
            sub_points_to.ptr() == ptr_mut_from_data::<[T]>(
                PtrData {
                    addr: (self.ptr()@.addr + start_index * size_of::<T>()) as usize,
                    provenance: self.ptr()@.provenance,
                    metadata: len as usize,
                },
            ),
            sub_points_to.mem_contents_seq() == self.mem_contents_seq().subrange(
                start_index as int,
                start_index as int + len as int,
            ),
            sub_points_to.abstract_bytes() == self.abstract_bytes().subrange(
                start_index * layout::size_of::<T>() as int,
                (start_index + len) * layout::size_of::<T>() as int,
            ),
    ;

    // TODO - verify using as_untyped, as_typed axioms by reasoning about the encoding of integer types
    /// Provided that memory is initialized, the pointer's address is aligned to `V`,
    /// and `self.value().len() * size_of::<T>() == size_of::<V>()`,
    /// we can always cast a `[T]` permission to a `V` permission.
    pub axiom fn cast_points_to<V>(tracked &self) -> (tracked points_to: &PointsTo<V>) where
        T: CompatibleSmallerBaseFor<V> + Integer,
        V: BasePow2 + Integer,

        requires
            self.is_init(),
            self.ptr()@.addr as int % align_of::<V>() as int == 0,
            self.value().len() * size_of::<T>() == size_of::<V>(),
        ensures
            points_to.ptr() == ptr_mut_from_data::<V>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (),
                },
            ),
            points_to.is_init(),
            points_to.value() as int == to_big_from_digits::<V, T>(self.value()).index(0),
    ;

    /// We can always convert a `PointsToUnaligned<[T]>` into a `SeqPointsTo<T>` for the same pointer,
    /// whose elements are individual `PointsToUnaligned<T>` with the memory contents of the corresponding index.
    pub axiom fn into_seq_pt(tracked self) -> (tracked s: SeqPointsTo<T>)
        requires
            self.ptr()@.addr as int % align_of::<T>() as int == 0,
        ensures
            forall|i|
                #![trigger s[i].mem_contents()]
                #![trigger self.mem_contents_seq()[i as int]]
                #![trigger s[i].ptr()@.provenance]
                #![trigger s[i].ptr()@.addr]
                0 <= i < self.mem_contents_seq().len() ==> {
                    &&& s[i].mem_contents() == self.mem_contents_seq()[i as int]
                    &&& s[i].ptr()@.provenance == s.ptr()@.provenance
                    &&& s[i].ptr()@.addr == s.ptr()@.addr + i * layout::size_of::<T>()
                },
            s.ptr() == self.ptr() as *mut T,
            s.len() == self.mem_contents_seq().len(),
            s.abstract_bytes() == self.abstract_bytes(),
            s.wf(),
    ;

    /// Same as `into_seq_pt`, but for `&PointsToUnaligned<[T]>`.
    pub axiom fn into_seq_pt_shared(tracked &self) -> (tracked s: &SeqPointsTo<T>)
        requires
            self.ptr()@.addr as int % align_of::<T>() as int == 0,
        ensures
            forall|i|
                #![trigger s[i].mem_contents()]
                #![trigger self.mem_contents_seq()[i as int]]
                #![trigger s[i].ptr()@.provenance]
                #![trigger s[i].ptr()@.addr]
                0 <= i < self.mem_contents_seq().len() ==> {
                    &&& s[i].mem_contents() == self.mem_contents_seq()[i as int]
                    &&& s[i].ptr()@.provenance == s.ptr()@.provenance
                    &&& s[i].ptr()@.addr == s.ptr()@.addr + i * layout::size_of::<T>()
                },
            s.ptr() == self.ptr() as *mut T,
            s.len() == self.mem_contents_seq().len(),
            s.abstract_bytes() == self.abstract_bytes(),
            s.wf(),
    ;
}

impl PointsTo<str> {
    /// The (possibly uninitialized) memory that this permission gives access to.
    pub uninterp spec fn mem_contents(&self) -> MemContents<&str>;

    /// Returns `true` if the permission's associated memory is initialized.
    #[verifier::inline]
    pub open spec fn is_init(&self) -> bool {
        self.mem_contents().is_init()
    }

    /// Returns `true` if the permission's associated memory is uninitialized.
    #[verifier::inline]
    pub open spec fn is_uninit(&self) -> bool {
        self.mem_contents().is_uninit()
    }

    /// If the permission's associated memory is initialized,
    /// returns the value that the pointer points to.
    /// Otherwise, the result is meaningless.
    #[verifier::inline]
    pub open spec fn value(&self) -> &str
        recommends
            self.is_init(),
    {
        self.mem_contents().value()
    }

    /// Guarantee that the `PointsTo` points to a non-null address.
    pub axiom fn is_nonnull(tracked &self)
        ensures
            self.ptr()@.addr != 0,
    ;

    // https://doc.rust-lang.org/reference/behavior-considered-undefined.html#r-undefined.validity.reference-box
    // https://doc.rust-lang.org/std/ptr/index.html#alignment
    /// Guarantee that the `PointsTo` points to an aligned address.
    ///
    // Note that even for ZSTs, pointers need to be aligned.
    pub axiom fn is_aligned(tracked &self)
        ensures
            self.ptr()@.addr as int % spec_align_of_val::<str>(self.value()) as int == 0,
    ;

    /// Invariant: The corresponding abstract bytes must decode into the value in memory.
    pub axiom fn abstract_bytes_decode(&self)
        ensures
            self.is_init() ==> abs_decode::<str>(self.abstract_bytes(), self.value()),
            !self.is_init() ==> self.abstract_bytes().len() == size_of::<u8>() * spec_size_of_val::<
                str,
            >(self.value()),
    ;

    /// Casts an initialized `&PointsTo<str>` to an initialized `&PointsTo<[u8]>`,
    /// where the resulting permission will take on the given `target` value in memory.
    /// Requires that it is possible to transmute between the pointed-to value of `self` and the provided value `target`.
    pub proof fn cast_to_u8_shared<'a>(tracked &'a self, tracked target: &[u8]) -> (tracked ret:
        &'a PointsTo<[u8]>)
        requires
            transmute_pre_points_to::<str, [u8]>(self.value(), target),
            self.is_init(),
        ensures
            ret.is_init(),
            ret.value() == target@,
            ret.ptr() == self.ptr() as *mut [u8],
    {
        broadcast use group_transmute_axioms, layout_of_slices, layout_of_str;

        use_type_invariant(self);

        self.abstract_bytes_decode();
        self.cast_to_u8_shared_inner(target)
    }

    /// An initialized `&PointsTo<str>` can always be cast to an initialized `&PointsTo<[u8]>` provided that the resulting
    /// `[u8]` value in memory can be decoded from the original permission's abstract bytes.
    /// The abstract bytes remain unchanged in the resulting permission.
    axiom fn cast_to_u8_shared_inner<'a>(tracked &'a self, tracked target: &[u8]) -> (tracked ret:
        &'a PointsTo<[u8]>)
        requires
            abs_decode::<[u8]>(self.abstract_bytes(), target),
            self.is_init(),
            self.ptr()@.addr as int % layout::spec_align_of_val::<[u8]>(target) as int == 0,
        ensures
            ret.is_init(),
            ret.value() == target@,
            ret.ptr() == self.ptr() as *mut [u8],
            ret.abstract_bytes() == self.abstract_bytes(),
    ;

    /// Creates a reference to a `PointsToUnaligned<[u8]>` from a reference to a `PointsTo<str>` with the same provenance
    /// and a range corresponding to the address of the `PointsTo<str>`, size of the `str`, and length.
    pub axiom fn as_untyped(tracked &self) -> (tracked raw: &PointsToUnaligned<[u8]>)
        ensures
            self.ptr() == raw.ptr() as *mut str,  // since *mut str is the same as *mut [u8], this condition captures addr, provenance, and metadata
            self.abstract_bytes() == raw.abstract_bytes(),
            raw.is_uninit(),
    ;
}

/// We can convert this permission into a `PointsTo<[T]>` with the same pointer
/// and the same memory contents at every index.
pub axiom fn seq_into_slice<T>(tracked spt: SeqPointsTo<T>) -> (tracked pt: PointsTo<[T]>)
    requires
        spt.wf(),
    ensures
        forall|i|
            0 <= i < pt.mem_contents_seq().len() ==> #[trigger] pt.mem_contents_seq()[i as int]
                == spt[i].mem_contents(),
        spt.abstract_bytes() == pt.abstract_bytes(),
        pt.ptr() as *mut T == spt.ptr(),
        pt.ptr()@.metadata == spt.len(),
;

/// We can create a reference to a `PointsTo<[T]>` from a reference to a `SeqPointsTo<T>`,
/// with the same pointer and the same memory contents at every index.
pub axiom fn seq_into_slice_shared<T>(tracked spt: &SeqPointsTo<T>) -> (tracked pt: &PointsTo<[T]>)
    requires
        spt.wf(),
    ensures
        forall|i|
            0 <= i < pt.mem_contents_seq().len() ==> #[trigger] pt.mem_contents_seq()[i as int]
                == spt[i].mem_contents(),
        spt.abstract_bytes() == pt.abstract_bytes(),
        pt.ptr() as *mut T == spt.ptr(),
        pt.ptr()@.metadata == spt.len(),
;

/// If the domain exactly contains the indices bounded by `self.len()`,
/// we can convert a mutable reference to this permission into a `&mut PointsTo<[T]>`
/// with the same pointer and the same memory contents at every index.
/// While the pointer and length will stay the same, any changes to the memory contents
/// will be reflected in the original `SeqPointsTo<T>` permission.
pub axiom fn seq_into_slice_mut<T>(tracked spt: &mut SeqPointsTo<T>) -> (tracked pt: &mut PointsTo<
    [T],
>)
    requires
        spt.wf(),
    ensures
        pt.ptr() as *mut T == old(spt).ptr(),
        pt.ptr()@.metadata == old(spt).len(),
        pt.abstract_bytes() == old(spt).abstract_bytes(),
        forall|i|
            0 <= i < pt.mem_contents_seq().len() ==> #[trigger] pt.mem_contents_seq()[i as int]
                == old(spt)[i].mem_contents(),
        // Gurantees on final(spt) are conditional on the final(pt) having the same pointer and length
        final(pt).ptr() == pt.ptr() && final(pt).len() == pt.len() ==> ({
            &&& final(spt).wf()
            &&& (forall|i|
                0 <= i < pt.mem_contents_seq().len()
                    ==> #[trigger] final(pt).mem_contents_seq()[i as int]
                    == final(spt)[i].mem_contents())
            &&& final(spt).abstract_bytes() == final(pt).abstract_bytes()
            &&& old(spt).ptr() == final(spt).ptr()
            &&& old(spt).len() == final(spt).len()
            &&& (forall|i|
                0 <= i < final(spt).len() ==> #[trigger] final(spt)[i].ptr() == old(spt)[i].ptr())
        }),
;