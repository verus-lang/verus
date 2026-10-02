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
}

impl PointsTo<[u8]> {
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
