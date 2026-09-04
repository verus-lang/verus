/// Data associated with a `PointsTo` permission.
/// We keep track of both the pointer, the (potentially uninitialized) value
/// it points to, and the abstract bytes in memory corresponding to Rust's abstract machine.
///
/// If `mem_contents` is `Init(T)`, this signifies that `ptr` points to initialized memory,
/// and the value of `mem_contents` is consistent with the bytes `ptr` points to,
/// We also have all the ghost state associated with type `T`.
///
/// If `mem_contents` is `Uninit`, then we have no knowledge about what's in memory,
/// and we assume `ptr` points to uninitialized memory.
/// (To be pedantic, the bytes might be initialized in Rust's abstract machine,
///  but we don't know, so we have to pretend they're uninitialized.)
#[cfg(verus_keep_ghost)]
pub ghost struct PointsToData<T> {
    pub ptr: *mut T,
    pub mem_contents: MemContents<T>,
    pub abstract_bytes: Seq<AbstractByte>,
}

#[cfg(verus_keep_ghost)]
impl<T> View for PointsTo<T> {
    type V = PointsToData<T>;

    open spec fn view(&self) -> Self::V {
        PointsToData {
            ptr: self.ptr(),
            mem_contents: self.mem_contents(),
            abstract_bytes: self.abstract_bytes(),
        }
    }
}

impl<T: ?Sized> PointsTo<T> {
    /// Guarantee that the `PointsTo` points to an aligned address.
    /// See: <https://doc.rust-lang.org/reference/behavior-considered-undefined.html#r-undefined.validity.reference-box>
    /// See: <https://doc.rust-lang.org/std/ptr/index.html#alignment>
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        let v: &T = arbitrary();
        self.inner.ptr()@.addr as int % spec_align_of_val::<T>(v) as int == 0
    }
}

#[cfg(verus_keep_ghost)]
impl<T> View for PointsToUnaligned<T> {
    type V = PointsToData<T>;

    open spec fn view(&self) -> Self::V {
        PointsToData {
            ptr: self.ptr(),
            mem_contents: self.mem_contents(),
            abstract_bytes: self.abstract_bytes(),
        }
    }
}

impl<T> PointsTo<T> {
    /// Convert an aligned `PointsTo` to an unaligned `PointsToUnaligned`.
    /// This is always safe since aligned is stricter than unaligned.
    ///
    /// Ensures pointer locations remain the same, and memory
    /// initializations states remain the same.
    pub proof fn into_unaligned(tracked self) -> (tracked perm: PointsToUnaligned<T>)
        ensures
            perm.ptr() == self.ptr(),
            perm.mem_contents() == self.mem_contents(),
    {
        self.inner
    }

    /// Borrow an aligned `PointsTo` as an unaligned `PointsToUnaligned`.
    /// This is always safe since aligned is stricter than unaligned.
    ///
    /// Ensures pointer locations remain the same, and memory
    /// initializations states remain the same.
    pub proof fn as_unaligned(tracked &self) -> (tracked perm: &PointsToUnaligned<T>)
        ensures
            perm.ptr() == self.ptr(),
            perm.mem_contents() == self.mem_contents(),
    {
        &self.inner
    }

    /// If the memory is initialized, then the bytes must decode into the given value in memory.
    /// If the memory is uninitialized, then the bytes can be anything.
    pub broadcast proof fn abstract_bytes_decode(&self)
        ensures
            self.is_init() ==> #[trigger] abs_decode::<T>(self.abstract_bytes(), &self.value()),
            self.is_uninit() ==> self.abstract_bytes().len() == size_of::<T>(),
    {
        self.inner.abstract_bytes_decode();
    }

    /// A `PointsTo<T>` can always be cast to a logically uninitialized `PointsTo<[u8]>`, an untyped view of this memory.
    /// The `mem_contents_seq()` on the resulting permission is fully uninitialized, meaning that the permission cannot be used to read `u8` values from this memory.
    ///
    /// The abstract bytes remain the same. This preserves the typed contents in memory on a roundtrip cast (see `PointsTo<[u8]>::cast_to_typed`).
    /// Note that this means provenance is not lost, which matches Rust's semantics for casting/transmuting in-memory values.
    ///
    /// This function also returns a `tracked Option<T>` corresponding to the `MemContents<T>` on `self`.
    /// This is intended to be used with `PointsTo<[u8]>::cast_to_typed` in order to maintain the typed contents of the memory on a roundtrip.
    /// The use of `tracked Option<T>` prohibits creating permission-carrying types out of thin air, i.e. in the case where `T` is a type that stores/represents a permission (e.g., shared references).
    pub proof fn cast_to_untyped(tracked self) -> (tracked (dst, typed_value): (
        PointsTo<[u8]>,
        Option<T>,
    ))
        ensures
            self.abstract_bytes() == dst.abstract_bytes(),
            dst.is_fully_uninit(),
            self.ptr()@.addr == dst.ptr()@.addr,
            self.ptr()@.provenance == dst.ptr()@.provenance,
            size_of::<T>() == dst.ptr()@.metadata,
            typed_value.is_some() <==> self.is_init(),
            typed_value.is_some() ==> typed_value.unwrap() == self.value(),
    {
        broadcast use layout_of_slices, align_of_u8, layout_of_primitives, group_raw_ptr_axioms;

        let tracked mut perm = self;
        let tracked typed_value: Option<T>;
        if self.is_init() {
            typed_value = Some(perm.take());
        } else {
            typed_value = None;
        }

        let tracked untyped = perm.into_untyped();
        let tracked u8_slice = PointsTo::<[u8]>::from_untyped(
            untyped,
            layout::size_of::<T>() as usize,
        );

        (u8_slice, typed_value)
    }

    /// Creates a `PointsTo<T>` from a `PointsToUnaligned<[u8]>` from with the same provenance
    /// and a ptr corresponding to the range of the `PointsToUnaligned<[u8]>`.
    /// The resulting `PointsTo<T>` will be uninitialized.
    pub axiom fn from_untyped(tracked raw: PointsToUnaligned<[u8]>) -> (tracked out: Self)
        requires
            raw.ptr()@.addr as int % layout::align_of::<T>() as int == 0,
            layout::size_of::<T>() == raw.ptr()@.metadata,
        ensures
            out.ptr() == raw.ptr() as *mut T,
            out.abstract_bytes() == raw.abstract_bytes(),
            out.is_uninit(),
    ;

    /// Creates a `PointsToUnaligned<[u8]>` from a `PointsTo<T>` with the same provenance
    /// and a range corresponding to the address of the `PointsTo<T>` and size of `T`.
    /// If there is any value stored in memory, it is dropped.
    pub axiom fn into_untyped(tracked self) -> (tracked raw: PointsToUnaligned<[u8]>)
        ensures
            self.ptr() == raw.ptr() as *mut T,
            layout::size_of::<T>() == raw.ptr()@.metadata,
            self.abstract_bytes() == raw.abstract_bytes(),
            raw.is_fully_uninit(),
    ;

    /// Creates a reference to a `PointsToUnaligned<[u8]>` from a reference to a `PointsTo<T>` with the same provenance
    /// and a range corresponding to the address of the `PointsTo<T>` and size of the `T`.
    pub axiom fn as_untyped(tracked &self) -> (tracked raw: &PointsToUnaligned<[u8]>)
        ensures
            self.ptr() == raw.ptr() as *mut T,
            layout::size_of::<T>() == raw.ptr()@.metadata,
            self.abstract_bytes() == raw.abstract_bytes(),
            raw.is_fully_uninit(),
    ;

    /// Creates a mutable reference to a `PointsToUnaligned<[u8]>` from a reference to a `PointsTo<T>` with the same provenance
    /// and a range corresponding to the address of the `PointsTo<T>` and size of the `T`.
    /// If this permission carries any MemContents, they are dropped here.
    /// (call `take` first if you want to save the MemContents)
    pub axiom fn as_untyped_mut(tracked &mut self) -> (tracked raw: &mut PointsToUnaligned<[u8]>)
        ensures
            old(self).ptr() == raw.ptr() as *mut T,
            layout::size_of::<T>() == raw.ptr()@.metadata,
            old(self).abstract_bytes() == raw.abstract_bytes(),
            raw.is_fully_uninit(),
            final(raw).ptr() == raw.ptr() ==> ({
                &&& final(self).ptr() == old(self).ptr()
                &&& final(self).abstract_bytes() == final(raw).abstract_bytes()
                &&& final(self).is_uninit()
            }),
    ;

    /// This takes a borrow of the `T` from `MemContents<T>` from `self`.
    pub axiom fn borrow(tracked &self) -> (tracked val: &T)
        requires
            self.is_init(),
        ensures
            val == self.value(),
    ;

    /// This takes a mutable borrow of the `T` from `MemContents<T>>` on `self`.
    pub axiom fn borrow_mut(tracked &mut self) -> (tracked r: &mut T)
        requires
            self.is_init(),
        ensures
            *r == old(self).value(),
            mut_ref_ptr(r) == old(self).ptr(),
            //
            final(self).is_init(),
            final(self).ptr() == old(self).ptr(),
            final(self).value() == *final(r),
    ;

    /// This moves the `MemContents<T>` out from `self`.
    pub axiom fn take(tracked &mut self) -> (tracked val: T)
        requires
            self.is_init(),
        ensures
            val == old(self).value(),
            final(self).ptr() == old(self).ptr(),
            final(self).abstract_bytes() == old(self).abstract_bytes(),
            final(self).is_uninit(),
    ;

    // Consumes the `T` and puts it in the `MemContents<T>` for `self`.
    pub axiom fn put(tracked &mut self, tracked val: T)
        requires
            abs_decode::<T>(self.abstract_bytes(), &val),
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).abstract_bytes() == old(self).abstract_bytes(),
            final(self).is_init(),
            final(self).value() == val,
    ;
}

impl<T> PointsToUnaligned<T> {
    /// Convert PointsToUnaligned to an aligned PointsTo.
    /// Requires the pointer address to be properly aligned.
    ///
    /// Ensures pointer locations remain the same, and memory
    /// initializations states remain the same.
    pub proof fn into_aligned(tracked self) -> (tracked perm: PointsTo<T>)
        requires
            self.ptr()@.addr as int % align_of::<T>() as int == 0,
        ensures
            perm.ptr() == self.ptr(),
            perm.mem_contents() == self.mem_contents(),
            perm.abstract_bytes() == self.abstract_bytes(),
    {
        broadcast use layout_of_sized;

        PointsTo { inner: self }
    }

    /// Borrow an unaligned PointsToUnaligned as an aligned PointsTo.
    /// Requires the pointer address to be properly aligned.
    ///
    /// Ensures pointer locations remain the same, and memory
    /// initializations states remain the same.
    ///
    /// Note: Currently an axiom since we don't have support for coercing equivalent references.
    pub axiom fn as_aligned(tracked &self) -> (tracked perm: &PointsTo<T>)
        requires
            self.ptr()@.addr as int % align_of::<T>() as int == 0,
        ensures
            perm.ptr() == self.ptr(),
            perm.mem_contents() == self.mem_contents(),
            perm.abstract_bytes() == self.abstract_bytes(),
    ;
}

/// The length of `mem_contents_seq()` should always match the pointer's metadata.
pub broadcast axiom fn axiom_pt_slice_len<T>(pt: PointsTo<[T]>)
    ensures
        #[trigger] pt.mem_contents_seq().len() == pt.ptr()@.metadata,
;

/// The length of `mem_contents_seq()` should always match the pointer's metadata.
pub broadcast axiom fn axiom_pt_slice_unaligned_len<T>(pt: PointsToUnaligned<[T]>)
    ensures
        #[trigger] pt.mem_contents_seq().len() == pt.ptr()@.metadata,
;

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

impl PointsToUnaligned<[u8]> {
    /// If `T` is zero sized, then we can construct an uninitialized `PointsToUnaligned<[T]>` from any non-null pointer.
    /// The range of memory pointed to by this permission will be empty.
    pub axiom fn zero_sized<T>(ptr: *mut T) -> (tracked perm: Self)
        requires
            ptr@.addr != 0,
            layout::size_of::<T>() == 0,
            ptr@.provenance.is_some() ==> {
                &&& ptr@.addr as int >= ptr@.provenance.data().start_addr()
                &&& ptr@.addr <= ptr@.provenance.data().start_addr()
                    + ptr@.provenance.data().alloc_len()
            },
        ensures
            perm.ptr()@.addr == ptr@.addr,
            perm.ptr()@.provenance == ptr@.provenance,
            perm.ptr()@.metadata == 0,
            perm.abstract_bytes().len() == layout::size_of::<T>(),
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

pub tracked struct SeqPointsTo<T> {
    perm: Seq<PointsTo<T>>,
    ptr: Ghost<*mut T>,
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

impl<T> SeqPointsTo<T> {
    /// The keys must fall in the range `[0, self.len())`.
    /// For each key `i`, the corresponding `PointsTo<T>` must have the same provenance as
    /// the `self.ptr()`, and its pointer's address is offset from `self.ptr()` by `i`.
    // #[verifier::type_invariant]
    // Cannot use type invariant since we need to return a mutable reference to `perm`.
    pub open spec fn wf(self) -> bool {
        &&& forall|i|
            #![trigger self[i].ptr()@.provenance]
            #![trigger self[i].ptr()@.addr]
            0 <= i < self.len() ==> {
                &&& self[i].ptr()@.provenance == self.ptr()@.provenance
                &&& self[i].ptr()@.addr == self.ptr()@.addr + i * layout::size_of::<T>()
            }
        &&& (self.len() != 0 && layout::size_of::<T>() != 0) ==> {
            &&& self.ptr()@.provenance.is_some()
        }
        &&& self.ptr()@.provenance.is_some() ==> {
            &&& self.ptr()@.provenance.data().start_addr() <= self.ptr()@.addr
            &&& self.ptr()@.addr + self.len() * layout::size_of::<T>()
                <= self.ptr()@.provenance.data().start_addr()
                + self.ptr()@.provenance.data().alloc_len()
        }
        &&& self.ptr()@.addr != 0
        &&& self.ptr()@.addr as nat % align_of::<T>() == 0
    }

    /// The pointer that this permission is associated with.
    pub closed spec fn ptr(self) -> *mut T {
        self.ptr@
    }

    /// The `Seq<PointsTo<T>>` that this type is a wrapper for.
    pub closed spec fn seq_perm(self) -> Seq<PointsTo<T>> {
        self.perm
    }

    pub open spec fn mem_contents(self) -> Seq<MemContents<T>> {
        self.seq_perm().map(|i: int, elt: PointsTo<T>| elt.mem_contents())
    }

    /// A "flattened" view of the abstract bytes.
    /// Because the abstract bytes do not change across casting/transmuting, it is often more
    /// convenient to have a single flattened view of the bytes that is the same as for `PointsTo<[T]>`.
    pub open spec fn abstract_bytes(self) -> Seq<AbstractByte> {
        Self::abstract_bytes_inner(self.seq_perm())
    }

    pub open spec fn abstract_bytes_inner(perms: Seq<PointsTo<T>>) -> Seq<AbstractByte> {
        perms.fold_left(
            Seq::empty(),
            |acc: Seq<AbstractByte>, elt: PointsTo<T>| acc + elt.abstract_bytes(),
        )
    }

    /// The length of the sequence of `PointsTo<T>`.
    #[verifier::inline]
    pub open spec fn len(self) -> nat {
        self.seq_perm().len()
    }

    /// `[]` operator, synonymous with `index`.
    #[verifier::inline]
    pub open spec fn spec_index(self, index: nat) -> PointsTo<T>
        recommends
            0 <= index < self.len(),
    {
        self.seq_perm()[index as int]
    }

    /// Returns `true` if all of the permission's associated memory is initialized.
    #[verifier::inline]
    pub open spec fn is_init(&self) -> bool {
        forall|i| 0 <= i < self.len() ==> #[trigger] self[i].is_init()
    }

    /// Returns `true` if any part of the permission's associated memory is uninitialized.
    #[verifier::inline]
    pub open spec fn is_uninit(&self) -> bool {
        !self.is_init()
    }

    /// Returns `true` if all of the permission's associated memory is uninitialized.
    #[verifier::inline]
    pub open spec fn is_fully_uninit(&self) -> bool {
        forall|i| 0 <= i < self.len() ==> #[trigger] self[i].is_uninit()
    }

    /// Given that all of the permission's associated memory is initialized,
    /// returns the underlying values as a sequence.
    #[verifier::inline]
    pub open spec fn value(&self) -> Seq<T>
        recommends
            self.is_init(),
    {
        Seq::new(self.len(), |i| self[i as nat].value())
    }

    /// Returns a `tracked` reference to the underlying `Seq<PointsTo<T>>`,
    /// given `tracked &self`.
    pub proof fn tracked_perm_seq(tracked &self) -> (tracked ret: &Seq<PointsTo<T>>)
        requires
            self.wf(),
        ensures
            ret == self.seq_perm(),
    {
        &self.perm
    }

    pub proof fn borrow_mut(tracked &mut self, i: int) -> (tracked ret: &mut PointsTo<T>)
        requires
            self.wf(),
            0 <= i < self.len(),
        ensures
            final(self).ptr() == old(self).ptr(),
            final(ret).ptr() == ret.ptr() ==> final(self).wf(),
            *ret == old(self).seq_perm()[i],
            final(self).seq_perm() == old(self).seq_perm().update(i, *final(ret)),
    {
        broadcast use group_seq_axioms;

        self.perm.tracked_borrow_mut(i)
    }

    /// Returns a `tracked` mutable reference to the underlying `Seq<PointsTo<T>>`,
    /// given `tracked &mut self`. `self.ptr` will remain unchanged.
    ///
    /// Provided that this mutable reference is not used to change the sequence length
    /// or any of the `PointsTo<T>` pointers, the invariant will be preserved.
    pub proof fn tracked_perm_seq_mut(tracked &mut self) -> (tracked ret: &mut Seq<PointsTo<T>>)
        requires
            self.wf(),
        ensures
            *ret == old(self).seq_perm(),
            final(self).seq_perm() == *final(ret),
            old(self).ptr() == final(self).ptr(),
            // Criteria necessary for re-establishing invariants
            (old(self).len() == final(self).len() && forall|i|
                #![auto]
                0 <= i < final(self).len() ==> final(self)[i].ptr() == old(self)[i].ptr())
                ==> final(self).wf(),
    {
        &mut self.perm
    }

    /// Sanity check for the criteria for ensuring that the final value of `&mut self` is still well-formed:
    ///
    /// * All pointers remain the same.
    /// * The length remains the same.
    ///
    /// Note that we _are_ allowed to change `self.mem_contents()` without affecting the invariant's validity.
    pub broadcast proof fn constants(&mut self)
        requires
            old(self).wf(),
            forall|i|
                #![trigger old(self)[i].ptr()]
                #![trigger final(self)[i].ptr()]
                0 <= i < final(self).len() ==> old(self)[i].ptr() == final(self)[i].ptr(),
            old(self).len() == final(self).len(),
            old(self).ptr() == final(self).ptr(),
        ensures
            #[trigger] final(self).wf(),
    {
    }

    /// Proof of equivalence for two different ways to get the `MemContents<T>` at a given index `i`.
    pub broadcast proof fn mem_contents_equiv(self, i: int)
        requires
            0 <= i < self.len(),
        ensures
            #![trigger self.mem_contents()[i]]
            #![trigger self.seq_perm()[i]]
            self.mem_contents()[i] == self.seq_perm()[i].mem_contents(),
    {
        broadcast use group_vstd_default;

    }

    /// Given an aligned and non-null pointer,
    /// it is always possible to construct a `SeqPointsTo` with an empty sequence of permissions.
    pub proof fn empty(ptr: *mut T) -> (tracked spt: SeqPointsTo<T>)
        requires
            ptr@.addr != 0,
            ptr@.addr as nat % align_of::<T>() == 0,
            ptr@.provenance.is_some() ==> {
                &&& ptr@.addr as int >= ptr@.provenance.data().start_addr()
                &&& ptr@.addr <= ptr@.provenance.data().start_addr()
                    + ptr@.provenance.data().alloc_len()
            },
        ensures
            spt.seq_perm() == Seq::<PointsTo<T>>::empty(),
            spt.ptr() == ptr,
            spt.len() == 0,
            spt.wf(),
    {
        broadcast use group_vstd_default;

        SeqPointsTo { perm: Seq::tracked_empty(), ptr: Ghost(ptr) }
    }

    /// If the memory covered by this permission is not zero-sized,
    /// then the pointer's provenance is non-null.
    pub proof fn provenance_non_null(tracked &self)
        requires
            layout::size_of::<T>() * self.len() != 0,
            self.wf(),
        ensures
            self.ptr()@.provenance != Provenance::None,
    {
        assert(layout::size_of::<T>() != 0);
        assert(self.len() != 0);
        self.perm.tracked_borrow(0).provenance_non_null();
    }

    /// We can construct a `SeqPointsTo` with `length`-many `PointsTo` permissions,
    /// provided that `T` is zero-sized and that the pointer is non-null and aligned.
    pub proof fn zero_sized(ptr: *mut T, length: nat) -> (tracked spt: Self)
        requires
            ptr@.addr != 0,
            ptr@.addr as nat % align_of::<T>() == 0,
            ptr@.provenance.is_some() ==> {
                &&& ptr@.addr as int >= ptr@.provenance.data().start_addr()
                &&& ptr@.addr <= ptr@.provenance.data().start_addr()
                    + ptr@.provenance.data().alloc_len()
            },
            layout::size_of::<T>() == 0,
        ensures
            forall|i| #![auto] 0 <= i < spt.len() ==> spt[i].is_uninit(),
            spt.ptr() == ptr,
            spt.len() == length,
            spt.wf(),
    {
        SeqPointsTo::empty(ptr).zero_sized_helper(length, length)
    }

    proof fn zero_sized_helper(tracked self, remaining: nat, total: nat) -> (tracked spt: Self)
        requires
            self.ptr()@.addr != 0,
            self.ptr()@.addr as nat % align_of::<T>() == 0,
            layout::size_of::<T>() == 0,
            self.len() + remaining == total,
            forall|i| #![auto] 0 <= i < self.len() ==> self[i].is_uninit(),
            self.wf(),
            self.ptr()@.provenance.is_some() ==> {
                &&& self.ptr()@.addr as int >= self.ptr()@.provenance.data().start_addr()
                &&& self.ptr()@.addr <= self.ptr()@.provenance.data().start_addr()
                    + self.ptr()@.provenance.data().alloc_len()
            },
        ensures
            spt.ptr() == self.ptr(),
            spt.len() == total,
            forall|i| #![auto] 0 <= i < spt.len() ==> spt[i].is_uninit(),
            spt.wf(),
        decreases remaining,
    {
        broadcast use group_vstd_default;

        if remaining == 0 {
            self
        } else {
            // use_type_invariant(&self);
            let tracked zs_pt = PointsTo::zero_sized(self.ptr());
            let tracked mut mut_spt = self;
            mut_spt.perm.tracked_push(zs_pt);
            Self::abstract_bytes_len_helper(mut_spt.seq_perm());

            mut_spt.zero_sized_helper((remaining - 1) as nat, total)
        }
    }

    proof fn abstract_bytes_len_helper(perms: Seq<PointsTo<T>>)
        ensures
            Self::abstract_bytes_inner(perms).len() == perms.len() * layout::size_of::<T>(),
        decreases perms.len(),
    {
        broadcast use
            crate::vstd::seq::group_seq_axioms,
            crate::vstd::type_representation::encode_decode_len,
        ;

        if perms.len() > 0 {
            Self::abstract_bytes_len_helper(perms.drop_last());
            perms.last().abstract_bytes_decode();
            assert((perms.len() - 1) * layout::size_of::<T>() + layout::size_of::<T>()
                == perms.len() * layout::size_of::<T>()) by (nonlinear_arith);
        }
    }

    /// The length of the abstract bytes matches the size of this type multiplied by the number of elements this permission represents.
    pub broadcast proof fn abstract_bytes_len(&self)
        ensures
            #[trigger] self.abstract_bytes().len() == self.len() * layout::size_of::<T>(),
    {
        Self::abstract_bytes_len_helper(self.seq_perm());
    }

    // Relates the abstract bytes for a sequence of permissions to subranges of those permissions and subranges of the abstract bytes.
    // Useful for avoiding reasoning about fold_left directly.
    proof fn abstract_bytes_subrange(perms: Seq<PointsTo<T>>, split: int)
        requires
            0 <= split <= perms.len(),
        ensures
    // abstract bytes can be split by subranges of the permissions themselves

            Self::abstract_bytes_inner(perms) == Self::abstract_bytes_inner(
                perms.subrange(0, split),
            ) + Self::abstract_bytes_inner(perms.subrange(split, perms.len() as int)),
            // abstract bytes of a prefix of permssions correspond to a prefix of the entire abstract bytes
            Self::abstract_bytes_inner(perms.subrange(0, split)) == Self::abstract_bytes_inner(
                perms,
            ).subrange(0, split * layout::size_of::<T>()),
            // abstract bytes of a suffix of permissions correspond to suffix of the entire abstract bytes
            Self::abstract_bytes_inner(perms.subrange(split, perms.len() as int))
                == Self::abstract_bytes_inner(perms).subrange(
                split * layout::size_of::<T>(),
                perms.len() as int * layout::size_of::<T>(),
            ),
            // the abstract bytes of a prefix of permissions has the expected length
            Self::abstract_bytes_inner(perms.subrange(0, split)).len() == split * layout::size_of::<
                T,
            >(),
            // the abstract bytes of a suffix of permissions has the expected length
            Self::abstract_bytes_inner(perms.subrange(split, perms.len() as int)).len() == (
            perms.len() - split) * layout::size_of::<T>(),
        decreases perms.len() - split,
    {
        broadcast use group_vstd_default, crate::vstd::arithmetic::mul::group_mul_basics;

        if perms.len() > split {
            Self::abstract_bytes_subrange(perms.subrange(0, perms.len() - 1), split);
            perms.lemma_slice_of_slice(0, perms.len() - 1, 0, split);
            perms.lemma_slice_of_slice(0, perms.len() - 1, split, perms.len() - 1);
            assert(Self::abstract_bytes_inner(perms.subrange(0, perms.len() - 1))
                == Self::abstract_bytes_inner(perms.subrange(0, split))
                + Self::abstract_bytes_inner(perms.subrange(split, perms.len() - 1)));

            assert(perms.last() == perms[perms.len() - 1]);
            assert(perms.drop_last() == perms.subrange(0, perms.len() - 1));
            assert(Self::abstract_bytes_inner(perms) == Self::abstract_bytes_inner(
                perms.subrange(0, perms.len() - 1),
            ) + perms[perms.len() - 1].abstract_bytes());
            assert(perms.subrange(split, perms.len() as int).last() == perms[perms.len() - 1]);
            assert(perms.subrange(split, perms.len() as int).drop_last() == perms.subrange(
                split,
                perms.len() - 1,
            ));
            assert(Self::abstract_bytes_inner(perms.subrange(split, perms.len() as int))
                == Self::abstract_bytes_inner(perms.subrange(split, perms.len() - 1))
                + perms[perms.len() - 1].abstract_bytes());

            Self::abstract_bytes_len_helper(perms.subrange(0, split));
            Self::abstract_bytes_len_helper(perms.subrange(split, perms.len() as int));
            assert(perms.subrange(split, perms.len() as int).len() == perms.len() - split);
            assert(Self::abstract_bytes_inner(
                perms.subrange(0, perms.len() - 1).subrange(0, split),
            ).len() == Self::abstract_bytes_inner(perms.subrange(0, split)).len());
            assert(Self::abstract_bytes_inner(perms).len() - Self::abstract_bytes_inner(
                perms.subrange(0, split),
            ).len() == Self::abstract_bytes_inner(perms.subrange(split, perms.len() as int)).len());
            assert(perms.len() * layout::size_of::<T>() - split * layout::size_of::<T>() == (
            perms.len() - split) * layout::size_of::<T>()) by (nonlinear_arith);
        } else {
            Self::abstract_bytes_len_helper(perms);
        }
    }

    /// The abstract bytes of an individual permission in a sequence corresponds to a subrange of length `layout::size_of::<T>()`
    /// from the entire abstract bytes.
    pub broadcast proof fn abstract_bytes_equiv(&self, i: int)
        requires
            0 <= i < self.len(),
        ensures
            #[trigger] self.seq_perm()[i].abstract_bytes() == self.abstract_bytes().subrange(
                i * layout::size_of::<T>(),
                (i + 1) * layout::size_of::<T>(),
            ),
    {
        broadcast use group_vstd_default;

        Self::abstract_bytes_len_helper(self.seq_perm());

        Self::abstract_bytes_subrange(self.seq_perm(), i + 1);
        Self::abstract_bytes_subrange(self.seq_perm().subrange(0, i + 1), i);
        assert(self.seq_perm()[i] == self.seq_perm().subrange(0, i + 1).subrange(i, i + 1)[0]);
        self.abstract_bytes().lemma_slice_of_slice(
            0,
            (i + 1) * layout::size_of::<T>(),
            i * layout::size_of::<T>(),
            (i + 1) * layout::size_of::<T>(),
        );
    }

    proof fn abstract_bytes_decode_helper(&self, len: int)
        requires
            0 <= len <= self.len(),
            self.wf(),
        ensures
            forall|i: int|
                0 <= i < len ==> {
                    &&& (#[trigger] self.mem_contents()[i]).is_init() ==> abs_decode::<T>(
                        self.seq_perm()[i].abstract_bytes(),
                        &self.mem_contents()[i].value(),
                    )
                    &&& self.mem_contents()[i].is_uninit()
                        ==> self.seq_perm()[i].abstract_bytes().len() == size_of::<T>()
                },
        decreases len,
    {
        broadcast use group_vstd_default;

        if len > 0 {
            self.abstract_bytes_decode_helper(len - 1);
            self.perm[len - 1].abstract_bytes_decode();
            self.mem_contents_equiv(len - 1);
        }
    }

    /// For all positions in this sequence, the abstract bytes for that position can be decoded into the value in memory at that position.
    pub proof fn abstract_bytes_decode(&self)
        requires
            self.wf(),
        ensures
            forall|i: int|
                0 <= i < self.len() ==> {
                    &&& (#[trigger] self.mem_contents()[i]).is_init() ==> abs_decode::<T>(
                        self.abstract_bytes().subrange(
                            i * layout::size_of::<T>(),
                            (i + 1) * layout::size_of::<T>(),
                        ),
                        &self.mem_contents()[i].value(),
                    )
                    &&& self.mem_contents()[i].is_uninit()
                        ==> self.seq_perm()[i].abstract_bytes().len() == size_of::<T>()
                },
    {
        broadcast use SeqPointsTo::abstract_bytes_equiv;

        self.abstract_bytes_decode_helper(self.len() as int);
    }

    pub proof fn into_seq(tracked self) -> (tracked r: Seq<PointsTo<T>>)
        ensures
            r == self.seq_perm(),
    {
        self.perm
    }

    pub proof fn from_seq(tracked r: Seq<PointsTo<T>>, ptr: *mut T) -> (tracked s: Self)
        requires
            (forall|i|
                #![trigger r[i].ptr()@.provenance]
                #![trigger r[i].ptr()@.addr]
                0 <= i < r.len() ==> {
                    &&& r[i].ptr()@.provenance == ptr@.provenance
                    &&& r[i].ptr()@.addr == ptr@.addr + i * layout::size_of::<T>()
                }),
            r.len() != 0 && layout::size_of::<T>() != 0 ==> {
                &&& ptr@.provenance.is_some()
                &&& ptr@.provenance.data().start_addr() <= ptr@.addr
                &&& ptr@.addr + r.len() * layout::size_of::<T>()
                    <= ptr@.provenance.data().start_addr() + ptr@.provenance.data().alloc_len()
            },
            ptr@.addr as nat % align_of::<T>() == 0,
            ptr@.addr != 0,
        ensures
            r == s.seq_perm(),
            s.ptr() == ptr,
    {
        SeqPointsTo::<T> { perm: r, ptr: Ghost(ptr) }
    }

    /// Casting a `SeqPointsTo<T>` to a `SeqPointsTo<u8>` casts the pointer,
    /// multiplies the length by `size_of::<T>()`, and preserves the abstract bytes.
    /// The resulting `SeqPointsTo<u8>` is logically uninitialized, so it cannot be read from.
    /// The `tracked typed_value` represents the typed contents from this memory,
    /// which can be later used to cast the `dst` permission back to a typed permission.
    pub proof fn cast_to_untyped(tracked self) -> (tracked (dst, typed_value): (
        SeqPointsTo<u8>,
        Seq<Option<T>>,
    ))
        requires
            self.wf(),
        ensures
            dst.ptr() == self.ptr() as *mut u8,
            dst.len() == self.len() * layout::size_of::<T>(),
            dst.abstract_bytes() == self.abstract_bytes(),
            forall|i: int|
                0 <= i < self.len() ==> {
                    &&& typed_value[i].is_some() <==> (#[trigger] self.mem_contents()[i]).is_init()
                    &&& typed_value[i].is_some() ==> typed_value[i].unwrap()
                        == self.mem_contents()[i].value()
                },
            typed_value.len() == self.len(),
            dst.wf(),
        decreases self.len(),
    {
        broadcast use
            group_vstd_default,
            align_of_u8,
            crate::vstd::arithmetic::mul::group_mul_basics,
        ;

        if self.len() == 0 {
            (SeqPointsTo::<u8>::empty(self.ptr() as *mut u8), Seq::tracked_empty())
        } else {
            let tracked (head, mut tail) = self.split((self.len() - 1) as nat);
            let tracked (tail_u8_slice, tail_mem_contents) = tail.perm.tracked_remove(
                0,
            ).cast_to_untyped();
            let tracked tail_u8 = tail_u8_slice.into_seq_pt();
            let tracked (head_u8, mut head_mem_contents) = head.cast_to_untyped();
            head_mem_contents.tracked_push(tail_mem_contents);
            assert(layout::size_of::<T>() + (self.len() - 1) * layout::size_of::<T>() == self.len()
                * layout::size_of::<T>()) by (nonlinear_arith);
            assert(forall|i: int|
                0 <= i < self.len() - 1 ==> #[trigger] self.mem_contents()[i]
                    == head.mem_contents()[i]);
            (head_u8.join(tail_u8), head_mem_contents)
        }
    }

    /// Splits the `SeqPointsTo<T>` into two permissions at the index boundary `mid`.
    pub proof fn split(tracked self, mid: nat) -> (tracked (first, second): (Self, Self))
        requires
            0 <= mid <= self.len(),
            self.wf(),
        ensures
            first.seq_perm() == self.seq_perm().take(mid as int),
            second.seq_perm() == self.seq_perm().skip(mid as int),
            first.abstract_bytes() == self.abstract_bytes().take(
                mid as int * layout::size_of::<T>(),
            ),
            second.abstract_bytes() == self.abstract_bytes().skip(
                mid as int * layout::size_of::<T>(),
            ),
            first.ptr() == self.ptr(),
            second.ptr() == ptr_mut_from_data(
                PtrData::<T> {
                    addr: (self.ptr()@.addr + mid * layout::size_of::<T>()) as usize,
                    provenance: self.ptr()@.provenance,
                    metadata: self.ptr()@.metadata,
                },
            ),
            first.wf(),
            second.wf(),
    {
        broadcast use {group_vstd_default, crate::vstd::arithmetic::mul::lemma_mul_inequality};

        if self.len() != 0 && size_of::<T>() != 0 {
            assert(layout::size_of::<T>() * self.len() != 0) by (nonlinear_arith)
                requires
                    self.len() != 0,
                    size_of::<T>() != 0,
            ;
            self.provenance_non_null();
        }
        let ghost ghost_self = self;

        let tracked mut perm = self.perm;
        let tracked other = perm.tracked_skip(mid as int);

        let tracked first = Self { perm: perm, ptr: self.ptr };
        let tracked second = Self {
            perm: other,
            ptr: Ghost(
                ptr_mut_from_data(
                    PtrData::<T> {
                        addr: (self.ptr()@.addr + mid * layout::size_of::<T>()) as usize,
                        provenance: self.ptr()@.provenance,
                        metadata: self.ptr()@.metadata,
                    },
                ),
            ),
        };
        if self.len() != 0 {
            if size_of::<T>() != 0 {
                assert((ghost_self.ptr()@.addr + mid * layout::size_of::<T>()) as nat % align_of::<
                    T,
                >() == 0) by {
                    broadcast use {lemma_mul_mod_noop_right, lemma_add_mod_noop, layout_of_sized};

                }
                assert(ghost_self.ptr()@.addr + mid * layout::size_of::<T>() + second.len()
                    * layout::size_of::<T>() == ghost_self.ptr()@.addr + ghost_self.len()
                    * layout::size_of::<T>()) by (nonlinear_arith)
                    requires
                        mid + second.len() == ghost_self.len(),
                ;
                assert forall|i: nat| 0 <= i < second.len() implies #[trigger] second[i].ptr()@.addr
                    == second.ptr()@.addr + i * layout::size_of::<T>() by {
                    assert(ghost_self.ptr()@.addr + (i + mid) * layout::size_of::<T>()
                        == ghost_self.ptr()@.addr + mid * layout::size_of::<T>() + i
                        * layout::size_of::<T>()) by (nonlinear_arith);
                }
            }
            Self::abstract_bytes_subrange(ghost_self.seq_perm(), mid as int);
        }
        (first, second)
    }

    /// Concatenates `SeqPointsTo<T>` permissions `self` and `other`,
    /// provided their pointers have the same provenance
    /// and `other`'s pointer starts at the end of `self`'s domain.
    pub proof fn join(tracked self, tracked other: Self) -> (tracked joined: Self)
        requires
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len() * layout::size_of::<T>(),
            self.wf(),
            other.wf(),
        ensures
            joined.ptr() == self.ptr(),
            joined.seq_perm() == self.seq_perm() + other.seq_perm(),
            joined.abstract_bytes() == self.abstract_bytes() + other.abstract_bytes(),
            joined.wf(),
    {
        broadcast use group_vstd_default;

        let tracked mut perm = self.perm;
        perm.tracked_add(other.perm);

        let tracked joined = Self { perm: perm, ptr: Ghost(self.ptr()) };

        Self::abstract_bytes_subrange(joined.seq_perm(), self.len() as int);
        assert(joined.seq_perm().subrange(0, self.len() as int) == self.seq_perm());
        assert(joined.seq_perm().subrange(self.len() as int, joined.len() as int)
            == other.seq_perm());

        assert(joined.ptr()@.addr + self.len() * layout::size_of::<T>() + other.len()
            * layout::size_of::<T>() == joined.ptr()@.addr + joined.len() * layout::size_of::<T>())
            by (nonlinear_arith)
            requires
                self.len() + other.len() == joined.len(),
        ;

        assert forall|i: nat| 0 <= i < other.len() implies #[trigger] joined[i
            + self.len()].ptr()@.addr == joined.ptr()@.addr + (i + self.len()) * layout::size_of::<
            T,
        >() by {
            assert(self.ptr()@.addr + self.len() * layout::size_of::<T>() + i * layout::size_of::<
                T,
            >() == self.ptr()@.addr + (i + self.len()) * layout::size_of::<T>())
                by (nonlinear_arith);
        }
        assert forall|i: nat| 0 <= i < joined.len() implies #[trigger] joined[i].ptr()@.addr
            == joined.ptr()@.addr + i * layout::size_of::<T>() by {
            if i < self.len() {
                assert(joined[i].ptr()@.addr == joined.ptr()@.addr + i * layout::size_of::<T>());
            } else {
                assert(joined[i].ptr()@.addr == joined[(i - self.len()) as nat
                    + self.len()].ptr()@.addr);
            }
        }

        joined
    }

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
            r.seq_perm() == old(self).seq_perm().subrange(i as int, j as int),
            // Need to add requirement that decoding holds on every PointsTo<T>?
            // Implicitly we expect that if wf holds, each PointsTo satisfies its axioms
            final(r).wf() && final(r).ptr() == r.ptr() && final(r).len() == r.len() ==> {
                &&& final(self).wf()
                &&& final(self).ptr() == old(self).ptr()
                &&& final(self).seq_perm() == old(self).seq_perm().subrange(0, i as int)
                    + final(r).seq_perm() + old(self).seq_perm().subrange(
                    j as int,
                    old(self).len() as int,
                )
            },
    ;

    /// Creates a `PointsToRaw` reference from a `SeqPointsTo<V>` reference with the same provenance
    /// and a range starting at the address of the `PointsTo<V>` with length `size_of::<V>() * self.len()`.
    pub proof fn as_untyped(tracked &self) -> (tracked raw: &PointsToUnaligned<[u8]>)
        requires
            self.wf(),
        ensures
            self.ptr()@.addr == raw.ptr()@.addr,
            self.ptr()@.provenance == raw.ptr()@.provenance,
            self.len() * layout::size_of::<T>() == raw.ptr()@.metadata,
            self.abstract_bytes() == raw.abstract_bytes(),
            raw.is_fully_uninit(),
    {
        broadcast use group_raw_ptr_axioms;
        // use_type_invariant(&self);

        seq_into_slice_shared(self).as_untyped()
    }
}

impl SeqPointsTo<u8> {
    /// We can cast a `SeqPointsTo<u8>` to a `SeqPointsTo<T>` of length `capacity` under the following conditions:
    ///
    /// (1) The pointer's address is aligned to `T`.
    ///
    /// (2) The length is exactly `capacity * layout::size_of::<T>()`.
    ///
    /// (3) For each non-None element in `typed_value`, the corresponding abstract bytes for the `SeqPointsTo<u8>` can be decoded
    ///     into the given value. Note that `typed_value` is allowed to contain None items (these are ignored for purposes of decoding)
    ///     and can be a prefix of the total `capacity` (in which case, the remaining memory is all logically uninitialized).
    ///
    /// The resulting `SeqPointsTo<T>` will have a prefix of memory corresponding to `typed_value`.
    /// The rest of the memory will be logically uninitialized. The abstract bytes will also remain the same.
    pub proof fn cast_to_typed<T>(
        tracked self,
        capacity: usize,
        tracked typed_value: Seq<Option<T>>,
    ) -> (tracked out: SeqPointsTo<T>)
        requires
            self.ptr()@.addr as nat % align_of::<T>() == 0,
            self.len() == capacity * layout::size_of::<T>(),
            typed_value.len() <= capacity,
            forall|i: int|
                0 <= i < typed_value.len() && typed_value[i].is_some() ==> #[trigger] abs_decode::<
                    T,
                >(
                    self.abstract_bytes().subrange(
                        i * layout::size_of::<T>(),
                        (i + 1) * layout::size_of::<T>(),
                    ),
                    &typed_value[i].unwrap(),
                ),
            self.wf(),
        ensures
            out.ptr() == self.ptr() as *mut T,
            out.len() == capacity,
            out.abstract_bytes() == self.abstract_bytes(),
            forall|i: int|
                0 <= i < typed_value.len() ==> {
                    &&& (#[trigger] out.mem_contents()[i]).is_init() <==> typed_value[i].is_some()
                    &&& typed_value[i].is_some() ==> typed_value[i].unwrap()
                        == out.mem_contents()[i].value()
                },
            out.wf(),
        decreases capacity,
    {
        broadcast use
            group_vstd_default,
            align_of_u8,
            crate::vstd::arithmetic::mul::group_mul_basics,
        ;

        if capacity == 0 {
            SeqPointsTo::<T>::empty(self.ptr() as *mut T)
        } else {
            if layout::size_of::<T>() != 0 {
                assert(capacity * layout::size_of::<T>() != 0) by (nonlinear_arith)
                    requires
                        capacity != 0,
                        layout::size_of::<T>() != 0,
                ;
                self.provenance_non_null();
            }
            // split into "head" and "tail", where tail is the last permission

            assert(0 <= (capacity - 1) as nat * layout::size_of::<T>() <= capacity
                * layout::size_of::<T>()) by (nonlinear_arith)
                requires
                    capacity > 0,
            ;
            assert((self.ptr()@.addr + (capacity - 1) as nat * layout::size_of::<T>()) as nat
                % align_of::<T>() == 0) by {
                broadcast use {lemma_mul_mod_noop_right, lemma_add_mod_noop, layout_of_sized};

            }
            Self::abstract_bytes_subrange(self.seq_perm(), (capacity - 1) * layout::size_of::<T>());
            let tracked (head, mut tail) = self.split(
                (capacity - 1) as nat * layout::size_of::<T>(),
            );

            // cast the tail into either an init or uninit permission, depending on typed_value
            let tracked mut head_typed_value = typed_value;
            let tracked mut tail_typed_value_opt;
            if typed_value.len() == capacity {
                tail_typed_value_opt = Some(head_typed_value.tracked_pop());
            } else {
                tail_typed_value_opt = None;
            }
            let tracked tail_slice = seq_into_slice(tail);
            assert(layout::size_of::<T>() == (capacity - 1 + 1) * layout::size_of::<T>() - (capacity
                - 1) * layout::size_of::<T>()) by (nonlinear_arith);
            let tracked tail_pt;
            if typed_value.len() == capacity && typed_value[capacity - 1].is_some() {
                let tracked tail_typed_value = tail_typed_value_opt.tracked_take().tracked_take();
                tail_pt = tail_slice.cast_to_typed(tail_typed_value);
                assert(tail_pt.value() == typed_value[capacity - 1].unwrap());
            } else {
                tail_pt = tail_slice.cast_to_typed_uninit();
                if typed_value.len() == capacity {
                    assert(tail_pt.is_uninit());
                }
            }
            let tracked mut tail_perm = Seq::tracked_empty();
            tail_perm.tracked_push(tail_pt);
            let tracked tail_typed = SeqPointsTo { perm: tail_perm, ptr: Ghost(tail_pt.ptr()) };
            SeqPointsTo::<T>::abstract_bytes_len_helper(tail_typed.seq_perm());

            // invoke inductive hypothesis on head
            assert forall|i: int|
                0 <= i < capacity - 1 implies #[trigger] head.abstract_bytes().subrange(
                i * layout::size_of::<T>(),
                (i + 1) * layout::size_of::<T>(),
            ) == self.abstract_bytes().subrange(
                i * layout::size_of::<T>(),
                (i + 1) * layout::size_of::<T>(),
            ) by {
                assert(0 <= i * layout::size_of::<T>() <= (i + 1) * layout::size_of::<T>() <= (
                capacity - 1) * layout::size_of::<T>()) by (nonlinear_arith)
                    requires
                        0 <= i < capacity - 1,
                ;
                self.abstract_bytes().lemma_slice_of_slice(
                    0,
                    (capacity - 1) * layout::size_of::<T>(),
                    i * layout::size_of::<T>(),
                    (i + 1) * layout::size_of::<T>(),
                );
            }
            let tracked head_typed = head.cast_to_typed((capacity - 1) as usize, head_typed_value);

            // join head and tail
            let tracked res = head_typed.join(tail_typed);
            assert(res.mem_contents() == head_typed.mem_contents() + tail_typed.mem_contents());
            res
        }
    }
}

pub open spec fn addr_from_index<T>(ptr: *mut [T], i: nat) -> usize
    recommends
        ptr@.addr + i * layout::size_of::<T>() <= usize::MAX,
{
    (ptr@.addr + i * layout::size_of::<T>()) as usize
}

pub open spec fn range_set(begin: nat, len: nat) -> Set<nat> {
    Set::new(|i: nat| begin <= i < begin + len)
}

pub open spec fn bounded_set(len: nat) -> Set<nat> {
    range_set(0, len)
}

pub open spec fn get_index_offset<T>(base_ptr: *mut [T], other_ptr: *mut [T]) -> nat
    recommends
        layout::size_of::<T>() != 0,
        base_ptr@.addr <= other_ptr@.addr,
        (other_ptr@.addr - base_ptr@.addr) as nat % layout::size_of::<T>() == 0,
{
    (other_ptr@.addr - base_ptr@.addr) as nat / layout::size_of::<T>()
}

pub open spec fn map_keys<T>(map: Map<nat, T>, offset: nat) -> Map<nat, T> {
    Map::new(
        |i: nat| map.dom().map(|i: nat| i + offset).contains(i),
        |i: nat| map[(i - offset) as nat],
    )
}

// Allocation and deallocation via the global allocator
/// Permission to perform a deallocation with the global allocator.
#[verifier::external_body]
pub tracked struct Dealloc {
    no_copy: NoCopy,
}

/// Data associated with a `Dealloc` permission.
pub ghost struct DeallocData {
    /// The originally requested size to be allocated. May be smaller than the actual allocated size.
    pub size: nat,
    /// The provenance of the allocation.
    pub provenance: Provenance,
}

impl Dealloc {
    pub uninterp spec fn view(self) -> DeallocData;

    /// Start address of the allocation you are allowed to deallocate.
    #[verifier::inline]
    pub open spec fn addr(self) -> usize {
        self.view().provenance.data().start_addr()
    }

    /// Size of the allocation you are allowed to deallocate.
    #[verifier::inline]
    pub open spec fn size(self) -> nat {
        self.view().size
    }

    /// Alignment of the allocation you are allowed to deallocate.
    #[verifier::inline]
    pub open spec fn align(self) -> nat {
        self.view().provenance.data().alignment()
    }

    /// Provenance of the allocation you are allowed to deallocate.
    #[verifier::inline]
    pub open spec fn provenance(self) -> Provenance {
        self.view().provenance
    }

    /// We can always create a `Dealloc` permission for an empty allocation with null provenance.
    pub axiom fn empty() -> (tracked dealloc: Self)
        ensures
            dealloc@.provenance == Provenance::None,
            dealloc@.size == 0,
    ;

    /// If the size is non-zero, then the pointer's provenance is non-null.
    /// <https://doc.rust-lang.org/std/ptr/index.html#provenance>
    pub axiom fn provenance_non_null(tracked &self)
        requires
            self@.size != 0,
        ensures
            self@.provenance != Provenance::None,
    ;

    /// If the provenance is `Some`,
    /// the originally requested size must be at most the actually allocated size.
    pub axiom fn in_bounds(tracked &self)
        requires
            self@.provenance != Provenance::None,
        ensures
            self@.size <= self@.provenance.data().alloc_len(),
    ;

    /// Guarantees that the memory ranges associated with two distinct, non-ZST permissions will not overlap,
    /// since you cannot have two `Dealloc` permissions to the same allocation.
    /// (`self` is an &mut reference to enforce distinctness,
    /// so you cannot pass the same PointsTo as both arguments.)
    /// Since both allocations are non-zero-sized, this implies the start addresses have distinct addresses.
    ///
    /// Note: If either allocation is zero-sized, we get disjointness "for free" without having to call this axiom,
    /// since the empty memory range cannot possibly intersect with any other memory.
    /// However, note that if one allocation is empty and the other is a non-empty,
    /// the disjointness definition as stated here here does not hold,
    /// since the ZST start address could be in the middle of the non-ZST's range.
    pub axiom fn is_disjoint<S>(tracked &mut self, tracked other: &Self)
        requires
            self@.provenance != Provenance::None,
            other@.provenance != Provenance::None,
            self@.provenance.data().alloc_len() != 0,
            other@.provenance.data().alloc_len() != 0,
        ensures
            *old(self) == *final(self),
            final(self)@.provenance.data().start_addr() as int
                + final(self)@.provenance.data().alloc_len()
                <= other@.provenance.data().start_addr() as int
                || other@.provenance.data().start_addr() as int
                + other@.provenance.data().alloc_len()
                <= final(self)@.provenance.data().start_addr() as int,
    ;
}
