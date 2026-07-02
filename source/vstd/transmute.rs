#![allow(unused_imports)]

use super::arithmetic::power::*;
use super::arithmetic::power2::*;
use super::endian::*;
use super::layout::*;
use super::math::*;
use super::prelude::*;
use super::raw_ptr::*;
use super::seq::*;
use super::type_representation::*;
use crate::vstd::group_vstd_default;

verus! {

broadcast use {group_layout_axioms, group_vstd_default};

/// Generic precondition on transmute.
pub open spec fn transmute_pre<T, U>(src: T, dst: U) -> bool {
    &&& forall|bytes|
        #![trigger abs_encode::<T>(&src, bytes)]
        #![trigger abs_decode::<U>(bytes, &dst)]
        abs_encode::<T>(&src, bytes) ==> abs_decode::<U>(bytes, &dst)
    &&& abs_can_be_encoded::<T>()
}

/// Generic postcondition on transmute.
pub open spec fn transmute_post<U>(dst_ghost: U, dst: U) -> bool {
    dst_ghost == dst
}

/// Generic precondition on transmute for "pointed-to" values of the given types.
pub open spec fn transmute_pre_points_to<T: ?Sized, U: ?Sized>(src: &T, dst: &U) -> bool {
    &&& forall|bytes| #[trigger] abs_decode::<T>(bytes, src) ==> abs_decode::<U>(bytes, dst)
    &&& abs_can_be_encoded::<T>()
}

pub broadcast proof fn abs_encode_impl<T: AbstractByteRepresentation>(v: T, b: Seq<AbstractByte>)
    requires
        T::can_be_encoded(),
    ensures
        #![trigger abs_encode::<T>(&v, b)]
        #![trigger T::encode(v, b)]
        #![trigger abs_decode::<T>(b, &v)]
        #![trigger T::decode(b, v)]
        abs_encode::<T>(&v, b) <==> T::encode(v, b),
        abs_decode::<T>(b, &v) <==> T::decode(b, v),
{
    <T as AbstractByteRepresentation>::abs_encode_impl(v, b);
}

pub broadcast proof fn abs_can_be_encoded_impl<T: AbstractByteRepresentation>()
    requires
        T::can_be_encoded(),
    ensures
        #[trigger] abs_can_be_encoded::<T>(),
{
    <T as AbstractByteRepresentation>::abs_can_be_encoded_impl();
}

pub broadcast proof fn abs_encode_impl_unsized<
    T: ?Sized,
    EncodingT: AbstractByteRepresentationUnsized<T>,
>(v: &T, b: Seq<AbstractByte>)
    requires
        EncodingT::can_be_encoded(),
    ensures
        #![trigger abs_encode::<T>(v, b), EncodingT::encode(v, b)]
        #![trigger abs_decode::<T>(b, v), EncodingT::decode(b, v)]
        abs_encode::<T>(v, b) <==> EncodingT::encode(v, b),
        abs_decode::<T>(b, v) <==> EncodingT::decode(b, v),
{
    EncodingT::abs_encode_impl(v, b);
}

pub proof fn abs_can_be_encoded_impl_unsized<
    T: ?Sized,
    EncodingT: AbstractByteRepresentationUnsized<T>,
>()
    requires
        EncodingT::can_be_encoded(),
    ensures
        abs_can_be_encoded::<T>(),
{
    EncodingT::abs_can_be_encoded_impl();
}

pub broadcast group group_transmute_axioms {
    abs_encode_impl,
    abs_can_be_encoded_impl,
    abs_encode_impl_unsized,
    abs_decode_mem_contents,
    abs_decode_mem_contents_unsized,
    group_type_representation_axioms,
}

/* "Test cases" on transmute to validate the encoding specs */

macro_rules! transmute_refl_unique_lemma {
    ($(
        ($typ:ty, $refl_lemma_name:ident, $unique_lemma_name:ident);
    )+) => {$(
        verus! {
            /// A value `x: $typ` can be transmuted to itself.
            pub proof fn $refl_lemma_name(tracked x: $typ, y: $typ)
                requires
                    x == y
                ensures
                    transmute_pre(x, y),
            {
                broadcast use group_transmute_axioms;

                assert forall|bytes| abs_encode::<$typ>(&x, bytes) implies abs_decode::<$typ>(bytes, &(y@)) by {
                    <$typ as AbstractByteRepresentation>::encoding_invertible(x, bytes);
                }
            }

            /// When a `$typ` is transmuted to a `$typ`, the value can only be transmuted to itself.
            pub proof fn $unique_lemma_name(tracked x: $typ, y: $typ)
                requires
                    transmute_pre(x, y)
                ensures
                    x == y
            {
                broadcast use group_transmute_axioms;

                let bytes = <$typ as AbstractByteRepresentation>::encoding_exists(x);
            }
        }
    )+};
}

transmute_refl_unique_lemma! {
    ((), transmute_unit_refl, transmute_unit_unique);
    (bool, transmute_bool_refl, transmute_bool_unique);
    (u8, transmute_u8_refl, transmute_u8_unique);
    (u16, transmute_u16_refl, transmute_u16_unique);
    (u32, transmute_u32_refl, transmute_u32_unique);
    (u64, transmute_u64_refl, transmute_u64_unique);
    (u128, transmute_u128_refl, transmute_u128_unique);
    (usize, transmute_usize_refl, transmute_usize_unique);
    (i8, transmute_i8_refl, transmute_i8_unique);
    (i16, transmute_i16_refl, transmute_i16_unique);
    (i32, transmute_i32_refl, transmute_i32_unique);
    (i64, transmute_i64_refl, transmute_i64_unique);
    (i128, transmute_i128_refl, transmute_i128_unique);
    (isize, transmute_isize_refl, transmute_isize_unique);
}

/// A value `x: *mut T` for `T: Sized` can be transmuted to itself.
pub proof fn transmute_mut_ptr_sized_refl<T: Sized>(tracked x: *mut T, y: *mut T)
    requires
        x@ == y@,
    ensures
        transmute_pre(x, y),
{
    broadcast use group_transmute_axioms;

    assert forall|bytes| abs_encode::<*mut T>(&x, bytes) implies abs_decode::<*mut T>(
        bytes,
        &y,
    ) by {
        <*mut T as AbstractByteRepresentation>::encoding_invertible(x, bytes);
    }
}

/// When a `*mut T` is transmuted to a `*mut T` for `T: Sized`, a value can only be transmuted to itself.
pub proof fn transmute_mut_ptr_sized_unique<T: Sized>(tracked x: *mut T, y: *mut T)
    requires
        transmute_pre(x, y),
    ensures
        x@ == y@,
{
    broadcast use group_transmute_axioms;

    let bytes = <*mut T as AbstractByteRepresentation>::encoding_exists(x);
}

/// A value `x: *const T` for `T: Sized` can be transmuted to itself.
pub proof fn transmute_const_ptr_sized_refl<T: Sized>(tracked x: *const T, y: *const T)
    requires
        x@ == y@,
    ensures
        transmute_pre(x, y),
{
    broadcast use group_transmute_axioms;

    assert forall|bytes| abs_encode::<*const T>(&x, bytes) implies abs_decode::<*const T>(
        bytes,
        &y,
    ) by {
        <*const T as AbstractByteRepresentation>::encoding_invertible(x, bytes);
    }
}

/// When a `*const T` is transmuted to a `*const T` for `T: Sized`, a value can only be transmuted to itself.
pub proof fn transmute_const_ptr_sized_unique<T: Sized>(tracked x: *const T, y: *const T)
    requires
        transmute_pre(x, y),
    ensures
        x@ == y@,
{
    broadcast use group_transmute_axioms;

    let bytes = <*const T as AbstractByteRepresentation>::encoding_exists(x);
}

// we cannot prove that x can only be transmuted to y because that would need stronger properties from the metadata encoding
/// When transmuting a `*mut T` to a `*mut T` for `T: ?Sized`, a value `x: *mut T` can be transmuted to itself.
pub proof fn transmute_mut_ptr_unsized_refl<T: ?Sized>(tracked x: *mut T, y: *mut T)
    requires
        ptr_metadata_encoding_well_defined::<T>(),
        x == y,
    ensures
        transmute_pre(x, y),
{
    broadcast use group_transmute_axioms;

    assert forall|bytes| abs_encode::<*mut T>(&x, bytes) implies abs_decode::<*mut T>(
        bytes,
        &y,
    ) by {
        <*mut T as AbstractByteRepresentation>::encoding_invertible(x, bytes);
    }
}

/// When transmuting a `*const T` to a `*const T` for `T: ?Sized`, a value `x: *const T` can be transmuted to itself.
pub proof fn transmute_const_ptr_unsized_refl<T: ?Sized>(tracked x: *const T, y: *const T)
    requires
        ptr_metadata_encoding_well_defined::<T>(),
        x == y,
    ensures
        transmute_pre(x, y),
{
    broadcast use group_transmute_axioms;

    assert forall|bytes| abs_encode::<*const T>(&x, bytes) implies abs_decode::<*const T>(
        bytes,
        &y,
    ) by {
        <*const T as AbstractByteRepresentation>::encoding_invertible(x, bytes);
    }
}

/// A `usize` can be transmuted to a `*mut T` for `T: Sized`. The resulting pointer has an address corresponding to the source value and a null `Provenance`.
pub proof fn transmute_usize_mut_ptr<T: Sized>(tracked src: usize) -> (tracked dst: *mut T)
    ensures
        transmute_pre(src, dst),
        dst == ptr_mut_from_data(
            PtrData::<T> { addr: src, provenance: Provenance::null(), metadata: () },
        ),
{
    broadcast use group_transmute_axioms;

    let tracked dst = tracked_ptr_mut_from_data(
        PtrData { addr: src, provenance: Provenance::null(), metadata: () },
    );
    assert forall|bytes| #[trigger] abs_encode::<usize>(&src, bytes) implies abs_decode::<*mut T>(
        bytes,
        &dst,
    ) by {
        assert(bytes =~= bytes.subrange(0, size_of::<usize>() as int));
        assert(Seq::<AbstractByte>::empty() =~= bytes.subrange(
            size_of::<usize>() as int,
            size_of::<*mut T>() as int,
        ));
    }
    dst
}

/// If the memory is initialized, then the bytes must decode into the given value in memory.
/// If the memory is uninitialized, then the bytes cannot be decoded to any value.
pub broadcast axiom fn abs_decode_mem_contents<T>(bytes: Seq<AbstractByte>, value: MemContents<T>)
    ensures
        #[trigger] abs_decode::<MemContents<T>>(bytes, &value) <==> (
        value matches MemContents::Init(t) && abs_decode::<T>(bytes, &t)),
;

/// If the memory is initialized, then the bytes must decode into the given value in memory.
/// If the memory is uninitialized, then the bytes cannot be decoded to any value.
pub broadcast axiom fn abs_decode_mem_contents_unsized<T: ?Sized>(
    bytes: Seq<AbstractByte>,
    value: MemContents<&T>,
)
    ensures
        #[trigger] abs_decode::<MemContents<&T>>(bytes, &value) <==> (
        value matches MemContents::Init(t) && abs_decode::<T>(bytes, t)),
;

impl<T> PointsTo<T> {
    /// Invariant: If this memory is initialized, then it its abstract bytes must decode into the value in memory.
    pub axiom fn abstract_bytes_decode(&self)
        ensures
            self.is_init() ==> #[trigger] abs_decode::<MemContents<T>>(
                self.abstract_bytes(),
                &self.mem_contents(),
            ),
    ;

    /// A `PointsTo<T>` can always be transmuted to a logically uninitialized `PointsTo<[u8]>`.
    /// The `mem_contents_seq()` on the resulting permission is not specified, meaning that the permission cannot be used to read `u8` values from this memory.
    /// (In some scenarios, it could be safe to read `u8` values from this memory, but this would require a stronger precondition
    /// that the abstract bytes of `self` can be decoded into `u8` values, i.e., the abstract bytes must be initialized.
    /// For our current use cases, this is not necessary.)
    /// The abstract bytes remain the same. This preserves the typed contents in memory on a roundtrip transmute (see `PointsTo<[u8]>::transmute_to_typed`).
    /// Note that this means provenance is not lost, which matches Rust's semantics for transmuting in-memory values.
    ///
    /// This axiom also returns a `tracked MemContents<T>`, which is intended to be used with `PointsTo<[u8]>::transmute_to_typed` in order to maintain the contents of the memory on a roundtrip.
    /// Because the `T` field for the `MemContents::Init` variant is marked as `ghost`, one cannot extract a `tracked T` from a `tracked MemContents<T>`.
    /// This prohibits creating permissions out of thin air, in the case where `T` is a type that stores/represents a permission (e.g., shared references).
    pub axiom fn transmute_to_u8_uninit(tracked self) -> (tracked (dst, mem_contents): (
        PointsTo<[u8]>,
        MemContents<T>,
    ))
        ensures
            self.abstract_bytes() == dst.abstract_bytes(),
            self.ptr()@.addr == dst.ptr()@.addr,
            self.ptr()@.provenance == dst.ptr()@.provenance,
            size_of::<T>() == dst.ptr()@.metadata,
            mem_contents == self.mem_contents(),
    ;
}

impl<T> PointsTo<[T]> {
    /// Invariant: For all elements in this slice of memory, if the memory is initialized, then the corresponding abstract bytes must decode into the value in memory.
    pub axiom fn abstract_bytes_decode(&self)
        ensures
            forall|i|
                0 <= i < self.mem_contents_seq().len() && self.mem_contents_seq()[i].is_init()
                    ==> #[trigger] abs_decode::<MemContents<T>>(
                    self.abstract_bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
                    &self.mem_contents_seq()[i],
                ),
    ;
}

impl PointsTo<str> {
    /// Invariant: If this memory is initialized, then the corresponding abstract bytes must decode into the value in memory.
    pub axiom fn abstract_bytes_decode(&self)
        ensures
            self.is_init() ==> abs_decode::<MemContents<&str>>(
                self.abstract_bytes(),
                &self.mem_contents(),
            ),
    ;
}

impl PointsTo<[u8]> {
    /// A `PointsTo<[u8]>` can be transmuted to an initialized `PointsTo<T>` when the abstract bytes can be
    /// decoded into a `MemContents<T>` and the pointer for this permission is of the expected length.
    /// The resulting permission will take on the given `MemContents<T>`.
    /// The abstract bytes remain the same. This preserves the typed contents in memory on a roundtrip transmute (see `PointsTo<T>::transmute_to_u8`).
    /// Note that this means provenance is not lost, which matches Rust's semantics for transmuting in-memory values.
    ///
    /// The `dst_mem_contents` argument must be tracked in order to prohibit creating permissions out of thin air,
    /// in the case where `T` is a type that stores/represents a permission (e.g., shared references).
    /// Note because `MemContents<T>` is a `ghost` struct, one cannot create a `tracked MemContents<T>` out of "raw", `ghost` or `tracked` `T` values.
    /// The only way to obtain a `tracked MemContents<T>` is via the `PointsTo<T>::transmute_to_u8_uninit` axiom.
    /// This ensures that the `dst_mem_contents` in fact correspond to actual values in memory.
    pub axiom fn transmute_to_typed<T>(
        tracked self,
        tracked dst_mem_contents: MemContents<T>,
    ) -> (tracked dst: PointsTo<T>)
        requires
            abs_decode::<MemContents<T>>(self.abstract_bytes(), &dst_mem_contents),
            size_of::<T>() == self.ptr()@.metadata,
        ensures
            self.abstract_bytes() == dst.abstract_bytes(),
            dst.mem_contents() == dst_mem_contents,
            self.ptr() as *mut T == dst.ptr(),
    ;

    /// A `PointsTo<[u8]>` can always be transmuted to a logically uninitialized `PointsTo<T>`.
    /// The `mem_contents_seq()` on the resulting permission is not specified, meaning that the permission cannot
    /// be used to read `T` values from this memory.
    /// The abstract bytes remain the same. This preserves the typed contents in memory on a roundtrip transmute (see `PointsTo<T>::transmute_to_u8`).
    /// Note that this means provenance is not lost, which matches Rust's semantics for transmuting in-memory values.
    pub axiom fn transmute_to_typed_uninit<T>(tracked self) -> (tracked dst: PointsTo<T>)
        requires
            size_of::<T>() == self.ptr()@.metadata,
        ensures
            self.abstract_bytes() == dst.abstract_bytes(),
            self.ptr() as *mut T == dst.ptr(),
    ;
}

impl<T> PointsTo<T> {
    /// Transmutes an initialized `&PointsTo<T>` to an initialized `&PointsTo<U>`,
    /// where the resulting permission will take on the given `target` value in memory.
    /// Requires that it is possible to transmute between the pointed-to value of `self` and the provided value `target`.
    // This function is friendlier to use because it hides the details of the abstract bytes.
    // Clients do not have to invoke the `abstract_bytes_decode` axiom.
    // TODO: version for nondeterministic targets
    pub proof fn transmute_shared<'a, U>(tracked &'a self, tracked target: U) -> (tracked ret:
        &'a PointsTo<U>)
        requires
            transmute_pre_points_to::<T, U>(&self.value(), &target),
            self.is_init(),
        ensures
            transmute_post::<U>(target, ret.value()),
            ret.is_init(),
            ret.value() == target,
            ret.ptr() == self.ptr() as *mut U,
    {
        broadcast use group_transmute_axioms;

        self.abstract_bytes_decode();
        assert(abs_decode::<T>(self.abstract_bytes(), &self.value()));
        self.transmute_shared_inner(target)
    }

    /// An initialized `&PointsTo<T>` can always be transmuted to an initialized `&PointsTo<U>` provided that the resulting
    /// `U` value in memory can be decoded from the original permission's abstract bytes.
    /// The abstract bytes remain unchanged in the resulting permission.
    axiom fn transmute_shared_inner<'a, U>(tracked &'a self, tracked target: U) -> (tracked ret:
        &'a PointsTo<U>)
        requires
            abs_decode::<U>(self.abstract_bytes(), &target),
        ensures
            ret.is_init(),
            ret.value() == target,
            ret.ptr() == self.ptr() as *mut U,
            ret.abstract_bytes() == self.abstract_bytes(),
    ;
}

impl PointsTo<str> {
    /// Transmutes an initialized `&PointsTo<str>` to an initialized `&PointsTo<[u8]>`,
    /// where the resulting permission will take on the given `target` value in memory.
    /// Requires that it is possible to transmute between the pointed-to value of `self` and the provided value `target`.
    pub proof fn transmute_shared<'a>(tracked &'a self, tracked target: &[u8]) -> (tracked ret:
        &'a PointsTo<[u8]>)
        requires
            transmute_pre_points_to::<str, [u8]>(self.value(), target),
            self.is_init(),
        ensures
            ret.is_init(),
            ret.value() == target@,
            ret.ptr() == self.ptr() as *mut [u8],
    {
        broadcast use group_transmute_axioms;

        self.abstract_bytes_decode();
        self.transmute_shared_inner(target)
    }

    /// An initialized `&PointsTo<str>` can always be transmuted to an initialized `&PointsTo<[u8]>` provided that the resulting
    /// `[u8]` value in memory can be decoded from the original permission's abstract bytes.
    /// The abstract bytes remain unchanged in the resulting permission.
    axiom fn transmute_shared_inner<'a>(tracked &'a self, tracked target: &[u8]) -> (tracked ret:
        &'a PointsTo<[u8]>)
        requires
            abs_decode::<[u8]>(self.abstract_bytes(), target),
        ensures
            ret.is_init(),
            ret.value() == target@,
            ret.ptr() == self.ptr() as *mut [u8],
            ret.abstract_bytes() == self.abstract_bytes(),
    ;
}

impl PointsTo<[u8]> {
    /// Transmutes an initialized `&PointsTo<[u8]>` to an initialized `&PointsTo<str>`,
    /// where the resulting permission will take on the given `target` value in memory.
    /// Requires that it is possible to transmute between the pointed-to value of `self` and the provided value `target`.
    pub proof fn transmute_shared<'a>(
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
        broadcast use group_transmute_axioms;

        self.abstract_bytes_decode();
        assert(value@.len() == self.abstract_bytes().len());
        assert forall|i: int| 0 <= i < self.mem_contents_seq().len() implies #[trigger] u8::decode(
            seq![self.abstract_bytes()[i]],
            value[i],
        ) by {
            assert(abs_decode::<MemContents<u8>>(
                self.abstract_bytes().subrange(i * size_of::<u8>(), (i + 1) * size_of::<u8>()),
                &self.mem_contents_seq()[i],
            ));
            assert(self.abstract_bytes().subrange(i * size_of::<u8>(), (i + 1) * size_of::<u8>())
                == seq![self.abstract_bytes()[i]]);
        }
        assert(EncodingU8Slice::decode(self.abstract_bytes(), value));
        assert(abs_decode::<[u8]>(self.abstract_bytes(), value));
        self.transmute_shared_inner(value, target)
    }

    /// An initialized `&PointsTo<[u8]>` can always be transmuted to an initialized `&PointsTo<str>` provided that the resulting
    /// `str` value in memory can be decoded from the original permission's abstract bytes.
    /// The abstract bytes remain unchanged in the resulting permission.
    axiom fn transmute_shared_inner<'a>(
        tracked &'a self,
        value: &[u8],
        tracked target: &str,
    ) -> (tracked ret: &'a PointsTo<str>)
        requires
            abs_decode::<str>(self.abstract_bytes(), target),
            self.value() == value@,
        ensures
            ret.is_init(),
            ret.value() == target,
            ret.ptr() == self.ptr() as *mut str,
            ret.abstract_bytes() == self.abstract_bytes(),
    ;
}

} // verus!
