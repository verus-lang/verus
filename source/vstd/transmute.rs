#![allow(unused_imports)]

use super::arithmetic::power::*;
use super::arithmetic::power2::*;
use super::endian::*;
use super::layout::*;
use super::math::*;
use super::prelude::*;
use super::primitive_int::*;
use super::raw_ptr::*;
use super::seq::*;
use super::type_representation::*;
use crate::vstd::group_vstd_default;

verus! {

broadcast use {group_layout_axioms, group_vstd_default};

/// Generic precondition on transmute.
pub open spec fn transmute_pre<T, U>(src: T, dst: Tracked<U>) -> bool {
    &&& forall|bytes|
        #![trigger abs_encode::<T>(&src, bytes)]
        #![trigger abs_decode::<U>(bytes, &(dst@))]
        abs_encode::<T>(&src, bytes) ==> abs_decode::<U>(bytes, &(dst@))
    &&& abs_can_be_encoded::<T>()
}

/// Generic postcondition on transmute.
pub open spec fn transmute_post<U>(dst_ghost: Tracked<U>, dst: U) -> bool {
    dst_ghost@ == dst
}

/// Generic precondition on transmute for `?Sized` types.
pub open spec fn transmute_pre_unsized<T: ?Sized, U: ?Sized>(src: &T, dst: Tracked<&U>) -> bool {
    &&& forall|bytes| #[trigger] abs_encode::<T>(src, bytes) ==> abs_decode::<U>(bytes, dst@)
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
    group_type_representation_axioms,
}

/* "Test cases" on transmute to validate the encoding specs */

macro_rules! transmute_refl_unique_lemma {
    ($(
        ($typ:ty, $refl_lemma_name:ident, $unique_lemma_name:ident);
    )+) => {$(
        verus! {
            /// A value `x: $typ` can be transmuted to itself.
            pub proof fn $refl_lemma_name(tracked x: $typ, y: Tracked<$typ>)
                requires
                    x == y@
                ensures
                    transmute_pre(x, y),
            {
                broadcast use group_transmute_axioms;

                assert forall|bytes| abs_encode::<$typ>(&x, bytes) implies abs_decode::<$typ>(bytes, &(y@)) by {
                    <$typ as AbstractByteRepresentation>::encoding_invertible(x, bytes);
                }
            }

            /// When a `$typ` is transmuted to a `$typ`, the value can only be transmuted to itself.
            pub proof fn $unique_lemma_name(tracked x: $typ, y: Tracked<$typ>)
                requires
                    transmute_pre(x, y)
                ensures
                    x == y@
            {
                broadcast use group_transmute_axioms;

                let bytes = <$typ as AbstractByteRepresentation>::encoding_exists(&x);
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
pub proof fn transmute_mut_ptr_sized_refl<T: Sized>(tracked x: *mut T, y: Tracked<*mut T>)
    requires
        x@ == y@@,
    ensures
        transmute_pre(x, y),
{
    broadcast use group_transmute_axioms;

    assert forall|bytes| abs_encode::<*mut T>(&x, bytes) implies abs_decode::<*mut T>(
        bytes,
        &(y@),
    ) by {
        <*mut T as AbstractByteRepresentation>::encoding_invertible(x, bytes);
    }
}

/// When a `*mut T` is transmuted to a `*mut T` for `T: Sized`, a value can only be transmuted to itself.
pub proof fn transmute_mut_ptr_sized_unique<T: Sized>(tracked x: *mut T, y: Tracked<*mut T>)
    requires
        transmute_pre(x, y),
    ensures
        x@ == y@@,
{
    broadcast use group_transmute_axioms;

    let bytes = <*mut T as AbstractByteRepresentation>::encoding_exists(&x);
}

/// A value `x: *const T` for `T: Sized` can be transmuted to itself.
pub proof fn transmute_const_ptr_sized_refl<T: Sized>(tracked x: *const T, y: Tracked<*const T>)
    requires
        x@ == y@@,
    ensures
        transmute_pre(x, y),
{
    broadcast use group_transmute_axioms;

    assert forall|bytes| abs_encode::<*const T>(&x, bytes) implies abs_decode::<*const T>(
        bytes,
        &(y@),
    ) by {
        <*const T as AbstractByteRepresentation>::encoding_invertible(x, bytes);
    }
}

/// When a `*const T` is transmuted to a `*const T` for `T: Sized`, a value can only be transmuted to itself.
pub proof fn transmute_const_ptr_sized_unique<T: Sized>(tracked x: *const T, y: Tracked<*const T>)
    requires
        transmute_pre(x, y),
    ensures
        x@ == y@@,
{
    broadcast use group_transmute_axioms;

    let bytes = <*const T as AbstractByteRepresentation>::encoding_exists(&x);
}

// we cannot prove that x can only be transmuted to y because that would need stronger properties from the metadata encoding
/// When transmuting a `*mut T` to a `*mut T` for `T: ?Sized`, a value `x: *mut T` can be transmuted to itself.
pub proof fn transmute_mut_ptr_unsized_refl<T: ?Sized>(tracked x: *mut T, y: Tracked<*mut T>)
    requires
        ptr_metadata_encoding_well_defined::<T>(),
        x == y@,
    ensures
        transmute_pre(x, y),
{
    broadcast use group_transmute_axioms;

    assert forall|bytes| abs_encode::<*mut T>(&x, bytes) implies abs_decode::<*mut T>(
        bytes,
        &(y@),
    ) by {
        <*mut T as AbstractByteRepresentation>::encoding_invertible(x, bytes);
    }
}

/// When transmuting a `*const T` to a `*const T` for `T: ?Sized`, a value `x: *const T` can be transmuted to itself.
pub proof fn transmute_const_ptr_unsized_refl<T: ?Sized>(tracked x: *const T, y: Tracked<*const T>)
    requires
        ptr_metadata_encoding_well_defined::<T>(),
        x == y@,
    ensures
        transmute_pre(x, y),
{
    broadcast use group_transmute_axioms;

    assert forall|bytes| abs_encode::<*const T>(&x, bytes) implies abs_decode::<*const T>(
        bytes,
        &(y@),
    ) by {
        <*const T as AbstractByteRepresentation>::encoding_invertible(x, bytes);
    }
}

/// A `usize` can be transmuted to a `*mut T` for `T: Sized`. The resulting pointer has an address corresponding to the source value and a null `Provenance`.
pub proof fn transmute_usize_mut_ptr<T: Sized>(tracked src: usize) -> (dst: Tracked<*mut T>)
    ensures
        transmute_pre(src, dst),
        dst@@.addr == src,
        dst@@.provenance == Provenance::null(),
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
    Tracked(dst)
}

impl<T: AbstractByteRepresentation> PointsTo<T> {
    // TODO: version for nondeterministic targets
    pub axiom fn transmute_shared<'a, U: AbstractByteRepresentation>(
        tracked &'a self,
        tracked target: Tracked<U>,
    ) -> (tracked ret: &'a PointsTo<U>)
        requires
            transmute_pre::<T, U>(self.value(), target),
            self.is_init(),
        ensures
            transmute_post::<U>(target, ret.value()),
            ret.is_init(),
            ret.ptr()@.addr == self.ptr()@.addr,
            ret.ptr()@.provenance == self.ptr()@.provenance,
            ret.ptr()@.metadata == self.ptr()@.metadata,
    ;
}

impl PointsTo<str> {
    pub axiom fn transmute_shared<'a>(tracked &'a self, target: Tracked<&[u8]>) -> (tracked ret:
        &'a PointsTo<[u8]>)
        requires
            transmute_pre_unsized::<str, [u8]>(self.value(), target),
            self.is_init(),
        ensures
            ret.is_init(),
            ret.value() == target@@,
            ret.ptr()@.addr == self.ptr()@.addr,
            ret.ptr()@.provenance == self.ptr()@.provenance,
            ret.ptr()@.metadata == self.ptr()@.metadata
    ;
}

impl PointsTo<[u8]> {
    pub axiom fn transmute_shared<'a>(tracked &'a self, value: &[u8], target: Tracked<&str>) -> (tracked ret:
        &'a PointsTo<str>)
        requires
            transmute_pre_unsized::<[u8], str>(value, target),
            self.is_init(),
            self.value() == value@ //require a separate argument for value since transmute_pre_unsized expects a &[u8] instead of a Seq<u8>
        ensures
            ret.is_init(),
            ret.value() == target,
            ret.ptr()@.addr == self.ptr()@.addr,
            ret.ptr()@.provenance == self.ptr()@.provenance,
            ret.ptr()@.metadata == self.ptr()@.metadata
    ;
}

} // verus!
