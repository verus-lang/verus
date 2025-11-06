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
    &&& forall|bytes| #[trigger] abs_encode::<T>(&src, bytes) ==> abs_decode::<U>(bytes, &(dst@))
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

pub broadcast proof fn abs_encode_impl<T: AbstractEncoding>(v: T, b: Seq<AbstractByte>)
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
    <T as AbstractEncoding>::abs_encode_impl(v, b);
}

pub broadcast proof fn abs_can_be_encoded_impl<T: AbstractEncoding>()
    requires
        T::can_be_encoded(),
    ensures
        #[trigger] abs_can_be_encoded::<T>(),
{
    <T as AbstractEncoding>::abs_can_be_encoded_impl();
}

pub broadcast proof fn abs_encode_impl_unsized<T: ?Sized, EncodingT: AbstractEncodingUnsized<T>>(
    v: &T,
    b: Seq<AbstractByte>,
)
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

pub proof fn abs_can_be_encoded_impl_unsized<T: ?Sized, EncodingT: AbstractEncodingUnsized<T>>()
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

/*  Helpers for specific transmute ops */

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
        assert(<*mut T as AbstractEncoding>::decode(bytes, dst));
    }
    Tracked(dst)
}

impl<T: AbstractEncoding> PointsTo<T> {
    // TODO: version for nondeterministic targets
    pub axiom fn transmute_shared<'a, U: AbstractEncoding>(
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
            ret.phy() == target,
            ret.ptr()@.addr == self.ptr()@.addr,
            ret.ptr()@.provenance == self.ptr()@.provenance,
            ret.ptr()@.metadata == self.ptr()@.metadata,
    ;
}

} // verus!
