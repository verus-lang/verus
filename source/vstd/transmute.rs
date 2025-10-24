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
pub open spec fn transmute_pre<T, U>(src: T, dst: U) -> bool {
    &&& forall|bytes| #[trigger] abs_encode::<T>(&src, bytes) ==> abs_decode::<U>(bytes, &dst)
    &&& can_be_encoded::<T>()
}

/// Generic postcondition on transmute.
pub open spec fn transmute_post<U>(dst_ghost: Ghost<U>, dst: U) -> bool {
    dst_ghost@ == dst
}

/// Generic precondition on transmute for `?Sized` types.
pub open spec fn transmute_pre_unsized<T: ?Sized, U: ?Sized>(src: &T, dst: &U) -> bool {
    forall|bytes| #[trigger] abs_encode::<T>(src, bytes) ==> abs_decode::<U>(bytes, dst)
}

pub broadcast proof fn abs_encode_impl<T: AbstractEncoding>(v: T, b: Seq<AbstractByte>)
    ensures
        #![trigger abs_encode::<T>(&v, b)]
        #![trigger T::encode(v, b)]
        #![trigger abs_decode::<T>(b, &v)]
        #![trigger T::decode(b, v)]
        abs_encode::<T>(&v, b) <==> T::encode(v, b),
        abs_decode::<T>(b, &v) <==> T::decode(b, v),
{
    <T as AbstractEncoding>::valid_encoding(v, b);
}

pub broadcast proof fn abs_encode_can_be_encoded<T: AbstractEncoding>()
    ensures
        #[trigger] can_be_encoded::<T>(),
{
    <T as AbstractEncoding>::can_be_encoded();
}

pub broadcast proof fn abs_encode_unsized_impl<T: ?Sized, EncodingT: AbstractEncodingUnsized<T>>(
    v: &T,
    b: Seq<AbstractByte>,
)
    ensures
        #![trigger abs_encode::<T>(v, b), EncodingT::encode(v, b)]
        #![trigger abs_decode::<T>(b, v), EncodingT::decode(b, v)]
        abs_encode::<T>(v, b) <==> EncodingT::encode(v, b),
        abs_decode::<T>(b, v) <==> EncodingT::decode(b, v),
{
    EncodingT::valid_encoding(v, b);
}

pub proof fn abs_encode_unsized_can_be_encoded<T: ?Sized, EncodingT: AbstractEncodingUnsized<T>>()
    ensures
        can_be_encoded::<T>(),
{
    EncodingT::can_be_encoded();
}

pub broadcast group group_transmute_axioms {
    abs_encode_impl,
    abs_encode_can_be_encoded,
    abs_encode_unsized_impl,
    group_type_representation_axioms,
}

/*  Helpers for specific transmute ops */

pub proof fn transmute_usize_mut_ptr<T: Sized>(src: usize) -> (dst: *mut T)
    ensures
        transmute_pre(src, dst),
        dst@.addr == src,
        dst@.provenance == Provenance::null(),
{
    broadcast use group_transmute_axioms;

    let dst = ptr_mut_from_data(
        PtrData { addr: src, provenance: Provenance::null(), metadata: () },
    );
    assert forall|bytes| #[trigger] abs_encode::<usize>(&src, bytes) implies abs_decode::<*mut T>(
        bytes,
        &dst,
    ) by {
        assert(bytes =~= bytes.subrange(0, size_of::<usize>() as int));
    }
    dst
}

impl<T: AbstractEncoding> PointsTo<T> {
    // TODO: version for nondeterministic targets
    pub axiom fn transmute_shared<'a, U: AbstractEncoding>(
        tracked &'a self,
        tracked target: U,
    ) -> (tracked ret: &'a PointsTo<U>)
        requires
            transmute_pre::<T, U>(self.value(), target),
            self.is_init(),
        ensures
            transmute_post::<U>(Ghost(target), ret.value()),
            ret.is_init(),
            ret.ptr()@.addr == self.ptr()@.addr,
            ret.ptr()@.provenance == self.ptr()@.provenance,
    ;
}

impl PointsTo<str> {
    pub axiom fn transmute_shared<'a>(tracked &'a self, target: &[u8]) -> (tracked ret:
        &'a PointsTo<[u8]>)
        requires
            self.is_init(),
            transmute_pre_unsized::<str, [u8]>(self.value(), target),
        ensures
            ret.is_init(),
            ret.value() == target@,
            ret.phy() == target,
            ret.ptr()@.addr == self.ptr()@.addr,
            ret.ptr()@.provenance == self.ptr()@.provenance,
    ;
}

} // verus!
