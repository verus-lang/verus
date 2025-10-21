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

/// Generic precondition on transmute. This requires that appropriate encodings have been defined on both the source and destination types.
pub open spec fn transmute_pre<T: AbstractEncoding, U: AbstractEncoding>(src: T, dst: U) -> bool {
    forall|bytes| #[trigger] T::encode(src, bytes) ==> U::decode(bytes, dst)
}

/// Generic postcondition on transmute.
pub open spec fn transmute_post<U: AbstractEncoding>(dst_ghost: Ghost<U>, dst: U) -> bool {
    dst_ghost@ == dst
}

/// Generic precondition on transmute for `?Sized` types. This requires that appropriate encodings have been defined on both the source and destination types.
pub open spec fn transmute_pre_unsized<
    T: ?Sized,
    U: ?Sized,
    EncodingT: AbstractEncodingUnsized<T>,
    EncodingU: AbstractEncodingUnsized<U>,
>(src: &T, dst: &U) -> bool {
    forall|bytes| #[trigger] EncodingT::encode(src, bytes) ==> EncodingU::decode(bytes, dst)
}

/*  Helpers for specific transmute ops */

pub proof fn transmute_usize_mut_ptr<T: Sized>(src: usize) -> (dst: *mut T)
    ensures
        transmute_pre(src, dst),
        dst@.addr == src,
        dst@.provenance == Provenance::null(),
{
    broadcast use usize_encode;

    let dst = ptr_mut_from_data(
        PtrData { addr: src, provenance: Provenance::null(), metadata: () },
    );
    assert forall|bytes| #[trigger]
        usize::encode(src, bytes) implies <*mut T as AbstractEncoding>::decode(bytes, dst) by {
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
    pub axiom fn transmute_shared<
        'a,
        EncodingStr: AbstractEncodingUnsized<str>,
        EncodingU8Slice: AbstractEncodingUnsized<[u8]>,
    >(tracked &'a self, target: &[u8]) -> (tracked ret: &'a PointsTo<[u8]>)
        requires
            self.is_init(),
            transmute_pre_unsized::<str, [u8], EncodingStr, EncodingU8Slice>(self.value(), target),
        ensures
            ret.is_init(),
            ret.value() == target@,
            ret.phy() == target,
            ret.ptr()@.addr == self.ptr()@.addr,
            ret.ptr()@.provenance == self.ptr()@.provenance,
    ;
}

} // verus!
