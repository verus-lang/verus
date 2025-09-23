#![allow(unused_imports)]

use super::prelude::*;
use super::raw_ptr::*;
use super::seq::*;

verus! {

// https://github.com/minirust/minirust/blob/master/spec/mem/interface.md#abstract-bytes
// https://github.com/minirust/minirust/blob/master/spec/lang/representation.md
pub enum AbstractByte {
    Uninit,
    Init(u8, Option<Provenance>),
}

pub uninterp spec fn can_be_encoded<T: ?Sized>() -> bool;

// compiler wants &T instead of T, complains about T not being Sized
/// Can 'value' be encoded to the given bytes?
pub uninterp spec fn encode<T: ?Sized>(value: &T, bytes: Seq<AbstractByte>) -> bool;

/// Can the given bytes always be decoded to the given value?
pub uninterp spec fn decode<T: ?Sized>(bytes: Seq<AbstractByte>, value: &T) -> bool;

// can't have T: ?Sized currently, because value and is_init are not implemented generically for DSTs
impl<T> PointsTo<T> {
    // TODO: version for nondeterministic targets
    pub axiom fn transmute_shared<'a, U>(tracked &'a self, tracked target: U) -> (tracked ret: & 'a PointsTo<U>)
        requires
            self.is_init(),
            can_be_encoded::<T>(),
            forall|bytes|
                #![trigger encode(&self.value(), bytes)]
                #![trigger decode(bytes, &target)]
                encode(&self.value(), bytes) ==> decode(bytes, &target),
        ensures
            ret.is_init(),
            ret.value() == target,
            ret.ptr()@.addr == self.ptr()@.addr,
            ret.ptr()@.provenance == self.ptr()@.provenance,
    ;
}

/* str */

pub broadcast axiom fn str_can_be_encoded()
    ensures
        #[trigger] can_be_encoded::<str>(),
;

impl PointsTo<str> {
    pub axiom fn transmute_shared<'a>(tracked &'a self, target: &[u8]) -> (tracked ret: &'a PointsTo<[u8]>)
        requires
            self.is_init(),
            can_be_encoded::<str>(),
            forall|bytes|
                #![trigger encode(self.value(), bytes)]
                #![trigger decode(bytes, target)]
                encode(self.value(), bytes) ==> decode(bytes, target),
        ensures
            ret.is_init(),
            ret.value() == target@,
            ret.phy() == target,
            ret.ptr()@.addr == self.ptr()@.addr,
            ret.ptr()@.provenance == self.ptr()@.provenance,
    ;
}

/* [u8] */

pub open spec fn u8_encode_eq(value: Seq<u8>, bytes: Seq<AbstractByte>) -> bool
    decreases bytes.len(),
    via u8_encode_decreases
{
    if bytes.len() == 0 {
        value.len() == 0
    } else {
        match bytes.first() {
            AbstractByte::Uninit => false,
            AbstractByte::Init(b, _) => {
                &&& value.len() > 0
                &&& b == value.first()
                &&& u8_encode_eq(value.drop_first(), bytes.drop_first())
            },
        }
    }
}

#[verifier::decreases_by]
proof fn u8_encode_decreases(value: Seq<u8>, bytes: Seq<AbstractByte>) {
    broadcast use axiom_seq_subrange_len::<AbstractByte>;

}

pub broadcast axiom fn u8_encode(b: &[u8], bytes: Seq<AbstractByte>)
    ensures
        #![trigger encode::<[u8]>(b, bytes)]
        #![trigger decode::<[u8]>(bytes, b)]
        encode::<[u8]>(b, bytes) <==> decode::<[u8]>(bytes, b),
        encode::<[u8]>(b, bytes) <==> u8_encode_eq(b@, bytes),
;

} // verus!
