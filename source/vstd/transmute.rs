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

pub uninterp spec fn can_be_decoded<T: ?Sized>() -> bool;

// compiler wants &T instead of T, complains about T not being Sized
/// Can 'value' be decoded to the given bytes?
pub uninterp spec fn decode<T: ?Sized>(value: &T, bytes: Seq<AbstractByte>) -> bool;

/// Can the given bytes always be encoded to the given value?
pub uninterp spec fn encode<T: ?Sized>(bytes: Seq<AbstractByte>, value: &T) -> bool;

// can't have T: ?Sized currently, because value and is_init are not implemented generically for DSTs
impl<T> PointsTo<T> {
    // TODO: version for nondeterministic targets
    pub axiom fn transmute<U>(tracked &self, tracked target: U) -> (tracked ret: &PointsTo<U>)
        requires
            self.is_init(),
            can_be_decoded::<T>(),
            forall|bytes|
                #![trigger decode(&self.value(), bytes)]
                #![trigger encode(bytes, &target)]
                decode(&self.value(), bytes) ==> encode(bytes, &target),
        ensures
            ret.is_init(),
            ret.value() == target,
            ret.ptr()@.addr == self.ptr()@.addr,
            ret.ptr()@.provenance == self.ptr()@.provenance,
    ;
}

/* str */

pub broadcast axiom fn str_can_be_decoded()
    ensures
        #[trigger] can_be_decoded::<str>(),
;

impl PointsTo<str> {
    pub axiom fn transmute(tracked &self, target: &[u8]) -> (tracked ret: &PointsTo<[u8]>)
        requires
            self.is_init(),
            can_be_decoded::<str>(),
            forall|bytes|
                #![trigger decode(self.value(), bytes)]
                #![trigger encode(bytes, target)]
                decode(self.value(), bytes) ==> encode(bytes, target),
        ensures
            ret.is_init(),
            ret.value() == target@,
            ret.ptr()@.addr == self.ptr()@.addr,
            ret.ptr()@.provenance == self.ptr()@.provenance,
    ;
}

/* [u8] */

pub open spec fn u8_decode_eq(value: Seq<u8>, bytes: Seq<AbstractByte>) -> bool
    decreases bytes.len(),
    via u8_decode_decreases
{
    if bytes.len() == 0 {
        value.len() == 0
    } else {
        match bytes.first() {
            AbstractByte::Uninit => false,
            AbstractByte::Init(b, _) => {
                &&& value.len() > 0
                &&& b == value.first()
                &&& u8_decode_eq(value.drop_first(), bytes.drop_first())
            },
        }
    }
}

#[verifier::decreases_by]
proof fn u8_decode_decreases(value: Seq<u8>, bytes: Seq<AbstractByte>) {
    broadcast use axiom_seq_subrange_len::<AbstractByte>;

}

pub broadcast axiom fn u8_decode(b: &[u8], bytes: Seq<AbstractByte>)
    ensures
        #![trigger decode::<[u8]>(b, bytes)]
        #![trigger encode::<[u8]>(bytes, b)]
        decode::<[u8]>(b, bytes) <==> encode::<[u8]>(bytes, b),
        decode::<[u8]>(b, bytes) <==> u8_decode_eq(b@, bytes),
;

} // verus!
