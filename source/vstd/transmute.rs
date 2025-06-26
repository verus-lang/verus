#![allow(unused_imports)]

use super::prelude::*;
use super::raw_ptr::*;
use super::seq::*;

verus!{

// https://github.com/minirust/minirust/blob/master/spec/mem/interface.md#abstract-bytes
// https://github.com/minirust/minirust/blob/master/spec/lang/representation.md

pub enum AbstractByte {
    Uninit,
    Init(u8, Option<Provenance>),
}

pub spec fn can_be_decoded<T: ?Sized>() -> bool;

/// Can 'value' be decoded to the given bytes?
pub spec fn decode<T: ?Sized>(value: &T, bytes: Seq<AbstractByte>) -> bool;

/// Can the given bytes always be encoded to the given value?
pub spec fn encode<T: ?Sized>(bytes: Seq<AbstractByte>, value: &T) -> bool;

impl<T> PointsTo<T> {
    // TODO: version for nondeterministic targets
    pub axiom fn transmute<U>(tracked self, tracked target: U) -> (tracked ret: PointsTo<U>)
        requires
            self.is_init(),
            can_be_decoded::<T>(),
            forall |bytes| decode(&self.value(), bytes) ==> encode(bytes, &target)
        ensures
            ret.is_init(),
            ret.value() == target,
            ret.ptr() == self.ptr();
}


axiom fn tracked_int(i: int) -> (tracked j: int)
    ensures j == i;

axiom fn tracked_bool(b: bool) -> (tracked b0: int)
    ensures b0 == b;

/* bools */

pub broadcast axiom fn bool_can_be_decoded()
    ensures #[trigger] can_be_decoded::<bool>();

pub broadcast axiom fn bool_decode(b: bool, bytes: Seq<AbstractByte>)
    ensures
        #![trigger decode::<bool>(&b, bytes)]
        #![trigger encode::<bool>(&b, bytes)]
        decode::<bool>(&b, bytes) <==> encode::<bool>(&b, bytes),
        decode::<bool>(&b, bytes) <==>
            (bytes == if b {
                seq![AbstractByte::Init(1, None)]
            } else {
                seq![AbstractByte::Init(0, None)]
            });

}

