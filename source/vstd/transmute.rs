#![allow(unused_imports)]

use crate::vstd::group_vstd_default;
use super::arithmetic::power::*;
use super::arithmetic::power2::*;
use super::endian::*;
use super::layout::*;
use super::prelude::*;
use super::raw_ptr::*;
use super::seq::*;

verus! {

broadcast use {group_layout_axioms, group_vstd_default};

// https://github.com/minirust/minirust/blob/master/spec/mem/interface.md#abstract-bytes
// https://github.com/minirust/minirust/blob/master/spec/lang/representation.md

pub enum AbstractByte {
    Uninit,
    Init(u8, Option<Provenance>),
}

pub trait Encoding where Self: Sized {
    /// Can 'value' be encoded to the given bytes?
    spec fn encode(value: Self, bytes: Seq<AbstractByte>) -> bool;

    /// Returns Some(v) if the given bytes can be decoded into the value v, else None
    spec fn decode(bytes: Seq<AbstractByte>) -> Option<Self>;

    /// Required properties for encoding (sanity check for any implementation of this trait)
    proof fn encoding_props()
        ensures
            forall|v, bytes| Self::encode(v, bytes) ==> bytes.len() == size_of::<Self>(),
            forall|v, bytes| Self::encode(v, bytes) ==> Self::decode(bytes) == Some(v),
    ;
}

/* bool */

impl Encoding for bool {
    open spec fn encode(value: Self, bytes: Seq<AbstractByte>) -> bool {
        &&& bytes.len() == 1
        &&& match bytes.first() {
            AbstractByte::Init(v, None::<Provenance>) => (v == 0 && !value) || (v == 1 && value),
            _ => false,
        }
    }

    open spec fn decode(bytes: Seq<AbstractByte>) -> Option<Self> {
        if bytes.len() == 1 {
            match bytes.first() {
                AbstractByte::Init(0, _) => Some(false),
                AbstractByte::Init(1, _) => Some(true),
                _ => None,
            }
        } else {
            None
        }
    }

    proof fn encoding_props() {
    }
}

/* u8 */

impl Encoding for u8 {
    open spec fn encode(value: Self, bytes: Seq<AbstractByte>) -> bool {
        &&& bytes.len() == 1
        &&& match bytes.first() {
            AbstractByte::Init(v, None::<Provenance>) => v == value,
            _ => false,
        }
    }

    open spec fn decode(bytes: Seq<AbstractByte>) -> Option<Self> {
        match bytes.first() {
            AbstractByte::Init(v, _) => {
                if bytes.len() == 1 {
                    Some(v)
                } else {
                    None
                }
            },
            _ => None,
        }
    }

    proof fn encoding_props() {
    }
}

/* usize */

/// Convert unsiged integer (as nat) to AbstractBytes.
pub open spec fn nat_to_bytes(n: nat, size: nat) -> Seq<AbstractByte> where
    decreases size,
{
    if size == 0 {
        Seq::empty()
    } else {
        let least = (n % u8::base()) as u8;
        let least_endian = seq![AbstractByte::Init(least, None)];
        let rest = n / u8::base();
        let rest_endian = nat_to_bytes(rest, (size - 1) as nat);
        match endianness() {
            Endian::Big => rest_endian.add(least_endian),
            Endian::Little => least_endian.add(rest_endian),
        }
    }
}

pub broadcast proof fn nat_to_bytes_len_size(n: nat, size: nat)
    ensures
        #[trigger] nat_to_bytes(n, size).len() == size
    decreases size
{
    if size == 0 {
    } else {
        nat_to_bytes_len_size(n / u8::base(), (size - 1) as nat);
    }
}

/// Convert AbstractBytes to unsigned integer (as nat).
/// Returns Some if the given AbstractBytes are a valid encoding of some number, None otherwise.
pub open spec fn bytes_to_nat(b: Seq<AbstractByte>) -> Option<nat> where
    decreases b.len(),
{
    if b.len() == 0 {
        Some(0 as nat)
    } else {
        let (least, rest) = match endianness() {
            Endian::Big => (b.last(), bytes_to_nat(b.drop_last())),
            Endian::Little => (b.first(), bytes_to_nat(b.drop_first())),
        };
        match (least, rest) {
            (AbstractByte::Init(v, _), Some(n)) => Some(v as nat + n * u8::base()),
            _ => None
        }
    }
}

pub broadcast proof fn nat_to_bytes_to_nat(n: nat, size: nat)
    requires
        n < pow(u8::base() as int, size)
    ensures
        #[trigger] bytes_to_nat(nat_to_bytes(n, size)) == Some(n)
    decreases
        nat_to_bytes(n, size).len()
{
    reveal(pow);
    if nat_to_bytes(n, size).len() == 0 {
    } else {
        let bytes = nat_to_bytes(n, size);
        let (least, rest) = match endianness() {
            Endian::Big => (bytes.last(), bytes.drop_last()),
            Endian::Little => (bytes.first(), bytes.drop_first()),
        };
        assert(rest =~= nat_to_bytes(n / u8::base(), (size - 1) as nat));
        assert(least == AbstractByte::Init((n % u8::base()) as u8, None));
        assert(n / u8::base() < pow(u8::base() as int, (size - 1) as nat));
        nat_to_bytes_to_nat(n / u8::base(), (size - 1) as nat);
        assert(bytes_to_nat(rest) == Some(n / u8::base()));
        assert(bytes_to_nat(bytes) == Some(((n % u8::base()) as u8) as nat + (n / u8::base()) * u8::base()));
    }
}

impl Encoding for usize {
    open spec fn encode(value: Self, bytes: Seq<AbstractByte>) -> bool {
        bytes == nat_to_bytes(value as nat, size_of::<Self>())
    }

    open spec fn decode(bytes: Seq<AbstractByte>) -> Option<Self> {
        if bytes.len() == size_of::<Self>() {
            match bytes_to_nat(bytes) {
                Some(n) => Some(n as Self),
                None => None
            }
        } else {
            None
        }
    }

    proof fn encoding_props() {
        broadcast use nat_to_bytes_len_size, nat_to_bytes_to_nat;
        assert forall|v, bytes| Self::encode(v, bytes) implies Self::decode(bytes) == Some(v) by {
            usize_max_bounds();
            assert(8 * size_of::<usize>() == usize::BITS);
            assert(pow2(usize::BITS as nat) == pow(2, usize::BITS as nat)) by {
                broadcast use lemma_pow2;
            }
            assert(pow(2, 8 * size_of::<usize>()) == pow(pow(2, 8), size_of::<usize>())) by {
                broadcast use lemma_pow_multiplies;
            }
            assert(pow(2, 8) == u8::base()) by (compute);
            assert(pow2(usize::BITS as nat) == pow(u8::base() as int, size_of::<usize>()));
            assert(v < pow(u8::base() as int, size_of::<usize>()));
        }
    }
}

pub trait EncodingNotSized<T: ?Sized> {
    /// Can 'value' be encoded to the given bytes?
    uninterp spec fn encode(value: &T, bytes: Seq<AbstractByte>) -> bool;

    /// Can the given bytes always be decoded to the given value?
    uninterp spec fn decode(bytes: Seq<AbstractByte>, value: &T) -> bool;
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
    pub axiom fn transmute_shared<'a, U>(tracked &'a self, tracked target: U) -> (tracked ret:
        &'a PointsTo<U>)
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
    pub axiom fn transmute_shared<'a>(tracked &'a self, target: &[u8]) -> (tracked ret:
        &'a PointsTo<[u8]>)
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
