#![allow(unused_imports)]

use super::arithmetic::power::*;
use super::arithmetic::power2::*;
use super::endian::*;
use super::layout::*;
use super::prelude::*;
use super::raw_ptr::*;
use super::seq::*;
use crate::vstd::group_vstd_default;

verus! {

broadcast use {group_layout_axioms, group_vstd_default};
// https://github.com/minirust/minirust/blob/master/spec/mem/interface.md#abstract-bytes
// https://github.com/minirust/minirust/blob/master/spec/lang/representation.md

pub enum AbstractByte {
    Uninit,
    Init(u8, Option<Provenance>),
}

impl AbstractByte {
    /// Returns true if all `AbstractByte`s in this sequence are `Init`.
    pub open spec fn all_init(bytes: Seq<Self>) -> bool {
        bytes.all(
            |b|
                match b {
                    AbstractByte::Init(_, _) => true,
                    _ => false,
                },
        )
    }

    /// Returns the Provenance shared by all of the (initialized) bytes in the sequence.
    /// If some bytes are uninitialized, or if some bytes do not share the same provenance (including having no provenance),
    /// then `Provenance::null()` is returned.
    pub open spec fn shared_provenance(bytes: Seq<Self>) -> Provenance
        recommends
            bytes.len() > 1,
        decreases bytes.len(),
    {
        if bytes.len() == 0 {
            Provenance::null()
        } else if bytes.len() == 1 {
            bytes.last().provenance_or_null()
        } else {
            let last_p = bytes.last().provenance_or_null();
            if Self::shared_provenance(bytes.drop_last()) == last_p {
                last_p
            } else {
                Provenance::null()
            }
        }
    }

    pub open spec fn byte(self) -> u8
        recommends
            self is Init,
    {
        self->0
    }

    pub open spec fn provenance(self) -> Option<Provenance> {
        match self {
            AbstractByte::Init(_, p) => p,
            _ => None,
        }
    }

    pub open spec fn provenance_or_null(self) -> Provenance {
        match self.provenance() {
            Some(p) => p,
            _ => Provenance::null(),
        }
    }
}

pub trait Encoding where Self: Sized {
    /// Returns the abstract encoding of the given value.
    spec fn encode(value: Self) -> Seq<AbstractByte>;

    /// Returns Some(v) if the given bytes can be decoded into the value v, else None.
    spec fn decode(bytes: Seq<AbstractByte>) -> Option<Self>;

    /// Required properties for encoding (sanity check for any implementation of this trait)
    proof fn encoding_props()
        ensures
            forall|v| #[trigger] Self::encode(v).len() == size_of::<Self>(),
            forall|v| Self::decode(#[trigger] Self::encode(v)) == Some(v),
    ;
}

/* bool */

impl Encoding for bool {
    open spec fn encode(value: Self) -> Seq<AbstractByte> {
        seq![
            AbstractByte::Init(
                if value {
                    1
                } else {
                    0
                },
                None,
            ),
        ]
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
    open spec fn encode(value: Self) -> Seq<AbstractByte> {
        seq![AbstractByte::Init(value, None)]
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

/* unsigned integers */

// We utilize the EndianNat type to transform an unsigned int to its byte representation.
/// Convert the given `EndianNat`` representation to `AbtractByte`s with the given provenance.
pub open spec fn endian_to_bytes(endian: EndianNat<u8>, prov: Option<Provenance>) -> Seq<
    AbstractByte,
> {
    endian.digits.map_values(|e| AbstractByte::Init(e as u8, prov))
}

/// Convert the given `AbstractByte` representation to its `EndianNat` representation (provenance is ignored).
pub open spec fn bytes_to_endian(bytes: Seq<AbstractByte>) -> EndianNat<u8> {
    EndianNat::<u8>::new_default(bytes.map_values(|b: AbstractByte| b.byte() as int))
}

/// Ensures that converting from an `EndianNat` representation to `AbtractByte`s and back results in the same `EndianNat`.
pub broadcast proof fn endian_to_bytes_to_endian(n: nat, len: nat, prov: Option<Provenance>)
    requires
        pow(u8::base() as int, len) > n,
    ensures
        #![trigger endian_to_bytes(EndianNat::<u8>::from_nat_with_len(n, len), prov)]
        ({
            let endian = EndianNat::<u8>::from_nat_with_len(n, len);
            let bytes = endian_to_bytes(endian, prov);
            &&& bytes_to_endian(bytes) == endian
            &&& endian.len() == bytes.len() == len
            &&& AbstractByte::all_init(bytes)
            &&& endian.wf()
        }),
{
    broadcast use
        EndianNat::from_nat_len,
        EndianNat::from_nat_with_len_wf,
        EndianNat::from_nat_with_len_endianness,
    ;

    let endian = EndianNat::<u8>::from_nat_with_len(n, len);
    let bytes = endian_to_bytes(endian, prov);
    assert(endian.wf());
    assert(endian.len() == len);
    assert(endian.len() == bytes.len());
}

/// Ensures that all bytes in the resulting `AbstractByte` representation indeed have the given provenance.
pub broadcast proof fn endian_to_bytes_shared_provenance(endian: EndianNat<u8>, prov: Provenance)
    requires
        endian.len() > 0,
    ensures
        #[trigger] AbstractByte::shared_provenance(endian_to_bytes(endian, Some(prov))) == prov,
    decreases endian.len(),
{
    if endian.len() == 1 {
    } else {
        let bytes = endian_to_bytes(endian, Some(prov));
        assert(bytes.drop_last() =~= endian_to_bytes(endian.drop_last(), Some(prov)));
        endian_to_bytes_shared_provenance(endian.drop_last(), prov);
    }
}

/// Ensures that all bytes in the resulting `AbstractByte` representation have no provenance.
pub broadcast proof fn endian_to_bytes_shared_provenance_none(endian: EndianNat<u8>)
    requires
        endian.len() > 0,
    ensures
        #[trigger] AbstractByte::shared_provenance(endian_to_bytes(endian, None))
            == Provenance::null(),
    decreases endian.len(),
{
    if endian.len() == 1 {
    } else {
        let bytes = endian_to_bytes(endian, None);
        assert(bytes.drop_last() =~= endian_to_bytes(endian.drop_last(), None));
        endian_to_bytes_shared_provenance_none(endian.drop_last());
    }
}

/* usize */

impl Encoding for usize {
    open spec fn encode(value: Self) -> Seq<AbstractByte> {
        endian_to_bytes(
            EndianNat::<u8>::from_nat_with_len(value as nat, size_of::<Self>()),
            // integer types have no provenance
            None,
        )
    }

    open spec fn decode(bytes: Seq<AbstractByte>) -> Option<Self> {
        // fail if any byte is uninitalized or if the byte sequence is not the necessary length
        if bytes.len() == size_of::<Self>() && AbstractByte::all_init(bytes) {
            let endian = bytes_to_endian(bytes);
            if endian.wf() {
                Some(endian.to_nat() as Self)
            } else {
                None
            }
        } else {
            None
        }
    }

    proof fn encoding_props() {
        broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

        usize_max_bounds();
    }
}

pub proof fn encode_usize(v: usize)
    ensures
        ({
            let bytes = usize::encode(v);
            &&& bytes.len() == size_of::<usize>()
            &&& AbstractByte::all_init(bytes)
            &&& AbstractByte::shared_provenance(bytes) == Provenance::null()
            &&& bytes_to_endian(bytes).to_nat() as usize == v
            &&& bytes_to_endian(bytes).wf()
        }),
{
    broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

    usize_max_bounds();
}

impl<T> Encoding for *mut T {
    open spec fn encode(value: Self) -> Seq<AbstractByte> {
        endian_to_bytes(
            EndianNat::<u8>::from_nat_with_len(value as nat, size_of::<Self>()),
            // the abstract encoding preserves the provenance from this pointer
            Some(value@.provenance),
        )
    }

    open spec fn decode(bytes: Seq<AbstractByte>) -> Option<Self> {
        // fail if any byte is uninitalized or if the byte sequence is not the necessary length
        if bytes.len() == size_of::<Self>() && AbstractByte::all_init(bytes) {
            let endian = bytes_to_endian(bytes);
            // if all bytes in the sequence have the same provenance, then this should be preserved in the decoding.
            // otherwise, the resulting pointer should have no provenance
            let prov = AbstractByte::shared_provenance(bytes);
            if endian.wf() {
                Some(
                    ptr_mut_from_data(
                        PtrData::<T> {
                            addr: endian.to_nat() as usize,
                            provenance: prov,
                            metadata: (),
                        },
                    ),
                )
            } else {
                None
            }
        } else {
            None
        }
    }

    proof fn encoding_props() {
        broadcast use
            EndianNat::from_nat_to_nat,
            endian_to_bytes_to_endian,
            endian_to_bytes_shared_provenance,
        ;

        usize_max_bounds();
    }
}

// Helpers for specific transmute ops
pub broadcast proof fn transmute_usize_mut_ptr<T>(src: usize)
    ensures
        #![trigger <*mut T as Encoding>::decode(usize::encode(src))]
        <*mut T as Encoding>::decode(usize::encode(src)).is_some(),
        ({
            let dst = <*mut T as Encoding>::decode(usize::encode(src)).unwrap();
            &&& dst@.addr == src
            &&& dst@.provenance == Provenance::null()
        }),
{
    encode_usize(src);
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
