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

pub trait Encoding<T: Sized> {
    /// Can 'value' be encoded to the given bytes?
    spec fn encode(value: T, bytes: Seq<AbstractByte>) -> bool;

    /// Can the bytes be decoded to the given value?
    spec fn decode(bytes: Seq<AbstractByte>, value: T) -> bool;

    // Required properties for encoding (sanity check for any implementation of this trait)
    /// Any encoding should match the size of this type.
    broadcast proof fn encoding_size(v: T, b: Seq<AbstractByte>)
        requires
            #[trigger] Self::encode(v, b),
        ensures
            b.len() == size_of::<T>(),
    ;

    /// Every value should have at least one encoding.
    proof fn encoding_exists(v: T) -> (b: Seq<AbstractByte>)
        ensures
            Self::encode(v, b),
    ;

    /// Any byte encoding should be able to be decoded back to the same value.
    broadcast proof fn encoding_invertible(v: T, b: Seq<AbstractByte>)
        requires
            #[trigger] Self::encode(v, b),
        ensures
            #[trigger] Self::decode(b, v),
    ;
}

/* bool */

pub struct EncodingBool {}

impl Encoding<bool> for EncodingBool {
    open spec fn encode(value: bool, bytes: Seq<AbstractByte>) -> bool {
        bytes == seq![
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

    open spec fn decode(bytes: Seq<AbstractByte>, value: bool) -> bool {
        &&& bytes.len() == 1
        &&& match bytes.first() {
            AbstractByte::Init(0, _) => !value,
            AbstractByte::Init(1, _) => value,
            _ => false,
        }
    }

    proof fn encoding_size(v: bool, b: Seq<AbstractByte>) {
    }

    proof fn encoding_exists(v: bool) -> (b: Seq<AbstractByte>) {
        seq![
            AbstractByte::Init(
                if v {
                    1
                } else {
                    0
                },
                None,
            ),
        ]
    }

    proof fn encoding_invertible(v: bool, b: Seq<AbstractByte>) {
    }
}

/* unsigned integers */

/* u8 */

pub struct EncodingU8 {}

impl Encoding<u8> for EncodingU8 {
    open spec fn encode(value: u8, bytes: Seq<AbstractByte>) -> bool {
        bytes == seq![AbstractByte::Init(value, None)]
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: u8) -> bool {
        &&& bytes.len() == 1
        &&& match bytes.first() {
            AbstractByte::Init(v, _) => v == value,
            _ => false,
        }
    }

    proof fn encoding_size(v: u8, b: Seq<AbstractByte>) {
    }

    proof fn encoding_exists(v: u8) -> (b: Seq<AbstractByte>) {
        seq![AbstractByte::Init(v, None)]
    }

    proof fn encoding_invertible(v: u8, b: Seq<AbstractByte>) {
    }
}

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

pub struct EncodingUsize {}

impl Encoding<usize> for EncodingUsize {
    open spec fn encode(value: usize, bytes: Seq<AbstractByte>) -> bool {
        bytes == endian_to_bytes(
            EndianNat::<u8>::from_nat_with_len(value as nat, size_of::<usize>()),
            // integer types have no provenance
            None,
        )
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: usize) -> bool {
        // fail if any byte is uninitalized or if the byte sequence is not the necessary length
        &&& bytes.len() == size_of::<usize>()
        &&& AbstractByte::all_init(bytes)
        &&& {
            let endian = bytes_to_endian(bytes);
            &&& endian.wf()
            &&& (endian.to_nat() as usize) == value
        }
    }

    proof fn encoding_size(v: usize, b: Seq<AbstractByte>) {
        broadcast use endian_to_bytes_to_endian;

        usize_max_bounds();
    }

    proof fn encoding_exists(v: usize) -> (b: Seq<AbstractByte>) {
        endian_to_bytes(EndianNat::<u8>::from_nat_with_len(v as nat, size_of::<usize>()), None)
    }

    proof fn encoding_invertible(v: usize, b: Seq<AbstractByte>) {
        broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

        usize_max_bounds();
    }
}

pub broadcast proof fn usize_encode(v: usize, bytes: Seq<AbstractByte>)
    requires
        #[trigger] EncodingUsize::encode(v, bytes),
    ensures
        bytes.len() == size_of::<usize>(),
        AbstractByte::all_init(bytes),
        AbstractByte::shared_provenance(bytes) == Provenance::null(),
        bytes_to_endian(bytes).to_nat() as usize == v,
        bytes_to_endian(bytes).wf(),
{
    broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

    usize_max_bounds();
}

/* Raw pointers */

pub struct EncodingMutPtr {}

impl<T> Encoding<*mut T> for EncodingMutPtr {
    open spec fn encode(value: *mut T, bytes: Seq<AbstractByte>) -> bool {
        bytes == endian_to_bytes(
            EndianNat::<u8>::from_nat_with_len(value as nat, size_of::<*mut T>()),
            // the abstract encoding preserves the provenance from this pointer
            Some(value@.provenance),
        )
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: *mut T) -> bool {
        // fail if any byte is uninitalized or if the byte sequence is not the necessary length
        &&& bytes.len() == size_of::<*mut T>()
        &&& AbstractByte::all_init(bytes)
        &&& {
            let endian = bytes_to_endian(bytes);
            // if all bytes in the sequence have the same provenance, then this should be preserved in the decoding.
            // otherwise, the resulting pointer should have no provenance
            let prov = AbstractByte::shared_provenance(bytes);
            &&& endian.wf()
            &&& value@.addr == endian.to_nat() as usize
            &&& value@.provenance == prov
        }
    }

    proof fn encoding_size(v: *mut T, b: Seq<AbstractByte>) {
        broadcast use endian_to_bytes_to_endian;

        usize_max_bounds();
    }

    proof fn encoding_exists(v: *mut T) -> (b: Seq<AbstractByte>) {
        endian_to_bytes(
            EndianNat::<u8>::from_nat_with_len(v as nat, size_of::<*mut T>()),
            Some(v@.provenance),
        )
    }

    proof fn encoding_invertible(v: *mut T, b: Seq<AbstractByte>) {
        broadcast use
            EndianNat::from_nat_to_nat,
            endian_to_bytes_to_endian,
            endian_to_bytes_shared_provenance,
        ;

        usize_max_bounds();
    }
}

// Helpers for specific transmute ops
pub proof fn transmute_usize_mut_ptr<T>(src: usize) -> (dst: *mut T)
    ensures
        forall|bytes| #[trigger]
            EncodingUsize::encode(src, bytes) ==> EncodingMutPtr::decode(bytes, dst),
        dst@.addr == src,
        dst@.provenance == Provenance::null(),
{
    broadcast use usize_encode;

    ptr_mut_from_data(PtrData { addr: src, provenance: Provenance::null(), metadata: () })
}

// can't have T: ?Sized currently, because value and is_init are not implemented generically for DSTs
impl<T> PointsTo<T> {
    // TODO: version for nondeterministic targets
    pub axiom fn transmute_shared<'a, U, EncodingT: Encoding<T>, EncodingU: Encoding<U>>(
        tracked &'a self,
        tracked target: U,
    ) -> (tracked ret: &'a PointsTo<U>)
        requires
            self.is_init(),
            forall|bytes|
                #![trigger EncodingT::encode(self.value(), bytes)]
                #![trigger EncodingU::decode(bytes, target)]
                EncodingT::encode(self.value(), bytes) ==> EncodingU::decode(bytes, target),
        ensures
            ret.is_init(),
            ret.value() == target,
            ret.ptr()@.addr == self.ptr()@.addr,
            ret.ptr()@.provenance == self.ptr()@.provenance,
    ;
}

/* Dynamically Sized Types */

pub trait EncodingNotSized<T: ?Sized> {
    /// Can 'value' be encoded to the given bytes?
    spec fn encode(value: &T, bytes: Seq<AbstractByte>) -> bool;

    /// Can the given bytes always be decoded to the given value?
    spec fn decode(bytes: Seq<AbstractByte>, value: &T) -> bool;

    // Required properties for encoding (sanity check for any implementation of this trait)
    /// Any encoding should match the size of the corresponding value.
    broadcast proof fn encoding_size(v: &T, b: Seq<AbstractByte>)
        requires
            #[trigger] Self::encode(v, b),
        ensures
            b.len() == spec_size_of_val::<T>(v),
    ;

    /// Every value should have at least one encoding.
    proof fn encoding_exists(v: &T) -> (b: Seq<AbstractByte>)
        ensures
            Self::encode(v, b),
    ;

    /// Any byte encoding should be able to be decoded back to the same value.
    broadcast proof fn encoding_invertible(v: &T, b: Seq<AbstractByte>)
        requires
            #[trigger] Self::encode(v, b),
        ensures
            #[trigger] Self::decode(b, v),
    ;
}

/* [u8] */

pub struct EncodingU8Slice {}

impl EncodingNotSized<[u8]> for EncodingU8Slice {
    // todo - should slices be encoded with provenance?
    // I'm not sure if we have a way of reasoning about provenance without the PointsTo...
    open spec fn encode(value: &[u8], bytes: Seq<AbstractByte>) -> bool {
        bytes == value@.map_values(|e| AbstractByte::Init(e, None))
    }

    // todo - should provenance be encoded?
    open spec fn decode(bytes: Seq<AbstractByte>, value: &[u8]) -> bool {
        value@ == bytes.map_values(|b: AbstractByte| b.byte())
    }

    proof fn encoding_size(v: &[u8], b: Seq<AbstractByte>) {
    }

    proof fn encoding_exists(v: &[u8]) -> (b: Seq<AbstractByte>) {
        v@.map_values(|e| AbstractByte::Init(e, None))
    }

    proof fn encoding_invertible(v: &[u8], b: Seq<AbstractByte>) {
        assert(v@ =~= b.map_values(|bt: AbstractByte| bt.byte()));
    }
}

/*
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
*/

impl PointsTo<str> {
    pub axiom fn transmute_shared<
        'a,
        EncodingStr: EncodingNotSized<str>,
        EncodingU8Slice: EncodingNotSized<[u8]>,
    >(tracked &'a self, target: &[u8]) -> (tracked ret: &'a PointsTo<[u8]>)
        requires
            self.is_init(),
            forall|bytes|
                #![trigger EncodingStr::encode(self.value(), bytes)]
                #![trigger EncodingU8Slice::decode(bytes, target)]
                EncodingStr::encode(self.value(), bytes) ==> EncodingU8Slice::decode(bytes, target),
        ensures
            ret.is_init(),
            ret.value() == target@,
            ret.phy() == target,
            ret.ptr()@.addr == self.ptr()@.addr,
            ret.ptr()@.provenance == self.ptr()@.provenance,
    ;
}

} // verus!
