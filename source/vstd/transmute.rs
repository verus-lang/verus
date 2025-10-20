#![allow(unused_imports)]

use super::arithmetic::power::*;
use super::arithmetic::power2::*;
use super::endian::*;
use super::layout::*;
use super::prelude::*;
use super::primitive_int::*;
use super::raw_ptr::*;
use super::seq::*;
use crate::vstd::group_vstd_default;

verus! {

broadcast use {group_layout_axioms, group_vstd_default};
// https://github.com/minirust/minirust/blob/master/spec/mem/interface.md#abstract-bytes
// https://github.com/minirust/minirust/blob/master/spec/lang/representation.md

/// Memory is represented as a sequence of abstract bytes.
/// Each byte is uninitialized or initialized.
/// An initialized byte may optionally have a provenance.
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

/// This trait defines an `AbstractByte` encoding over the given type `T`.
/// This definition enables reuse of the same underlying representation
/// across many concrete types. For example, enums can use the same representation as
/// a primitive type through the use of the `#[repr]` attribute.
/// See: https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr
pub trait TypeRepresentation<T> {
    /// Can 'value' be encoded to the given bytes?
    spec fn encode(value: T, bytes: Seq<AbstractByte>) -> bool;

    /// Can the bytes be decoded to the given value?
    spec fn decode(bytes: Seq<AbstractByte>, value: T) -> bool;

    // Required properties for a valid encoding.
    /// Any encoding should match the size of this type.
    broadcast proof fn encoding_size(v: T, b: Seq<AbstractByte>)
        requires
            #[trigger] Self::encode(v, b),
        ensures
            b.len() == size_of::<T>(),
    ;

    /// Every value should have at least one encoding.
    proof fn encoding_exists(tracked v: T) -> (b: Seq<AbstractByte>)
        ensures
            Self::encode(v, b),
    ;

    /// Any encoding should be able to be decoded back to the same value.
    broadcast proof fn encoding_invertible(v: T, b: Seq<AbstractByte>)
        requires
            #[trigger] Self::encode(v, b),
        ensures
            #[trigger] Self::decode(b, v),
    ;
}

/* bool */

pub struct BoolRepresentation {}

impl TypeRepresentation<bool> for BoolRepresentation {
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

    proof fn encoding_exists(tracked v: bool) -> (b: Seq<AbstractByte>) {
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

pub struct U8Representation {}

impl TypeRepresentation<u8> for U8Representation {
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

    proof fn encoding_exists(tracked v: u8) -> (b: Seq<AbstractByte>) {
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

/* u16 */

pub struct U16Representation {}

impl TypeRepresentation<u16> for U16Representation {
    open spec fn encode(value: u16, bytes: Seq<AbstractByte>) -> bool {
        bytes == endian_to_bytes(
            EndianNat::<u8>::from_nat_with_len(value as nat, size_of::<u16>()),
            // integer types have no provenance
            None,
        )
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: u16) -> bool {
        // fail if any byte is uninitalized or if the byte sequence is not the necessary length
        &&& bytes.len() == size_of::<u16>()
        &&& AbstractByte::all_init(bytes)
        &&& {
            let endian = bytes_to_endian(bytes);
            &&& endian.wf()
            &&& (endian.to_nat() as u16) == value
        }
    }

    proof fn encoding_size(v: u16, b: Seq<AbstractByte>) {
        broadcast use endian_to_bytes_to_endian;

        unsigned_int_max_bounds();
    }

    proof fn encoding_exists(tracked v: u16) -> (b: Seq<AbstractByte>) {
        endian_to_bytes(EndianNat::<u8>::from_nat_with_len(v as nat, size_of::<u16>()), None)
    }

    proof fn encoding_invertible(v: u16, b: Seq<AbstractByte>) {
        broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

        unsigned_int_max_bounds();
    }
}

/* u32 */

pub struct U32Representation {}

impl TypeRepresentation<u32> for U32Representation {
    open spec fn encode(value: u32, bytes: Seq<AbstractByte>) -> bool {
        bytes == endian_to_bytes(
            EndianNat::<u8>::from_nat_with_len(value as nat, size_of::<u32>()),
            // integer types have no provenance
            None,
        )
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: u32) -> bool {
        // fail if any byte is uninitalized or if the byte sequence is not the necessary length
        &&& bytes.len() == size_of::<u32>()
        &&& AbstractByte::all_init(bytes)
        &&& {
            let endian = bytes_to_endian(bytes);
            &&& endian.wf()
            &&& (endian.to_nat() as u32) == value
        }
    }

    proof fn encoding_size(v: u32, b: Seq<AbstractByte>) {
        broadcast use endian_to_bytes_to_endian;

        unsigned_int_max_bounds();
    }

    proof fn encoding_exists(tracked v: u32) -> (b: Seq<AbstractByte>) {
        endian_to_bytes(EndianNat::<u8>::from_nat_with_len(v as nat, size_of::<u32>()), None)
    }

    proof fn encoding_invertible(v: u32, b: Seq<AbstractByte>) {
        broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

        unsigned_int_max_bounds();
    }
}

/* u64 */

pub struct U64Representation {}

impl TypeRepresentation<u64> for U64Representation {
    open spec fn encode(value: u64, bytes: Seq<AbstractByte>) -> bool {
        bytes == endian_to_bytes(
            EndianNat::<u8>::from_nat_with_len(value as nat, size_of::<u64>()),
            // integer types have no provenance
            None,
        )
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: u64) -> bool {
        // fail if any byte is uninitalized or if the byte sequence is not the necessary length
        &&& bytes.len() == size_of::<u64>()
        &&& AbstractByte::all_init(bytes)
        &&& {
            let endian = bytes_to_endian(bytes);
            &&& endian.wf()
            &&& (endian.to_nat() as u64) == value
        }
    }

    proof fn encoding_size(v: u64, b: Seq<AbstractByte>) {
        broadcast use endian_to_bytes_to_endian;

        unsigned_int_max_bounds();
    }

    proof fn encoding_exists(tracked v: u64) -> (b: Seq<AbstractByte>) {
        endian_to_bytes(EndianNat::<u8>::from_nat_with_len(v as nat, size_of::<u64>()), None)
    }

    proof fn encoding_invertible(v: u64, b: Seq<AbstractByte>) {
        broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

        unsigned_int_max_bounds();
    }
}

/* usize */

pub struct UsizeRepresentation {}

impl TypeRepresentation<usize> for UsizeRepresentation {
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

        unsigned_int_max_bounds();
    }

    proof fn encoding_exists(tracked v: usize) -> (b: Seq<AbstractByte>) {
        endian_to_bytes(EndianNat::<u8>::from_nat_with_len(v as nat, size_of::<usize>()), None)
    }

    proof fn encoding_invertible(v: usize, b: Seq<AbstractByte>) {
        broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

        unsigned_int_max_bounds();
    }
}

/* Raw pointers */

/// This raw pointer representation is shared across *const T and *mut T because they have the same representation.
/// The below encoding works for types `T` that are both sized and unsized (i.e. DSTs).
/// The "prefix": the first `size_of::<usize>()` bytes of the encoding will always encode the pointer's address and per-byte provenance.
/// The "suffix": the next `size_of::<*mut T>() - size_of::<usize>()` bytes will have contents that are unspecified.
/// - For `T: Sized`, `size_of::<*mut T>() = size_of::<usize>()`, and so the suffix is a sequence of length 0.
/// - For `T` unsized, the Rust language reference only specifies that `size_of::<*mut T>() >= size_of::<usize>()`,
/// so this encoding allows the byte sequence to take the necessary (unspecified) length.
/// ([Reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer))
pub struct RawPtrRepresentation {}

impl<T: ?Sized> TypeRepresentation<*mut T> for RawPtrRepresentation {
    open spec fn encode(value: *mut T, bytes: Seq<AbstractByte>) -> bool {
        let prefix = bytes.subrange(0, size_of::<usize>() as int);
        &&& bytes.len() == size_of::<*mut T>()
        &&& prefix == endian_to_bytes(
            EndianNat::<u8>::from_nat_with_len(value@.addr as nat, size_of::<usize>()),
            // the abstract encoding preserves the provenance from this pointer
            Some(value@.provenance),
        )
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: *mut T) -> bool {
        let prefix = bytes.subrange(0, size_of::<usize>() as int);
        // fail if any byte is uninitalized or if the byte sequence is not the necessary length
        &&& bytes.len() == size_of::<*mut T>()
        &&& AbstractByte::all_init(prefix)
        &&& {
            let endian = bytes_to_endian(prefix);
            // if all bytes in the sequence have the same provenance, then this should be preserved in the decoding.
            // otherwise, the resulting pointer should have no provenance
            let prov = AbstractByte::shared_provenance(prefix);
            &&& endian.wf()
            &&& value@.addr == endian.to_nat() as usize
            &&& value@.provenance == prov
        }
    }

    proof fn encoding_size(v: *mut T, b: Seq<AbstractByte>) {
    }

    proof fn encoding_exists(tracked v: *mut T) -> (b: Seq<AbstractByte>) {
        broadcast use endian_to_bytes_to_endian;

        unsigned_int_max_bounds();
        let prefix = endian_to_bytes(
            EndianNat::<u8>::from_nat_with_len(v@.addr as nat, size_of::<usize>()),
            Some(v@.provenance),
        );
        let suffix = Seq::<AbstractByte>::new(
            (size_of::<*mut T>() - size_of::<usize>()) as nat,
            |i| AbstractByte::Uninit,
        );
        let b = prefix.add(suffix);
        assert(b.subrange(0, size_of::<usize>() as int) =~= prefix);
        assert(b.len() == size_of::<*mut T>());
        b
    }

    proof fn encoding_invertible(v: *mut T, b: Seq<AbstractByte>) {
        broadcast use
            EndianNat::from_nat_to_nat,
            endian_to_bytes_to_endian,
            endian_to_bytes_shared_provenance,
        ;

        unsigned_int_max_bounds();
    }
}

/// Represents whether a valid encoding has been defined for this type.
pub uninterp spec fn valid_encoding<T>() -> bool where T: Sized;

/// This trait is defines the given type's `AbstractByte` encoding.
pub trait AbstractEncoding where Self: Sized {
    /// Can 'value' be encoded to the given bytes?
    spec fn encode(value: Self, bytes: Seq<AbstractByte>) -> bool;

    /// Can the bytes be decoded to the given value?
    spec fn decode(bytes: Seq<AbstractByte>, value: Self) -> bool;

    // Required properties for a valid encoding.
    /// Any encoding should match the size of this type.
    broadcast proof fn encoding_size(v: Self, b: Seq<AbstractByte>)
        requires
            #[trigger] Self::encode(v, b),
        ensures
            b.len() == size_of::<Self>(),
    ;

    /// Every value should have at least one encoding.
    proof fn encoding_exists(tracked v: Self) -> (b: Seq<AbstractByte>)
        ensures
            Self::encode(v, b),
    ;

    /// Any encoding should be able to be decoded back to the same value.
    broadcast proof fn encoding_invertible(v: Self, b: Seq<AbstractByte>)
        requires
            #[trigger] Self::encode(v, b),
        ensures
            #[trigger] Self::decode(b, v),
    ;

    /// This is a intended to be implemented as an axiom.
    /// It acts as a placeholder to remind us that this encoding is axiomatized -- that is,
    /// it is assumed to be faithful to Rust's actual representation of this type.
    proof fn valid_encoding()
        ensures
            valid_encoding::<Self>(),
    ;
}

// This macro can't yet handle generics, but it can be used to reduce repeated code in simple cases.
macro_rules! encoding_from_type_representation {
    ($(
        ($name:ty, $type_repr:ty, $spec_mod:tt);
    )+) => {$(
        verus! {
            impl AbstractEncoding for $name {
                $spec_mod spec fn encode(value: Self, bytes: Seq<AbstractByte>) -> bool {
                    $type_repr::encode(value, bytes)
                }

                $spec_mod spec fn decode(bytes: Seq<AbstractByte>, value: Self) -> bool {
                    $type_repr::decode(bytes, value)
                }

                proof fn encoding_size(v: Self, b: Seq<AbstractByte>) {
                    $type_repr::encoding_size(v, b);
                }

                proof fn encoding_exists(tracked v: Self) -> (b: Seq<AbstractByte>) {
                    $type_repr::encoding_exists(v)
                }

                proof fn encoding_invertible(v: Self, b: Seq<AbstractByte>) {
                    $type_repr::encoding_invertible(v, b);
                }

                axiom fn valid_encoding();
            }
        }
    )+};
}

pub(crate) use encoding_from_type_representation;

encoding_from_type_representation! {
    (bool, BoolRepresentation, open);
    (u8, U8Representation, open);
    (u16, U16Representation, open);
    (u32, U32Representation, open);
    (u64, U64Representation, open);
    (usize, UsizeRepresentation, open);
}

pub broadcast proof fn u16_encode(v: u16, bytes: Seq<AbstractByte>)
    requires
        #[trigger] u16::encode(v, bytes),
    ensures
        bytes.len() == size_of::<u16>(),
        AbstractByte::all_init(bytes),
        AbstractByte::shared_provenance(bytes) == Provenance::null(),
        bytes_to_endian(bytes).to_nat() as u16 == v,
        bytes_to_endian(bytes).wf(),
{
    broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

    unsigned_int_max_bounds();
}

pub broadcast proof fn u32_encode(v: u32, bytes: Seq<AbstractByte>)
    requires
        #[trigger] u32::encode(v, bytes),
    ensures
        bytes.len() == size_of::<u32>(),
        AbstractByte::all_init(bytes),
        AbstractByte::shared_provenance(bytes) == Provenance::null(),
        bytes_to_endian(bytes).to_nat() as u32 == v,
        bytes_to_endian(bytes).wf(),
{
    broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

    unsigned_int_max_bounds();
}

pub broadcast proof fn u64_encode(v: u64, bytes: Seq<AbstractByte>)
    requires
        #[trigger] u64::encode(v, bytes),
    ensures
        bytes.len() == size_of::<u64>(),
        AbstractByte::all_init(bytes),
        AbstractByte::shared_provenance(bytes) == Provenance::null(),
        bytes_to_endian(bytes).to_nat() as u64 == v,
        bytes_to_endian(bytes).wf(),
{
    broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

    unsigned_int_max_bounds();
}

pub broadcast proof fn usize_encode(v: usize, bytes: Seq<AbstractByte>)
    requires
        #[trigger] usize::encode(v, bytes),
    ensures
        bytes.len() == size_of::<usize>(),
        AbstractByte::all_init(bytes),
        AbstractByte::shared_provenance(bytes) == Provenance::null(),
        bytes_to_endian(bytes).to_nat() as usize == v,
        bytes_to_endian(bytes).wf(),
{
    broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

    unsigned_int_max_bounds();
}

impl<T: ?Sized> AbstractEncoding for *mut T {
    open spec fn encode(value: Self, bytes: Seq<AbstractByte>) -> bool {
        RawPtrRepresentation::encode(value, bytes)
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: Self) -> bool {
        RawPtrRepresentation::decode(bytes, value)
    }

    proof fn encoding_size(v: Self, b: Seq<AbstractByte>) {
        RawPtrRepresentation::encoding_size(v, b);
    }

    proof fn encoding_exists(tracked v: Self) -> (b: Seq<AbstractByte>) {
        RawPtrRepresentation::encoding_exists(v)
    }

    proof fn encoding_invertible(v: Self, b: Seq<AbstractByte>) {
        RawPtrRepresentation::encoding_invertible(v, b);
    }

    axiom fn valid_encoding();
}

pub broadcast proof fn mut_ptr_sized_encode<T: Sized>(v: *mut T, bytes: Seq<AbstractByte>)
    requires
        #[trigger] <*mut T as AbstractEncoding>::encode(v, bytes),
    ensures
        bytes.len() == size_of::<*mut T>(),
        bytes =~= bytes.subrange(0, size_of::<*mut T>() as int),
        AbstractByte::all_init(bytes),
        AbstractByte::shared_provenance(bytes) == v@.provenance,
        bytes_to_endian(bytes).to_nat() as usize == v@.addr,
        bytes_to_endian(bytes).wf(),
{
    broadcast use
        EndianNat::from_nat_to_nat,
        endian_to_bytes_to_endian,
        endian_to_bytes_shared_provenance,
    ;

    unsigned_int_max_bounds();
    let prefix = endian_to_bytes(
        EndianNat::<u8>::from_nat_with_len(v@.addr as nat, size_of::<usize>()),
        Some(v@.provenance),
    );
    assert(prefix =~= bytes);
}

pub broadcast proof fn mut_ptr_unsized_encode<T: ?Sized>(v: *mut T, bytes: Seq<AbstractByte>)
    requires
        #[trigger] <*mut T as AbstractEncoding>::encode(v, bytes),
    ensures
        ({
            let prefix = bytes.subrange(0, size_of::<usize>() as int);
            &&& bytes.len() == size_of::<*mut T>()
            &&& AbstractByte::all_init(prefix)
            &&& AbstractByte::shared_provenance(prefix) == v@.provenance
            &&& bytes_to_endian(prefix).to_nat() as usize == v@.addr
            &&& bytes_to_endian(prefix).wf()
        }),
{
    broadcast use
        EndianNat::from_nat_to_nat,
        endian_to_bytes_to_endian,
        endian_to_bytes_shared_provenance,
    ;

    unsigned_int_max_bounds();
    let prefix = endian_to_bytes(
        EndianNat::<u8>::from_nat_with_len(v@.addr as nat, size_of::<usize>()),
        Some(v@.provenance),
    );
    assert(prefix =~= bytes.subrange(0, size_of::<usize>() as int));
}

impl<T: ?Sized> AbstractEncoding for *const T {
    open spec fn encode(value: Self, bytes: Seq<AbstractByte>) -> bool {
        RawPtrRepresentation::encode(value as *mut T, bytes)
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: Self) -> bool {
        RawPtrRepresentation::decode(bytes, value as *mut T)
    }

    proof fn encoding_size(v: Self, b: Seq<AbstractByte>) {
        RawPtrRepresentation::encoding_size(v as *mut T, b);
    }

    proof fn encoding_exists(tracked v: Self) -> (b: Seq<AbstractByte>) {
        RawPtrRepresentation::encoding_exists(v as *mut T)
    }

    proof fn encoding_invertible(v: Self, b: Seq<AbstractByte>) {
        RawPtrRepresentation::encoding_invertible(v as *mut T, b);
    }

    axiom fn valid_encoding();
}

pub broadcast proof fn const_ptr_sized_encode<T: Sized>(v: *const T, bytes: Seq<AbstractByte>)
    requires
        #[trigger] <*const T as AbstractEncoding>::encode(v, bytes),
    ensures
        bytes.len() == size_of::<*const T>(),
        bytes =~= bytes.subrange(0, size_of::<*const T>() as int),
        AbstractByte::all_init(bytes),
        AbstractByte::shared_provenance(bytes) == v@.provenance,
        bytes_to_endian(bytes).to_nat() as usize == v@.addr,
        bytes_to_endian(bytes).wf(),
{
    broadcast use
        EndianNat::from_nat_to_nat,
        endian_to_bytes_to_endian,
        endian_to_bytes_shared_provenance,
    ;

    unsigned_int_max_bounds();
    let prefix = endian_to_bytes(
        EndianNat::<u8>::from_nat_with_len(v@.addr as nat, size_of::<usize>()),
        Some(v@.provenance),
    );
    assert(prefix =~= bytes);
}

pub broadcast proof fn const_ptr_unsized_encode<T: ?Sized>(v: *const T, bytes: Seq<AbstractByte>)
    requires
        #[trigger] <*const T as AbstractEncoding>::encode(v, bytes),
    ensures
        ({
            let prefix = bytes.subrange(0, size_of::<usize>() as int);
            &&& bytes.len() == size_of::<*const T>()
            &&& AbstractByte::all_init(prefix)
            &&& AbstractByte::shared_provenance(prefix) == v@.provenance
            &&& bytes_to_endian(prefix).to_nat() as usize == v@.addr
            &&& bytes_to_endian(prefix).wf()
        }),
{
    broadcast use
        EndianNat::from_nat_to_nat,
        endian_to_bytes_to_endian,
        endian_to_bytes_shared_provenance,
    ;

    unsigned_int_max_bounds();
    let prefix = endian_to_bytes(
        EndianNat::<u8>::from_nat_with_len(v@.addr as nat, size_of::<usize>()),
        Some(v@.provenance),
    );
    assert(prefix =~= bytes.subrange(0, size_of::<usize>() as int));
}

/* Composite types */

/* Primitive representations */

pub trait PrimitiveRepresentation<Primitive: AbstractEncoding + PrimitiveInt> where Self: Sized {
    spec fn to_primitive(v: Self) -> Primitive;

    proof fn to_primitive_tracked(tracked v: Self) -> (tracked p: Primitive)
        ensures
            p == Self::to_primitive(v),
    ;

    proof fn layout_of_primitive_repr()
        ensures
            crate::vstd::layout::size_of::<Self>() == crate::vstd::layout::size_of::<Primitive>(),
            crate::vstd::layout::align_of::<Self>() == crate::vstd::layout::align_of::<Primitive>(),
    ;
}

pub struct PrimitiveRepresentationEncoding<
    Primitive: AbstractEncoding + PrimitiveInt,
    T: PrimitiveRepresentation<Primitive>,
> {
    _t: T,
    _primitive: Primitive,
}

impl<
    Primitive: AbstractEncoding + PrimitiveInt,
    T: PrimitiveRepresentation<Primitive>,
> TypeRepresentation<T> for PrimitiveRepresentationEncoding<Primitive, T> {
    open spec fn encode(value: T, bytes: Seq<AbstractByte>) -> bool {
        Primitive::encode(T::to_primitive(value), bytes)
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: T) -> bool {
        Primitive::decode(bytes, T::to_primitive(value))
    }

    proof fn encoding_size(v: T, b: Seq<AbstractByte>) {
        T::layout_of_primitive_repr();
        Primitive::encoding_size(T::to_primitive(v), b);
    }

    proof fn encoding_exists(tracked v: T) -> (b: Seq<AbstractByte>) {
        Primitive::encoding_exists(T::to_primitive_tracked(v))
    }

    proof fn encoding_invertible(v: T, b: Seq<AbstractByte>) {
        Primitive::encoding_invertible(T::to_primitive(v), b);
    }
}

/* Transparent representations */

pub trait TransparentRepresentation<Inner: AbstractEncoding> where Self: Sized {
    spec fn to_inner(v: Self) -> Inner;

    proof fn to_inner_tracked(tracked v: Self) -> (tracked i: Inner)
        ensures
            i == Self::to_inner(v),
    ;

    proof fn layout_of_transparent_repr()
        ensures
            crate::vstd::layout::size_of::<Self>() == crate::vstd::layout::size_of::<Inner>(),
            crate::vstd::layout::align_of::<Self>() == crate::vstd::layout::align_of::<Inner>(),
    ;
}

pub struct TransparentRepresentationEncoding<
    Inner: AbstractEncoding,
    T: TransparentRepresentation<Inner>,
> {
    _t: T,
    _inner: Inner,
}

impl<Inner: AbstractEncoding, T: TransparentRepresentation<Inner>> TypeRepresentation<
    T,
> for TransparentRepresentationEncoding<Inner, T> {
    open spec fn encode(value: T, bytes: Seq<AbstractByte>) -> bool {
        Inner::encode(T::to_inner(value), bytes)
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: T) -> bool {
        Inner::decode(bytes, T::to_inner(value))
    }

    proof fn encoding_size(v: T, b: Seq<AbstractByte>) {
        T::layout_of_transparent_repr();
        Inner::encoding_size(T::to_inner(v), b);
    }

    proof fn encoding_exists(tracked v: T) -> (b: Seq<AbstractByte>) {
        Inner::encoding_exists(T::to_inner_tracked(v))
    }

    proof fn encoding_invertible(v: T, b: Seq<AbstractByte>) {
        Inner::encoding_invertible(T::to_inner(v), b);
    }
}

/* Scalar ranges */

/// Imposes a scalar range restriction on an existing representation.
pub trait ScalarRangeRepresentation<Repr: TypeRepresentation<Self>> where Self: Sized {
    spec fn min() -> nat;

    spec fn max() -> nat;

    spec fn to_nat(v: Self) -> nat;

    proof fn valid_scalar_range_repr(tracked v: &Self)
        ensures
            Self::min() <= Self::to_nat(*v) <= Self::max(),
    ;
}

pub struct ScalarRangeRepresentationEncoding<
    Repr: TypeRepresentation<T>,
    T: ScalarRangeRepresentation<Repr>,
> {
    _t: T,
    _repr: Repr,
}

impl<Repr: TypeRepresentation<T>, T: ScalarRangeRepresentation<Repr>> TypeRepresentation<
    T,
> for ScalarRangeRepresentationEncoding<Repr, T> {
    open spec fn encode(value: T, bytes: Seq<AbstractByte>) -> bool {
        &&& Repr::encode(value, bytes)
        &&& T::min() <= T::to_nat(value) <= T::max()
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: T) -> bool {
        &&& Repr::decode(bytes, value)
        &&& T::min() <= T::to_nat(value) <= T::max()
    }

    proof fn encoding_size(v: T, b: Seq<AbstractByte>) {
        Repr::encoding_size(v, b);
    }

    proof fn encoding_exists(tracked v: T) -> (b: Seq<AbstractByte>) {
        T::valid_scalar_range_repr(&v);
        Repr::encoding_exists(v)
    }

    proof fn encoding_invertible(v: T, b: Seq<AbstractByte>) {
        Repr::encoding_invertible(v, b);
    }
}

/*  Helpers for specific transmute ops */

pub proof fn transmute_usize_mut_ptr<T: Sized>(src: usize) -> (dst: *mut T)
    ensures
        forall|bytes| #[trigger]
            usize::encode(src, bytes) ==> <*mut T as AbstractEncoding>::decode(bytes, dst),
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

// can't have T: ?Sized currently, because value and is_init are not implemented generically for DSTs
impl<T: AbstractEncoding> PointsTo<T> {
    // TODO: version for nondeterministic targets
    pub axiom fn transmute_shared<'a, U: AbstractEncoding>(
        tracked &'a self,
        tracked target: U,
    ) -> (tracked ret: &'a PointsTo<U>)
        requires
            self.is_init(),
            forall|bytes|
                #![trigger T::encode(self.value(), bytes)]
                #![trigger U::decode(bytes, target)]
                T::encode(self.value(), bytes) ==> U::decode(bytes, target),
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
