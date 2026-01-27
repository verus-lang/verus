//! This module defines (i.e., axiomatizes) the Rust abstract machine's representation for primitive types (integers, boolean, raw pointers),
//! as well as encodings for structs and enums derived from these primitive types.
//!
//! The uninterpreted functions `abs_encode`, `abs_decode`, and `can_be_encoded` define the encoding, decoding, and validity of transumute operations for a given type.
//! The abstract representation is encoded on a `Seq<AbstractByte>`, which encodes byte values as well as an optional `Provenance` for initialized memory.
//! Note that these functions are defined as relations between values and byte sequences, meaning that some byte sequences can be decoded to
//! multiple possible values (this is done to account for ghost state, which is not encoded in the abstract representation.)
//! These relations are unspecified for a given type unless they are explicitly implemented (see next paragraph).
//!
//! The `AbstractByteRepresentation` trait is implemented on a given type in order to add axioms for `abs_encode`, `abs_decode`, and `can_be_encoded` for that type.
//! The trait is used to ensure that the encoding axioms satisfy certain validity properties, e.g. that the resulting byte sequence is the correct length for the value/type,
//! and that a value's encoding can be decoded back to the same value (see: https://github.com/minirust/minirust/blob/master/spec/lang/representation.md#generic-properties).
//! `AbstractByteRepresentation` is implemented here for primitive integers (e.g., `u8`, `isize`), `bool`, `()`, and raw pointers.
//! `AbstractByteRepresentationUnsized` is the version of this trait for unsized types.
//!
//! The `PrimitiveRepresentation`, `TransparentRepresentation`, and `ScalarRangeRepresentation` traits are used to help
//! implement `AbstractByteRepresentation` for enums or structs with primitive, transparent, or scalar range representations.
//! (See: https://doc.rust-lang.org/reference/type-layout.html for more about primitive and transparent representations.
//! For scalar range representations, see the non-zero niche types for an example: https://doc.rust-lang.org/1.88.0/src/core/num/niche_types.rs.html.)
//!
//! The `AbstractByteEncoding` trait is used to make intermediate or shared definitions about encodings to byte sequences.
//! It is essentially the same as `AbstractByteRepresentation`, except that it does not include axioms tying the definitions to `abs_encode`, `abs_decode`, and `can_be_encoded`.
//! This is useful for when many types may share the same underlying byte-level representation, e.g. zero-sized types or `*const` and `*mut` pointers.
//! The representation is defined once on a `AbstractByteEncoding`, and then `AbstractByteRepresentation` is derived from the `AbstractByteEncoding`
//! for each of the relevant types (see: the `encoding_from_type_representation!` macro).
//! In other words, `AbstractByteRepresentation` defines *the* representation for a given type, whereas `AbstractByteEncoding` is a carrier for
//! potentially shared definitions.
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
use crate::vstd::group_vstd_default;

verus! {

// https://github.com/minirust/minirust/blob/master/spec/mem/interface.md#abstract-bytes
// https://github.com/minirust/minirust/blob/master/spec/lang/representation.md
broadcast use {group_layout_axioms, group_vstd_default};

/// Memory is represented as a sequence of abstract bytes. Each byte is uninitialized or initialized.
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

// The below spec functions define the `AbstractByte` encoding _abstractly_ for each type.
// This means that, e.g., we can state the specification for transmutes over all types.
// However, in order to reason meaningfully about this encoding, we must provide a concrete specification for it.
/// Is encoding allowed for this type?
pub uninterp spec fn abs_can_be_encoded<T: ?Sized>() -> bool;

/// Can 'value' be encoded to the given bytes?
pub uninterp spec fn abs_encode<T: ?Sized>(value: &T, bytes: Seq<AbstractByte>) -> bool;

/// Can the given bytes always be decoded to the given value?
pub uninterp spec fn abs_decode<T: ?Sized>(bytes: Seq<AbstractByte>, value: &T) -> bool;

/// This trait defines the concrete specification for the given type's `AbstractByte` encoding.
pub trait AbstractByteRepresentation where Self: Sized {
    /// Is encoding allowed for this type?
    /// Because `can_be_encoded` is a precondition for `abs_encode_impl` and `abs_can_be_encoded_impl`,
    /// this definition allows the encoding to be conditionally implement `abs_encode`, `abs_decode`, and `abs_can_be_encoded_impl`.
    spec fn can_be_encoded() -> bool;

    /// Can 'value' be encoded to the given bytes?
    spec fn encode(value: Self, bytes: Seq<AbstractByte>) -> bool;

    /// Can the bytes be decoded to the given value?
    spec fn decode(bytes: Seq<AbstractByte>, value: Self) -> bool;

    // Required properties for a valid encoding.
    /// Any encoding should match the size of this type.
    proof fn encoding_size(v: Self, b: Seq<AbstractByte>)
        requires
            Self::can_be_encoded(),
        ensures
            Self::encode(v, b) ==> b.len() == size_of::<Self>(),
            Self::decode(b, v) ==> b.len() == size_of::<Self>(),
    ;

    /// Every value should have at least one encoding. The `Self` argument is tracked to allow type invariants to be invoked.
    proof fn encoding_exists(tracked v: &Self) -> (b: Seq<AbstractByte>)
        requires
            Self::can_be_encoded(),
        ensures
            Self::encode(*v, b),
    ;

    /// Any encoding should be able to be decoded back to the same value.
    proof fn encoding_invertible(v: Self, b: Seq<AbstractByte>)
        requires
            Self::encode(v, b),
            Self::can_be_encoded(),
        ensures
            Self::decode(b, v),
    ;

    /// Ensures that this encoding implements the abstract `abs_encode` and `abs_decode`.
    /// This is intended to be implemented as an axiom.
    proof fn abs_encode_impl(v: Self, b: Seq<AbstractByte>)
        requires
            Self::can_be_encoded(),
        ensures
            Self::encode(v, b) <==> abs_encode::<Self>(&v, b),
            Self::decode(b, v) <==> abs_decode::<Self>(b, &v),
    ;

    /// Ensures that this encoding implements the abstract `abs_can_be_encoded`.
    /// This is intended to be implemented as an axiom.
    proof fn abs_can_be_encoded_impl()
        requires
            Self::can_be_encoded(),
        ensures
            abs_can_be_encoded::<Self>(),
    ;
}

/// This trait defines the concrete specification for the given type's `AbstractByte` encoding.
/// This definition is for `?Sized` types. Due to restrictions with Rust, this trait cannot be implemented on the type `T` directly.
pub trait AbstractByteRepresentationUnsized<T: ?Sized> {
    /// Is encoding allowed for this type?
    /// This definition allows the encoding to be conditionally defined, e.g. depending on generic type parameters for Self.
    spec fn can_be_encoded() -> bool;

    /// Can 'value' be encoded to the given bytes?
    spec fn encode(value: &T, bytes: Seq<AbstractByte>) -> bool;

    /// Can the given bytes always be decoded to the given value?
    spec fn decode(bytes: Seq<AbstractByte>, value: &T) -> bool;

    // Required properties for encoding (sanity check for any implementation of this trait)
    /// Any encoding should match the size of the corresponding value.
    proof fn encoding_size(v: &T, b: Seq<AbstractByte>)
        requires
            Self::can_be_encoded(),
        ensures
            Self::encode(v, b) ==> b.len() == spec_size_of_val::<T>(v),
            Self::decode(b, v) ==> b.len() == spec_size_of_val::<T>(v),
    ;

    /// Every value should have at least one encoding.
    proof fn encoding_exists(tracked v: &T) -> (b: Seq<AbstractByte>)
        requires
            Self::can_be_encoded(),
        ensures
            Self::encode(v, b),
    ;

    /// Any byte encoding should be able to be decoded back to the same value.
    proof fn encoding_invertible(v: &T, b: Seq<AbstractByte>)
        requires
            Self::encode(v, b),
            Self::can_be_encoded(),
        ensures
            Self::decode(b, v),
    ;

    /// Ensures that this encoding implements the abstract `abs_encode` and `abs_decode`.
    /// This is intended to be implemented as an axiom.
    proof fn abs_encode_impl(v: &T, b: Seq<AbstractByte>)
        requires
            Self::can_be_encoded(),
        ensures
            Self::encode(v, b) <==> abs_encode::<T>(v, b),
            Self::decode(b, v) <==> abs_decode::<T>(b, v),
    ;

    /// Ensures that this encoding implements the abstract `abs_can_be_encoded`.
    /// This is intended to be implemented as an axiom.
    proof fn abs_can_be_encoded_impl()
        requires
            Self::can_be_encoded(),
        ensures
            abs_can_be_encoded::<T>(),
    ;
}

/// The abstract encoding for `bool` encodes the value as a single byte without provenance. On decoding, provenance is ignored.
impl AbstractByteRepresentation for bool {
    open spec fn can_be_encoded() -> bool {
        true
    }

    open spec fn encode(value: bool, bytes: Seq<AbstractByte>) -> bool {
        &&& bytes.len() == 1
        &&& match bytes.first() {
            AbstractByte::Init(0, None) => !value,
            AbstractByte::Init(1, None) => value,
            _ => false,
        }
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

    proof fn encoding_exists(tracked v: &bool) -> (b: Seq<AbstractByte>) {
        seq![
            AbstractByte::Init(
                if *v {
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

    axiom fn abs_encode_impl(v: Self, b: Seq<AbstractByte>);

    axiom fn abs_can_be_encoded_impl();
}

// We utilize the EndianNat type to transform an unsigned int to its byte representation.
/// Convert the given `EndianNat`` representation to `AbtractByte`s with the given provenance.
pub open spec fn endian_to_bytes(endian: EndianNat<u8>, prov: Option<Provenance>) -> Seq<
    AbstractByte,
>
    recommends
        endian.wf(),
{
    endian.digits.map_values(|e| AbstractByte::Init(e as u8, prov))
}

/// Convert the given `AbstractByte` representation to its `EndianNat` representation (provenance is ignored).
pub open spec fn bytes_to_endian(bytes: Seq<AbstractByte>) -> EndianNat<u8>
    recommends
        AbstractByte::all_init(bytes),
{
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
    assert(endian.wf());  // trigger
    assert(endian.len() == bytes.len());  // trigger
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
        assert(bytes.drop_last() == endian_to_bytes(endian.drop_last(), Some(prov)));
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
        assert(bytes.drop_last() == endian_to_bytes(endian.drop_last(), None));
        endian_to_bytes_shared_provenance_none(endian.drop_last());
    }
}

macro_rules! unsigned_int_encoding {
    ($(
        ($int:ty, $lemma_name:ident);
    )+) => {$(
        verus! {
            /// The abstract encoding for `$int` encodes the value as a sequence of bytes of length `size_of::<$int>()`,
            /// with endianness matching the axiomatized `endianness()` for this platform, and without provenance.
            /// On decoding, provenance is ignored.
            impl AbstractByteRepresentation for $int {
                open spec fn can_be_encoded() -> bool {
                    true
                }

                open spec fn encode(value: $int, bytes: Seq<AbstractByte>) -> bool {
                    bytes == endian_to_bytes(
                        EndianNat::<u8>::from_nat_with_len(value as nat, size_of::<$int>()),
                        // integer types have no provenance
                        None,
                    )
                }

                open spec fn decode(bytes: Seq<AbstractByte>, value: $int) -> bool {
                    // fail if any byte is uninitalized or if the byte sequence is not the necessary length
                    &&& bytes.len() == size_of::<$int>()
                    &&& AbstractByte::all_init(bytes)
                    &&& {
                        let endian = bytes_to_endian(bytes);
                        &&& endian.wf()
                        &&& (endian.to_nat() as $int) == value
                    }
                }

                proof fn encoding_size(v: $int, b: Seq<AbstractByte>) {
                    broadcast use endian_to_bytes_to_endian;

                    unsigned_int_max_bounds();
                }

                proof fn encoding_exists(tracked v: &$int) -> (b: Seq<AbstractByte>) {
                    endian_to_bytes(EndianNat::<u8>::from_nat_with_len(v as nat, size_of::<$int>()), None)
                }

                proof fn encoding_invertible(v: $int, b: Seq<AbstractByte>) {
                    broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

                    unsigned_int_max_bounds();
                }

                axiom fn abs_encode_impl(v: Self, b: Seq<AbstractByte>);

                axiom fn abs_can_be_encoded_impl();
            }

            /// Useful properties about `$int::encode(v, bytes)`.
            pub broadcast proof fn $lemma_name(v: $int, bytes: Seq<AbstractByte>)
                requires
                    #[trigger] $int::encode(v, bytes),
                ensures
                    bytes.len() == size_of::<$int>(),
                    AbstractByte::all_init(bytes),
                    AbstractByte::shared_provenance(bytes) == Provenance::null(),
                    bytes_to_endian(bytes).to_nat() as $int == v,
                    bytes_to_endian(bytes).wf(),
            {
                broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

                unsigned_int_max_bounds();
            }
        }
    )+};
}

unsigned_int_encoding! {
    (u8, u8_encode);
    (u16, u16_encode);
    (u32, u32_encode);
    (u64, u64_encode);
    (u128, u128_encode);
    (usize, usize_encode);
}

/// When x is negative, the bitwise result of this function is equivalent
/// to the two's complement representation of x in the given base.
/// https://en.wikipedia.org/wiki/Two%27s_complement#Subtraction_from_2N
pub open spec fn twos_complement(x: int, len: nat) -> nat {
    (pow(u8::base() as int, len) - abs(x)) as nat
}

/// Convert signed number to unsigned number with equivalent bitwise representation.
/// For non-negative numbers, this is a no-op.
pub open spec fn signed_to_unsigned(x: int, len: nat) -> nat {
    if x >= 0 {
        x as nat
    } else {
        twos_complement(x, len)
    }
}

macro_rules! signed_int_encoding {
    ($(
        ($int:ty, $lemma_name:ident, $signed_to_unsigned_lemma_name:ident);
    )+) => {$(
        verus! {
            /// The abstract encoding for `$int` encodes the value as a sequence of bytes of length `size_of::<$int>()`,
            /// with endianness matching the axiomatized `endianness()` for this platform, and without provenance.
            /// Negative numbers are first converted to their unsigned bitwise equivalent and then encoded into bytes.
            /// On decoding, provenance is ignored.
            impl AbstractByteRepresentation for $int {
                open spec fn can_be_encoded() -> bool {
                    true
                }

                open spec fn encode(value: $int, bytes: Seq<AbstractByte>) -> bool {
                    bytes == endian_to_bytes(
                        EndianNat::<u8>::from_nat_with_len(signed_to_unsigned(value as int, size_of::<$int>()), size_of::<$int>()),
                        // integer types have no provenance
                        None,
                    )
                }

                open spec fn decode(bytes: Seq<AbstractByte>, value: $int) -> bool {
                    // fail if any byte is uninitalized or if the byte sequence is not the necessary length
                    &&& bytes.len() == size_of::<$int>()
                    &&& AbstractByte::all_init(bytes)
                    &&& {
                        let endian = bytes_to_endian(bytes);
                        &&& endian.wf()
                        &&& endian.to_nat() == signed_to_unsigned(value as int, size_of::<$int>())
                    }
                }

                proof fn encoding_size(v: $int, b: Seq<AbstractByte>) {
                    broadcast use endian_to_bytes_to_endian;

                    unsigned_int_max_bounds();
                }

                proof fn encoding_exists(tracked v: &$int) -> (b: Seq<AbstractByte>) {
                    endian_to_bytes(EndianNat::<u8>::from_nat_with_len(signed_to_unsigned(v as int, size_of::<$int>()), size_of::<$int>()), None)
                }

                proof fn encoding_invertible(v: $int, b: Seq<AbstractByte>) {
                    broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

                    unsigned_int_max_bounds();
                }

                axiom fn abs_encode_impl(v: Self, b: Seq<AbstractByte>);

                axiom fn abs_can_be_encoded_impl();
            }

            /// Useful properties about `$int::encode(v, bytes)`.
            pub broadcast proof fn $lemma_name(v: $int, bytes: Seq<AbstractByte>)
                requires
                    #[trigger] $int::encode(v, bytes),
                ensures
                    bytes.len() == size_of::<$int>(),
                    AbstractByte::all_init(bytes),
                    AbstractByte::shared_provenance(bytes) == Provenance::null(),
                    bytes_to_endian(bytes).to_nat() == signed_to_unsigned(v as int, size_of::<$int>()),
                    bytes_to_endian(bytes).wf(),
            {
                broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

                unsigned_int_max_bounds()
            }

            pub broadcast proof fn $signed_to_unsigned_lemma_name(v: $int, w: $int)
                requires
                    #[trigger] signed_to_unsigned(v as int, size_of::<$int>()) == #[trigger] signed_to_unsigned(w as int, size_of::<$int>())
                ensures
                    v == w
            {
                signed_int_min_max_bounds();
            }
        }
    )+};
}

signed_int_encoding! {
    (i8, i8_encode, i8_signed_to_unsigned_invertible);
    (i16, i16_encode, i16_signed_to_unsigned_invertible);
    (i32, i32_encode, i32_signed_to_unsigned_invertible);
    (i64, i64_encode, i64_signed_to_unsigned_invertible);
    (i128, i128_encode, i128_signed_to_unsigned_invertible);
    (isize, isize_encode, isize_signed_to_unsigned_invertible);
}

/// This trait defines an `AbstractByte` encoding over the given type `T`.
/// This definition enables reuse of the same underlying encode/decode specifications to implement `AbstractByteRepresentation` across several types.
/// (See the `encoding_from_type_representation` macro.)
/// For example, all zero-sized types can use the same (trivial) encode and decode specifications.
///
/// This trait can also be used to define an encoding on any `T: MyTrait` for some trait `MyTrait`.
/// We cannot implement `AbstractByteRepresentation` generically for all `T: MyTrait` because Rust cannot know that `AbstractByteRepresentation` has not already been implemented for any given `T: MyTrait`.
/// However, we can define a `AbstractByteEncoding` for such `T`, and then use it to implement the `AbstractByteRepresentation` for each concrete `T`. See `PrimitiveAbstractByteEncodingEncoding` for an example.
pub trait AbstractByteEncoding<T> {
    /// Is encoding allowed for this type?
    spec fn can_be_encoded() -> bool;

    /// Can 'value' be encoded to the given bytes?
    spec fn encode(value: T, bytes: Seq<AbstractByte>) -> bool;

    /// Can the bytes be decoded to the given value?
    spec fn decode(bytes: Seq<AbstractByte>, value: T) -> bool;

    // Required properties for a valid encoding.
    /// Any encoding should match the size of this type.
    proof fn encoding_size(v: T, b: Seq<AbstractByte>)
        requires
            Self::can_be_encoded(),
        ensures
            Self::encode(v, b) ==> b.len() == size_of::<T>(),
            Self::decode(b, v) ==> b.len() == size_of::<T>(),
    ;

    /// Every value should have at least one encoding.
    proof fn encoding_exists(tracked v: &T) -> (b: Seq<AbstractByte>)
        requires
            Self::can_be_encoded(),
        ensures
            Self::encode(*v, b),
    ;

    /// Any encoding should be able to be decoded back to the same value.
    proof fn encoding_invertible(v: T, b: Seq<AbstractByte>)
        requires
            Self::encode(v, b),
            Self::can_be_encoded(),
        ensures
            Self::decode(b, v),
    ;
}

#[allow(unused_macros)]
macro_rules! encoding_from_type_representation {
    ($(
        ($name:ty, $type_repr:ty, $spec_mod:tt);
    )+) => {$(
        verus! {
            /// The abstract encoding for `$name` is derived from `$type_repr`.
            impl AbstractByteRepresentation for $name {
                open spec fn can_be_encoded() -> bool {
                    $type_repr::can_be_encoded()
                }

                $spec_mod spec fn encode(value: Self, bytes: Seq<AbstractByte>) -> bool {
                    $type_repr::encode(value, bytes)
                }

                $spec_mod spec fn decode(bytes: Seq<AbstractByte>, value: Self) -> bool {
                    $type_repr::decode(bytes, value)
                }

                proof fn encoding_size(v: Self, b: Seq<AbstractByte>) {
                    $type_repr::encoding_size(v, b);
                }

                proof fn encoding_exists(tracked v: &Self) -> (b: Seq<AbstractByte>) {
                    $type_repr::encoding_exists(v)
                }

                proof fn encoding_invertible(v: Self, b: Seq<AbstractByte>) {
                    $type_repr::encoding_invertible(v, b);
                }

                axiom fn abs_encode_impl(v: Self, b: Seq<AbstractByte>);

                axiom fn abs_can_be_encoded_impl();
            }
        }
    )+};

    ($(
        ($name:ty, $generic:ty, $bound:ty, $type_repr:ty, $spec_mod:tt);
    )+) => {$(
        verus! {
            /// The abstract encoding for `$name<$generic>` is derived from `$type_repr`.
            impl<$generic: $bound> AbstractByteRepresentation for $name<$generic> {
                open spec fn can_be_encoded() -> bool {
                    $type_repr::can_be_encoded()
                }

                $spec_mod spec fn encode(value: Self, bytes: Seq<AbstractByte>) -> bool {
                    $type_repr::encode(value, bytes)
                }

                $spec_mod spec fn decode(bytes: Seq<AbstractByte>, value: Self) -> bool {
                    $type_repr::decode(bytes, value)
                }

                proof fn encoding_size(v: Self, b: Seq<AbstractByte>) {
                    $type_repr::encoding_size(v, b);
                }

                proof fn encoding_exists(tracked v: &Self) -> (b: Seq<AbstractByte>) {
                    $type_repr::encoding_exists(v)
                }

                proof fn encoding_invertible(v: Self, b: Seq<AbstractByte>) {
                    $type_repr::encoding_invertible(v, b);
                }

                axiom fn abs_encode_impl(v: Self, b: Seq<AbstractByte>);

                axiom fn abs_can_be_encoded_impl();
            }
        }
    )+};
}

pub(crate) use encoding_from_type_representation;

/// This trait is implemented on types which are zero-sized and therefore have a trivial `AbstractByte` encoding (i.e., the empty sequence).
/// It is used to define a corresponding `AbstractByteEncoding` for `Self` which is implemented on `ZeroSizedRepresentationEncoding<Self>`.
/// `ZeroSizedRepresentationEncoding<Self>` can then be used to implement `AbstractByteRepresentation` on `Self`.
pub trait ZeroSizedRepresentation where Self: Sized {
    proof fn layout_of_zero_sized_repr()
        ensures
            crate::vstd::layout::size_of::<Self>() == 0,
    ;
}

pub struct ZeroSizedRepresentationEncoding<T: ZeroSizedRepresentation> {
    _t: T,
}

impl<T: ZeroSizedRepresentation> AbstractByteEncoding<T> for ZeroSizedRepresentationEncoding<T> {
    open spec fn can_be_encoded() -> bool {
        true
    }

    open spec fn encode(value: T, bytes: Seq<AbstractByte>) -> bool {
        bytes == Seq::<AbstractByte>::empty()
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: T) -> bool {
        bytes == Seq::<AbstractByte>::empty()
    }

    proof fn encoding_size(v: T, b: Seq<AbstractByte>) {
        T::layout_of_zero_sized_repr();
    }

    proof fn encoding_exists(tracked v: &T) -> (b: Seq<AbstractByte>) {
        Seq::<AbstractByte>::empty()
    }

    proof fn encoding_invertible(v: T, b: Seq<AbstractByte>) {
    }
}

// () is a ZST and therefore can share the trivial encoding.
impl ZeroSizedRepresentation for () {
    proof fn layout_of_zero_sized_repr() {
        broadcast use group_layout_axioms;

    }
}

encoding_from_type_representation! {
    ((), ZeroSizedRepresentationEncoding::<()>, open);
}

/// Is there an `AbstractByte` encoding for this value?
pub open spec fn encoding_exists<T>(value: T) -> bool {
    exists|bytes| #[trigger] abs_encode::<T>(&value, bytes)
}

/// Has a suitable encoding been implemented for the pointer metadata type `<T as core::ptr::Pointee>::Metadata`?
pub open spec fn ptr_metadata_encoding_well_defined<T: ?Sized>() -> bool {
    // the size of the metadata should correspond to the amount of bytes that it must occupy in the pointer's encoding
    // (the first usize bytes in the pointer's encoding are the address)
    &&& size_of::<<T as core::ptr::Pointee>::Metadata>() + size_of::<usize>() == size_of::<
        *mut T,
    >()
    // any encoding of the metadata will take up the expected amount of bytes
    &&& (forall|value, bytes| #[trigger]
        abs_encode::<<T as core::ptr::Pointee>::Metadata>(&value, bytes) ==> size_of::<
            <T as core::ptr::Pointee>::Metadata,
        >() == bytes.len())
    &&& (forall|value, bytes| #[trigger]
        abs_decode::<<T as core::ptr::Pointee>::Metadata>(bytes, &value) ==> size_of::<
            <T as core::ptr::Pointee>::Metadata,
        >() == bytes.len())
    // the encoding is "invertible"
    &&& (forall|value, bytes| #[trigger]
        abs_encode::<<T as core::ptr::Pointee>::Metadata>(&value, bytes) ==> abs_decode::<
            <T as core::ptr::Pointee>::Metadata,
        >(bytes, &value))
    // an encoding exists for all metadata values
    &&& (forall|value| #[trigger] encoding_exists::<<T as core::ptr::Pointee>::Metadata>(value))
}

/// For `T: Sized`, the pointer metadata type for `*mut T` and `*const T` has a suitable encoding.
pub broadcast proof fn ptr_metadata_encoding_well_defined_sized_types<T: Sized>()
    ensures
        #[trigger] ptr_metadata_encoding_well_defined::<T>(),
{
    assert forall|value, bytes| #[trigger]
        abs_encode::<<T as core::ptr::Pointee>::Metadata>(&value, bytes) implies size_of::<
        <T as core::ptr::Pointee>::Metadata,
    >() == bytes.len() by {
        <<T as core::ptr::Pointee>::Metadata as AbstractByteRepresentation>::abs_encode_impl(
            value,
            bytes,
        );
        <<T as core::ptr::Pointee>::Metadata as AbstractByteRepresentation>::encoding_size(
            value,
            bytes,
        );
    }
    assert forall|value, bytes| #[trigger]
        abs_decode::<<T as core::ptr::Pointee>::Metadata>(bytes, &value) implies size_of::<
        <T as core::ptr::Pointee>::Metadata,
    >() == bytes.len() by {
        <<T as core::ptr::Pointee>::Metadata as AbstractByteRepresentation>::abs_encode_impl(
            value,
            bytes,
        );
        <<T as core::ptr::Pointee>::Metadata as AbstractByteRepresentation>::encoding_size(
            value,
            bytes,
        );
    }
    assert forall|value, bytes| #[trigger]
        abs_encode::<<T as core::ptr::Pointee>::Metadata>(&value, bytes) implies abs_decode::<
        <T as core::ptr::Pointee>::Metadata,
    >(bytes, &value) by {
        <<T as core::ptr::Pointee>::Metadata as AbstractByteRepresentation>::abs_encode_impl(
            value,
            bytes,
        );
        <<T as core::ptr::Pointee>::Metadata as AbstractByteRepresentation>::encoding_invertible(
            value,
            bytes,
        );
    }
    assert forall|value| #[trigger]
        encoding_exists::<<T as core::ptr::Pointee>::Metadata>(value) by {
        let bytes = Seq::<AbstractByte>::empty();
        <<T as core::ptr::Pointee>::Metadata as AbstractByteRepresentation>::abs_encode_impl(
            value,
            bytes,
        );
    }
}

/// Implements `AbstractByteEncoding` for raw pointers.
///
/// This encoding is intended to be shared across `*const T` and `*mut T`, as both types have the same layout (see: [Raw pointer type layout](https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer)).
/// The encoding is defined for `T: ?Sized`, and can be used to conditionally implement the encoding for raw pointers.
/// The condition is whether a suitable encoding has been implemented for the pointer's metadata type `<T as core::ptr::Pointee>::Metadata` (see: [Pointee::Metadata](https://doc.rust-lang.org/1.88.0/core/ptr/trait.Pointee.html#pointer-metadata)).
/// This is defined as `ptr_metadata_encoding_well_defined::<T>()`.
///
/// *Note:* This encoding assumes that the pointer address is encoded first, followed by the pointer metadata. This is, to our knowledge, not a stable assumption.
///
/// The encoding for raw pointers is divided into two parts:
///
/// The first `size_of::<usize>()` bytes encode the pointer's address and per-byte provenance.
/// On decoding, all of the first `size_of::<usize>()` bytes must have the same provenance in order for the resulting pointer to have non-null provenance.
///
/// The next `size_of::<*mut T>() - size_of::<usize>()` bytes encode the pointer's metadata.
/// This is specified using `abs_encode::<<T as core::ptr::Pointee>::Metadata>` and `abs_decode::<<T as core::ptr::Pointee>::Metadata>`.
/// - For `T: Sized`, the metadata is always `()`, so the metadata encoding is a sequence of length 0.
///   Because the encoding for `()` is already implemented (see the lemma `ptr_metadata_encoding_well_defined_sized_types`),
///   this `AbstractByteEncoding` provides an implementation for the encodings of raw pointers to all sized types.
/// - For `T: ?Sized`, if the encoding for `<T as core::ptr::Pointee>::Metadata` is not implemented as specified by `ptr_metadata_encoding_well_defined::<T>()`,
///   then this `AbstractByteEncoding` will not provide an implementation for the encodings of `*mut T` or `*const T`.
pub struct RawPtrRepresentation<T: ?Sized> {
    _t: T,
}

impl<T: ?Sized> AbstractByteEncoding<*mut T> for RawPtrRepresentation<T> {
    open spec fn can_be_encoded() -> bool {
        ptr_metadata_encoding_well_defined::<T>()
    }

    open spec fn encode(value: *mut T, bytes: Seq<AbstractByte>) -> bool {
        let prefix = bytes.subrange(0, size_of::<usize>() as int);
        let suffix = bytes.subrange(size_of::<usize>() as int, size_of::<*mut T>() as int);
        &&& bytes.len() == size_of::<*mut T>()
        &&& prefix == endian_to_bytes(
            EndianNat::<u8>::from_nat_with_len(value@.addr as nat, size_of::<usize>()),
            // the abstract encoding preserves the provenance from this pointer
            Some(value@.provenance),
        )
        &&& abs_encode::<<T as core::ptr::Pointee>::Metadata>(&value@.metadata, suffix)
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: *mut T) -> bool {
        let prefix = bytes.subrange(0, size_of::<usize>() as int);
        let suffix = bytes.subrange(size_of::<usize>() as int, size_of::<*mut T>() as int);
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
        &&& abs_decode::<<T as core::ptr::Pointee>::Metadata>(suffix, &value@.metadata)
    }

    proof fn encoding_size(v: *mut T, b: Seq<AbstractByte>) {
    }

    proof fn encoding_exists(tracked v: &*mut T) -> (b: Seq<AbstractByte>) {
        broadcast use endian_to_bytes_to_endian;

        unsigned_int_max_bounds();
        let prefix = endian_to_bytes(
            EndianNat::<u8>::from_nat_with_len(v@.addr as nat, size_of::<usize>()),
            Some(v@.provenance),
        );

        assert(encoding_exists::<<T as core::ptr::Pointee>::Metadata>(v@.metadata));
        let suffix = choose|bytes|
            abs_encode::<<T as core::ptr::Pointee>::Metadata>(&(v@.metadata), bytes);
        let b = prefix.add(suffix);
        assert(b.subrange(0, size_of::<usize>() as int) == prefix);
        assert(b.subrange(size_of::<usize>() as int, size_of::<*mut T>() as int) == suffix);
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

macro_rules! raw_ptr_encoding_from_type_representation {
    ($(
        ($mutability:tt, $sized_lemma_name:ident, $unsized_lemma_name:ident);
    )+) => {$(
        verus! {
            /// The abstract encoding for `*$mutability T` is derived from `RawPtrRepresentation`.
            impl<T: ?Sized> AbstractByteRepresentation for *$mutability T {
                open spec fn can_be_encoded() -> bool {
                    RawPtrRepresentation::<T>::can_be_encoded()
                }

                open spec fn encode(value: Self, bytes: Seq<AbstractByte>) -> bool {
                    RawPtrRepresentation::encode(value as *mut T, bytes)
                }

                open spec fn decode(bytes: Seq<AbstractByte>, value: Self) -> bool {
                    RawPtrRepresentation::decode(bytes, value as *mut T)
                }

                proof fn encoding_size(v: Self, b: Seq<AbstractByte>) {
                    RawPtrRepresentation::encoding_size(v as *mut T, b);
                }

                proof fn encoding_exists(tracked v: &Self) -> (b: Seq<AbstractByte>) {
                    let tracked m = &(*v as *mut T);
                    RawPtrRepresentation::encoding_exists(m)
                }

                proof fn encoding_invertible(v: Self, b: Seq<AbstractByte>) {
                    RawPtrRepresentation::encoding_invertible(v as *mut T, b);
                }

                axiom fn abs_encode_impl(v: Self, b: Seq<AbstractByte>);

                axiom fn abs_can_be_encoded_impl();
            }

            /// Useful properties for `<*$mutability T as AbstractByteRepresentation>::encode(v, bytes)` for `T: Sized`.
            pub broadcast proof fn $sized_lemma_name<T: Sized>(v: *$mutability T, bytes: Seq<AbstractByte>)
                requires
                    #[trigger] <*$mutability T as AbstractByteRepresentation>::encode(v, bytes),
                ensures
                    ({
                        let prefix = bytes.subrange(0, size_of::<usize>() as int);
                        let suffix = bytes.subrange(size_of::<usize>() as int, size_of::<*$mutability T>() as int);
                        &&& bytes.len() == size_of::<*$mutability T>()
                        &&& AbstractByte::all_init(prefix)
                        &&& AbstractByte::shared_provenance(prefix) == v@.provenance
                        &&& bytes_to_endian(prefix).to_nat() as usize == v@.addr
                        &&& bytes_to_endian(prefix).wf()
                        &&& ptr_metadata_encoding_well_defined::<T>()
                        &&& <() as AbstractByteRepresentation>::encode(v@.metadata, suffix)
                        &&& <() as AbstractByteRepresentation>::decode(suffix, v@.metadata)
                    }),
            {
                broadcast use
                    EndianNat::from_nat_to_nat,
                    endian_to_bytes_to_endian,
                    endian_to_bytes_shared_provenance,
                    ptr_metadata_encoding_well_defined_sized_types
                ;

                let suffix = bytes.subrange(size_of::<usize>() as int, size_of::<*$mutability T>() as int);
                <() as AbstractByteRepresentation>::abs_encode_impl(v@.metadata, suffix);

                unsigned_int_max_bounds();
            }

            /// Useful properties for `<*$mutability T as AbstractByteRepresentation>::encode(v, bytes)` for `T: ?Sized`.
            pub broadcast proof fn $unsized_lemma_name<T: ?Sized>(v: *$mutability T, bytes: Seq<AbstractByte>)
                requires
                    #[trigger] <*$mutability T as AbstractByteRepresentation>::encode(v, bytes),
                    ptr_metadata_encoding_well_defined::<T>()
                ensures
                    ({
                        let prefix = bytes.subrange(0, size_of::<usize>() as int);
                        let suffix = bytes.subrange(size_of::<usize>() as int, size_of::<*$mutability T>() as int);
                        &&& bytes.len() == size_of::<*$mutability T>()
                        &&& AbstractByte::all_init(prefix)
                        &&& AbstractByte::shared_provenance(prefix) == v@.provenance
                        &&& bytes_to_endian(prefix).to_nat() as usize == v@.addr
                        &&& bytes_to_endian(prefix).wf()
                        &&& abs_encode::<<T as core::ptr::Pointee>::Metadata>(&(v@.metadata), suffix)
                        &&& abs_decode::<<T as core::ptr::Pointee>::Metadata>(suffix, &(v@.metadata))
                    }),
            {
                broadcast use
                    EndianNat::from_nat_to_nat,
                    endian_to_bytes_to_endian,
                    endian_to_bytes_shared_provenance,
                ;

                unsigned_int_max_bounds();
            }
        }
    )+};
}

raw_ptr_encoding_from_type_representation! {
    (mut, mut_ptr_sized_encode, mut_ptr_unsized_encode);
    (const, const_ptr_sized_encode, const_ptr_unsized_encode);
}

/// This trait is implemented on fieldness enums with a primitive type representation, defined with the `#[repr(<primitive>)]` attribute.
/// Such types therefore share the same byte encoding as the `Primitive` type (see: [Primitive representations](https://doc.rust-lang.org/reference/type-layout.html#primitive-representation-of-field-less-enums)).
/// A primitive type representation means that the enum is encoded as the discriminant's integer value.
/// This trait is used to define a `AbstractByteEncoding` for `Self` which is implemented on `PrimitiveRepresentationEncoding<Primitive, Self>`.
/// This representation uses `<Primitive as AbstractByteRepresentation>::encode` and `<Primitive as AbstractByteRepresentation>::decode` after invoking `Self::to_primitive`.
/// `PrimitiveRepresentationEncoding<Primitive, Self>` can then be used to implement `AbstractByteRepresentation` on `Self`.
pub trait PrimitiveRepresentation<Primitive: AbstractByteRepresentation> where
    Self: Sized,
 {
    spec fn to_primitive(v: Self) -> Primitive;

    proof fn to_primitive_tracked(tracked v: &Self) -> (tracked p: &Primitive)
        ensures
            *p == Self::to_primitive(*v),
    ;

    proof fn layout_of_primitive_repr()
        ensures
            crate::vstd::layout::size_of::<Self>() == crate::vstd::layout::size_of::<Primitive>(),
            crate::vstd::layout::align_of::<Self>() == crate::vstd::layout::align_of::<Primitive>(),
    ;
}

pub struct PrimitiveRepresentationEncoding<
    Primitive: AbstractByteRepresentation,
    T: PrimitiveRepresentation<Primitive>,
> {
    _t: T,
    _primitive: Primitive,
}

impl<
    Primitive: AbstractByteRepresentation,
    T: PrimitiveRepresentation<Primitive>,
> AbstractByteEncoding<T> for PrimitiveRepresentationEncoding<Primitive, T> {
    open spec fn can_be_encoded() -> bool {
        Primitive::can_be_encoded()
    }

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

    proof fn encoding_exists(tracked v: &T) -> (b: Seq<AbstractByte>) {
        Primitive::encoding_exists(T::to_primitive_tracked(v))
    }

    proof fn encoding_invertible(v: T, b: Seq<AbstractByte>) {
        Primitive::encoding_invertible(T::to_primitive(v), b);
    }
}

/// This trait is implemented on structs or enums with a transparent type representation, defined with the `#[repr(transparent)]` attribute.
/// Such types therefore share the same encoding as the `Inner` type (see: [Transparent representations](https://doc.rust-lang.org/reference/type-layout.html#the-transparent-representation)).
/// A transparent type representation means that the struct/enum has at most one non-zero-sized field, and the type is thus encoded as that field's value.
/// This trait is used to define a `AbstractByteEncoding` for `Self` which is implemented on `TransparentRepresentationEncoding<Inner, Self>`.
/// This representation uses `<Inner as AbstractByteRepresentation>::encode` and `<Inner as AbstractByteRepresentation>::decode` after invoking `Self::to_inner`.
/// `TransparentRepresentationEncoding<Inner, Self>` can then be used to implement `AbstractByteRepresentation` on `Self`.
pub trait TransparentRepresentation<Inner: AbstractByteRepresentation> where Self: Sized {
    spec fn to_inner(v: Self) -> Inner;

    proof fn to_inner_tracked(tracked v: &Self) -> (tracked i: &Inner)
        ensures
            *i == Self::to_inner(*v),
    ;

    proof fn layout_of_transparent_repr()
        ensures
            crate::vstd::layout::size_of::<Self>() == crate::vstd::layout::size_of::<Inner>(),
            crate::vstd::layout::align_of::<Self>() == crate::vstd::layout::align_of::<Inner>(),
    ;
}

pub struct TransparentRepresentationEncoding<
    Inner: AbstractByteRepresentation,
    T: TransparentRepresentation<Inner>,
> {
    _t: T,
    _inner: Inner,
}

impl<Inner: AbstractByteRepresentation, T: TransparentRepresentation<Inner>> AbstractByteEncoding<
    T,
> for TransparentRepresentationEncoding<Inner, T> {
    open spec fn can_be_encoded() -> bool {
        Inner::can_be_encoded()
    }

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

    proof fn encoding_exists(tracked v: &T) -> (b: Seq<AbstractByte>) {
        Inner::encoding_exists(T::to_inner_tracked(v))
    }

    proof fn encoding_invertible(v: T, b: Seq<AbstractByte>) {
        Inner::encoding_invertible(T::to_inner(v), b);
    }
}

/// This trait is implemented on structs or enums with a scalar valid range, defined with the `#[repr(rustc_layout_scalar_valid_range_start(...))]` and `#[repr(rustc_layout_scalar_valid_range_end(...))]` attributes.
/// A scalar range representation means that the type must take on values within the specified range (which we represent over `nat`s).
/// The compiler uses this attribute to perform the niche optimization (See: [https://doc.rust-lang.org/std/option/#representation](https://doc.rust-lang.org/std/option/#representation)).
/// Given `Repr` which is an existing `AbstractByteEncoding<Self>`, this trait is used to define a new `AbstractByteEncoding` for `Self` which is implemented on `ScalarRangeRepresentationEncoding<Inner, Self>`.
/// This representation uses `Repr::encode` and `Repr::decode` but also that the value fall within the given range in order to be encoded or decoded, respectively.
/// `ScalarRangeRepresentationEncoding<Inner, Self>` can then be used to implement `AbstractByteRepresentation` on `Self`.
pub trait ScalarRangeRepresentation<Repr: AbstractByteEncoding<Self>> where Self: Sized {
    spec fn scalar_range_min() -> nat;

    spec fn scalar_range_max() -> nat;

    spec fn to_nat(v: Self) -> nat;

    spec fn in_scalar_range(v: Self) -> bool;

    proof fn valid_scalar_range_repr(tracked v: &Self)
        ensures
            Self::scalar_range_min() <= Self::to_nat(*v) <= Self::scalar_range_max(),
    ;
}

pub struct ScalarRangeRepresentationEncoding<
    Repr: AbstractByteEncoding<T>,
    T: ScalarRangeRepresentation<Repr>,
> {
    _t: T,
    _repr: Repr,
}

impl<Repr: AbstractByteEncoding<T>, T: ScalarRangeRepresentation<Repr>> AbstractByteEncoding<
    T,
> for ScalarRangeRepresentationEncoding<Repr, T> {
    open spec fn can_be_encoded() -> bool {
        Repr::can_be_encoded()
    }

    open spec fn encode(value: T, bytes: Seq<AbstractByte>) -> bool {
        &&& Repr::encode(value, bytes)
        &&& T::scalar_range_min() <= T::to_nat(value) <= T::scalar_range_max()
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: T) -> bool {
        &&& Repr::decode(bytes, value)
        &&& T::scalar_range_min() <= T::to_nat(value) <= T::scalar_range_max()
    }

    proof fn encoding_size(v: T, b: Seq<AbstractByte>) {
        Repr::encoding_size(v, b);
    }

    proof fn encoding_exists(tracked v: &T) -> (b: Seq<AbstractByte>) {
        T::valid_scalar_range_repr(&v);
        Repr::encoding_exists(v)
    }

    proof fn encoding_invertible(v: T, b: Seq<AbstractByte>) {
        Repr::encoding_invertible(v, b);
    }
}

/// The abstract encoding for a `[u8]` maps each value in the slice to a corresponding abtract byte with no provenance.
pub struct EncodingU8Slice;

impl AbstractByteRepresentationUnsized<[u8]> for EncodingU8Slice {
    open spec fn can_be_encoded() -> bool {
        true
    }

    open spec fn encode(value: &[u8], bytes: Seq<AbstractByte>) -> bool {
        bytes == value@.map_values(|e| AbstractByte::Init(e, None))
    }

    open spec fn decode(bytes: Seq<AbstractByte>, value: &[u8]) -> bool {
        value@ == bytes.map_values(|b: AbstractByte| b.byte())
    }

    proof fn encoding_size(v: &[u8], b: Seq<AbstractByte>) {
    }

    proof fn encoding_exists(tracked v: &[u8]) -> (b: Seq<AbstractByte>) {
        v@.map_values(|e| AbstractByte::Init(e, None))
    }

    proof fn encoding_invertible(v: &[u8], b: Seq<AbstractByte>) {
        assert(v@ == b.map_values(|bt: AbstractByte| bt.byte()));
    }

    axiom fn abs_encode_impl(v: &[u8], b: Seq<AbstractByte>);

    axiom fn abs_can_be_encoded_impl();
}

pub broadcast group group_type_representation_axioms {
    u8_encode,
    u16_encode,
    u32_encode,
    u64_encode,
    u128_encode,
    usize_encode,
    i8_encode,
    i16_encode,
    i32_encode,
    i64_encode,
    i128_encode,
    isize_encode,
    i8_signed_to_unsigned_invertible,
    i16_signed_to_unsigned_invertible,
    i32_signed_to_unsigned_invertible,
    i64_signed_to_unsigned_invertible,
    i128_signed_to_unsigned_invertible,
    isize_signed_to_unsigned_invertible,
    mut_ptr_sized_encode,
    mut_ptr_unsized_encode,
    const_ptr_sized_encode,
    const_ptr_unsized_encode,
    ptr_metadata_encoding_well_defined_sized_types,
}

} // verus!
