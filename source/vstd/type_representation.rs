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

broadcast use {group_layout_axioms, group_vstd_default};
// https://github.com/minirust/minirust/blob/master/spec/mem/interface.md#abstract-bytes
// https://github.com/minirust/minirust/blob/master/spec/lang/representation.md

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

/// Can 'value' be encoded to the given bytes?
pub uninterp spec fn abs_encode<T: ?Sized>(value: &T, bytes: Seq<AbstractByte>) -> bool;

/// Can the given bytes always be decoded to the given value?
pub uninterp spec fn abs_decode<T: ?Sized>(bytes: Seq<AbstractByte>, value: &T) -> bool;

/// This trait is defines the given type's `AbstractByte` encoding. This definition is for `Sized` types only: see `AbstractEncodingUnsized` for `?Sized` types.
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
    proof fn encoding_exists(tracked v: &Self) -> (b: Seq<AbstractByte>)
        ensures
            Self::encode(*v, b),
    ;

    /// Any encoding should be able to be decoded back to the same value.
    broadcast proof fn encoding_invertible(v: Self, b: Seq<AbstractByte>)
        requires
            #[trigger] Self::encode(v, b),
        ensures
            #[trigger] Self::decode(b, v),
    ;

    /// Ensures that the encoding defined here matches the axiomatized encoding functions `abs_encode` and `abs_decode`.
    /// This is intended to be implemented as an axiom.
    broadcast proof fn valid_encoding(v: Self, b: Seq<AbstractByte>)
        ensures
            #![trigger abs_encode::<Self>(&v, b)]
            #![trigger abs_decode::<Self>(b, &v)]
            Self::encode(v, b) <==> abs_encode::<Self>(&v, b),
            Self::decode(b, v) <==> abs_decode::<Self>(b, &v),
    ;
}

/// The abstract encoding for `bool` encodes the value as a single byte without provenance.
/// On decoding, provenance is ignored.
impl AbstractEncoding for bool {
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

    axiom fn valid_encoding(v: Self, b: Seq<AbstractByte>);
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

macro_rules! unsigned_int_encoding {
    ($(
        ($int:ty, $lemma_name:ident);
    )+) => {$(
        verus! {
            /// The abstract encoding for `$int` encodes the value as a sequence of bytes of length `size_of::<$int>()`,
            /// with endianness matching the axiomatized `endianness()` for this platform, and without provenance.
            /// On decoding, provenance is ignored.
            impl AbstractEncoding for $int {
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

                axiom fn valid_encoding(v: Self, b: Seq<AbstractByte>);
            }

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
        ($int:ty);
    )+) => {$(
        verus! {
            /// The abstract encoding for `$int` encodes the value as a sequence of bytes of length `size_of::<$int>()`,
            /// with endianness matching the axiomatized `endianness()` for this platform, and without provenance.
            /// Negative numbers are first converted to their unsigned bitwise equivalent and then encoded into bytes.
            /// On decoding, provenance is ignored.
            impl AbstractEncoding for $int {
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

                axiom fn valid_encoding(v: Self, b: Seq<AbstractByte>);
            }
        }
    )+};
}

signed_int_encoding! {
    (i8);
    (i16);
    (i32);
    (i64);
    (i128);
    (isize);
}

/// This trait defines an `AbstractByte` encoding over the given type `T`.
/// This definition enables reuse of the same underlying representation for `AbstractEncoding` across several concrete types.
/// For example, enums can use the same representation as a primitive type through the use of the `#[repr]` attribute.
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
    proof fn encoding_exists(tracked v: &T) -> (b: Seq<AbstractByte>)
        ensures
            Self::encode(*v, b),
    ;

    /// Any encoding should be able to be decoded back to the same value.
    broadcast proof fn encoding_invertible(v: T, b: Seq<AbstractByte>)
        requires
            #[trigger] Self::encode(v, b),
        ensures
            #[trigger] Self::decode(b, v),
    ;
}

/// Implements the type representation for raw pointers. This representation is shared across `*const T`` and `*mut T`.
/// The below encoding works for types `T` that are both sized and unsized (i.e. DSTs) and contains a prefix and a suffix.
/// The "prefix": the first `size_of::<usize>()` bytes of the encoding will always encode the pointer's address and per-byte provenance.
/// The "suffix": the next `size_of::<*mut T>() - size_of::<usize>()` bytes will have contents that are unspecified.
/// - For `T: Sized`, `size_of::<*mut T>() = size_of::<usize>()`, and so the suffix is a sequence of length 0 and thereby empty.
/// - For `T` unsized, the Rust language reference only specifies that `size_of::<*mut T>() >= size_of::<usize>()`, so this encoding allows the byte sequence to take the necessary (unspecified) length.
/// ([Reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer))
pub struct RawPtrRepresentation;

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

    proof fn encoding_exists(tracked v: &*mut T) -> (b: Seq<AbstractByte>) {
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

macro_rules! raw_ptr_encoding_from_type_representation {
    ($(
        ($mutability:tt, $sized_lemma_name:ident, $unsized_lemma_name:ident);
    )+) => {$(
        verus! {
            /// The abstract encoding for `*$mutability T` encodes the pointer's address and provenance in the first `size_of::<usize>()` bytes,
            /// and leaves the next `size_of::<*mut T>() - size_of::<usize>()` bytes unspecified.
            /// On decoding, all of the first `size_of::<usize>()` bytes must have the same provenance in order for the resulting pointer to have non-null provenance.
            impl<T: ?Sized> AbstractEncoding for *$mutability T {
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

                axiom fn valid_encoding(v: Self, b: Seq<AbstractByte>);
            }

            pub broadcast proof fn $sized_lemma_name<T: Sized>(v: *$mutability T, bytes: Seq<AbstractByte>)
                requires
                    #[trigger] <*$mutability T as AbstractEncoding>::encode(v, bytes),
                ensures
                    bytes.len() == size_of::<*$mutability T>(),
                    bytes =~= bytes.subrange(0, size_of::<*$mutability T>() as int),
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

            pub broadcast proof fn $unsized_lemma_name<T: ?Sized>(v: *$mutability T, bytes: Seq<AbstractByte>)
                requires
                    #[trigger] <*$mutability T as AbstractEncoding>::encode(v, bytes),
                ensures
                    ({
                        let prefix = bytes.subrange(0, size_of::<usize>() as int);
                        &&& bytes.len() == size_of::<*$mutability T>()
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
        }
    )+};
}

raw_ptr_encoding_from_type_representation! {
    (mut, mut_ptr_sized_encode, mut_ptr_unsized_encode);
    (const, const_ptr_sized_encode, const_ptr_unsized_encode);
}
// Composite types: The representations for these types are derived from the encoding on another type.


/// This trait is used to define a `TypeRepresentation` for the given type using the `AbstractEncoding` for a primitive type.
/// The corresponding `TypeRepresentation` is implemented on the struct `PrimitiveRepresentationEncoding<Primitive, Self>`.
/// This models the type representation for fieldless enums with the `#[repr(<primitive>)]` annotation.
/// [Primitive representations](https://doc.rust-lang.org/reference/type-layout.html#primitive-representation-of-field-less-enums)
pub trait PrimitiveRepresentation<Primitive: AbstractEncoding + PrimitiveInt> where Self: Sized {
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

    proof fn encoding_exists(tracked v: &T) -> (b: Seq<AbstractByte>) {
        Primitive::encoding_exists(T::to_primitive_tracked(v))
    }

    proof fn encoding_invertible(v: T, b: Seq<AbstractByte>) {
        Primitive::encoding_invertible(T::to_primitive(v), b);
    }
}

/// This trait is used to define a `TypeRepresentation` for the given type using the `AbstractEncoding` for the only nonzero-sized field on that type.
/// The corresponding `TypeRepresentation` is implemented on the struct `TransparentRepresentationEncoding<Primitive, Self>`.
/// This models the type representation for structs and enums with the `#[repr(transparent)]` annotation.
/// [Transparent representations](https://doc.rust-lang.org/reference/type-layout.html#the-transparent-representation)
pub trait TransparentRepresentation<Inner: AbstractEncoding> where Self: Sized {
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

    proof fn encoding_exists(tracked v: &T) -> (b: Seq<AbstractByte>) {
        Inner::encoding_exists(T::to_inner_tracked(v))
    }

    proof fn encoding_invertible(v: T, b: Seq<AbstractByte>) {
        Inner::encoding_invertible(T::to_inner(v), b);
    }
}

/// This trait is used to define a `TypeRepresentation` for the given type by imposing a scalar range restriction (implemented on `nat`s) on an existing `TypeRepresentation` for this type.
/// The corresponding `TypeRepresentation` is implemented on the struct `ScalarRangeRepresentationEncoding<Repr, Self>`.
/// This models the `#[rustc_layout_scalar_valid_range_start(...)]` and `#[rustc_layout_scalar_valid_range_end(...)]` attributes.
/// These additional range restrictions on the encoding are needed when the type's representation is a transparent representation
/// because we must forbid values outside of the allowed range from being decoded.
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

    proof fn encoding_exists(tracked v: &T) -> (b: Seq<AbstractByte>) {
        T::valid_scalar_range_repr(&v);
        Repr::encoding_exists(v)
    }

    proof fn encoding_invertible(v: T, b: Seq<AbstractByte>) {
        Repr::encoding_invertible(v, b);
    }
}

// This macro can't yet handle generics, but it can be used to reduce repeated code in simple cases.
#[allow(unused_macros)]
macro_rules! encoding_from_type_representation {
    ($(
        ($name:ty, $type_repr:ty, $spec_mod:tt);
    )+) => {$(
        verus! {
            /// The abstract encoding for `$name` is derived from `$type_repr`.
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

                proof fn encoding_exists(tracked v: &Self) -> (b: Seq<AbstractByte>) {
                    $type_repr::encoding_exists(v)
                }

                proof fn encoding_invertible(v: Self, b: Seq<AbstractByte>) {
                    $type_repr::encoding_invertible(v, b);
                }

                axiom fn valid_encoding(v: Self, b: Seq<AbstractByte>);
            }
        }
    )+};
}

pub(crate) use encoding_from_type_representation;

/// This trait is defines the given type's `AbstractByte` encoding. This definition is for `?Sized` types.
/// Due to restrictions on Rust, this trait cannot be implemented on the type `T` directly.
pub trait AbstractEncodingUnsized<T: ?Sized> {
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

    /// Ensures that the encoding defined here matches the axiomatized encoding functions `abs_encode` and `abs_decode`.
    /// This is intended to be implemented as an axiom.
    broadcast proof fn valid_encoding(v: &T, b: Seq<AbstractByte>)
        ensures
            #![trigger Self::encode(v, b), abs_encode::<T>(v, b)]
            #![trigger Self::decode(b, v), abs_decode::<T>(b, v)]
            Self::encode(v, b) <==> abs_encode::<T>(v, b),
            Self::decode(b, v) <==> abs_decode::<T>(b, v),
    ;
}

/// The abstract encoding for a `[u8]` maps each value in the slice to a corresponding abtract byte with no provenance.
pub struct EncodingU8Slice;

impl AbstractEncodingUnsized<[u8]> for EncodingU8Slice {
    // todo - should slices be encoded with provenance?
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

    axiom fn valid_encoding(v: &[u8], b: Seq<AbstractByte>);
}

} // verus!
