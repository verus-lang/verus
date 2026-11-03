//! This module defines (i.e., axiomatizes) the Rust abstract machine's representation for many primitive types (integers, boolean, raw pointers, shared references, slices),
//! as well as helpers for defining the representation for structs and enums derived from these primitive types.
//!
//! The representation is defined on a `Seq<AbstractByte>`, which encodes byte values as well as an optional `Provenance` for initialized memory.
//!
//! The `TypeRepresentation` trait is implemented on a given type in order to add axioms defining how that type can be encoded into and decoded from a `Seq<AbstractByte>`.
//! The trait is used to ensure that the encoding axioms satisfy certain validity properties, e.g. that the resulting byte sequence is the correct length for the value/type,
//! and that a value's encoding can be decoded back to the same value (see: <https://github.com/minirust/minirust/blob/master/spec/lang/representation.md#generic-properties>).
#![allow(unused_imports)]

use super::arithmetic::power::*;
use super::arithmetic::power2::*;
use super::endian::*;
use super::layout::*;
use super::math::*;
use super::prelude::*;
use super::raw_ptr::{shared_ref_ptr, Provenance};
use super::seq::*;
use crate::vstd::group_vstd_default;
use core::marker::{MetaSized, PhantomData};

verus! {

// https://github.com/minirust/minirust/blob/master/spec/mem/interface.md#abstract-bytes
// https://github.com/minirust/minirust/blob/master/spec/lang/representation.md
broadcast use {group_layout_axioms, group_vstd_default};

/// The Rust memory model treats memory as a sequence of abstract bytes. Each byte is uninitialized or initialized.
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
    /// then `Provenance::None` is returned.
    pub open spec fn shared_provenance(bytes: Seq<Self>) -> Provenance
        decreases bytes.len(),
    {
        if bytes.len() == 0 {
            Provenance::None
        } else if bytes.len() == 1 {
            bytes.last().provenance_or_null()
        } else {
            let last_p = bytes.last().provenance_or_null();
            if Self::shared_provenance(bytes.drop_last()) == last_p {
                last_p
            } else {
                Provenance::None
            }
        }
    }

    /// The byte value associated with this `AbstractByte`.
    pub open spec fn byte(self) -> u8
        recommends
            self is Init,
    {
        self->0
    }

    /// The optional `Provenance` associated with this `AbstractByte`.
    pub open spec fn provenance(self) -> Option<Provenance> {
        match self {
            AbstractByte::Init(_, p) => p,
            _ => None,
        }
    }

    /// The `Provenance` associated with this `AbstractByte`, if there is one, otherwise `Provenance::None`.
    pub open spec fn provenance_or_null(self) -> Provenance {
        match self.provenance() {
            Some(p) => p,
            _ => Provenance::None,
        }
    }
}

/// This trait is used to specify how values of a given type are encoded and decoded into a sequence of `AbstractByte`s.
/// The operations `encode` and `decode` are specified as relations because values may be associated with 
/// ghost members that are not represented in the abstract byte encoding.
///
/// Implementors of this trait must ensure that the specifications satisfy several properties by proving the lemmas on this trait.
/// While the specifications defined by implementations of this trait are trusted, these lemmas help check for unsound or vacuous specifications.
/// The required properties are:
/// (1) Any abstract byte sequence satisfying `encode` or `decode` is the correct size for the type, as specified by `size_of::<T>()`.
/// (2) Any `tracked` value of the type has at least one abstract byte sequence satisfying `encode`. 
/// This requirement is on `tracked` values only because this restricts lemma to values satisfying the type invariant.
/// (3) Any abstract byte sequence that encodes a value of the type must decode into the same value.
/// Note on definition ordering: the `requires`/`ensures` of the proof functions below are stated in the trait,
/// so Verus does not record that an implementation's proof functions depend on that implementation's own
/// spec functions (including inherited defaults such as `encode`/`decode`). Depending on the rest of the crate,
/// the spec function definitions may then be emitted after the proofs that need them.
/// As a workaround, implementations restate their postconditions in terms of `Self::encode`/`Self::decode`
/// in the proof bodies, which records the dependency.
pub trait TypeRepresentation where Self: MetaSized {
    /// Is encoding allowed for this type?
    /// Because `can_be_encoded` is a precondition for `abs_encode_impl` and `abs_can_be_encoded_impl`,
    /// this definition allows the encoding to be conditionally implement `abs_encode`, `abs_decode`, and `abs_can_be_encoded_impl`.
    spec fn can_be_encoded() -> bool;

    /// Does this type's abstract byte encoding depend on the value's shadow data?
    /// Shadow data is only observable for shared reference types, so this is `false` for
    /// almost every type. When it is `false`, `encode`/`decode` ignore their `shadow_data`
    /// argument entirely and the `*_no_shadow_data` forms below are the canonical ones.
    spec fn encoding_depends_on_shadow_data() -> bool;

    /// Can `value` be encoded to the given bytes, for a type whose encoding does not
    /// depend on shadow data? Only meaningful when `!encoding_depends_on_shadow_data()`.
    spec fn encode_no_shadow_data(value: &Self, bytes: Seq<AbstractByte>) -> bool;

    /// Can `value` and associated `shadow_data` be encoded to the given bytes?
    /// Only meaningful when `encoding_depends_on_shadow_data()`.
    spec fn encode_with_shadow_data(value: &Self, shadow_data: ShadowData<Self>, bytes: Seq<AbstractByte>) -> bool;

    /// Can the bytes be decoded to `value`, for a type whose encoding does not depend on
    /// shadow data? Only meaningful when `!encoding_depends_on_shadow_data()`.
    spec fn decode_no_shadow_data(bytes: Seq<AbstractByte>, value: &Self) -> bool;

    /// Can the bytes be decoded to `value` and associated `shadow_data`?
    /// Only meaningful when `encoding_depends_on_shadow_data()`.
    spec fn decode_with_shadow_data(bytes: Seq<AbstractByte>, value: &Self, shadow_data: ShadowData<Self>) -> bool;

    /// Can 'value' and associated `shadow_data` be encoded to the given bytes?
    /// Dispatches to the shadow-data-dependent or -independent definition for this type.
    open spec fn encode(value: &Self, shadow_data: ShadowData<Self>, bytes: Seq<AbstractByte>) -> bool {
        if Self::encoding_depends_on_shadow_data() {
            Self::encode_with_shadow_data(value, shadow_data, bytes)
        } else {
            Self::encode_no_shadow_data(value, bytes)
        }
    }

    /// Can the bytes be decoded to `value` and associated `shadow_data`?
    /// Dispatches to the shadow-data-dependent or -independent definition for this type.
    open spec fn decode(bytes: Seq<AbstractByte>, value: &Self, shadow_data: ShadowData<Self>) -> bool {
        if Self::encoding_depends_on_shadow_data() {
            Self::decode_with_shadow_data(bytes, value, shadow_data)
        } else {
            Self::decode_no_shadow_data(bytes, value)
        }
    }

    // Required properties for a valid encoding.
    /// If `encoding_depends_on_shadow_data()` is `false`, then the encoding really must not
    /// vary with the shadow data. This checks that an implementation has not misdeclared the
    /// flag, e.g. by overriding `encode`/`decode` with shadow-data-dependent definitions.
    proof fn encoding_independent_of_shadow_data(
        v: &Self,
        shadow_data1: ShadowData<Self>,
        shadow_data2: ShadowData<Self>,
        b: Seq<AbstractByte>,
    )
        requires
            !Self::encoding_depends_on_shadow_data(),
        ensures
            Self::encode(v, shadow_data1, b) == Self::encode(v, shadow_data2, b),
            Self::decode(b, v, shadow_data1) == Self::decode(b, v, shadow_data2),
    ;

    /// Any abstract byte encoding should be the correct length, determined by the size of this type.
    proof fn encoding_size(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>)
        requires
            Self::can_be_encoded(),
        ensures
            Self::encode(v, shadow_data, b) ==> b.len() == spec_size_of_val::<Self>(v),
            Self::decode(b, v, shadow_data) ==> b.len() == spec_size_of_val::<Self>(v),
    ;

    /// Every value should have at least one encoding. The `Self` argument is tracked to allow type invariants to be invoked.
    proof fn encoding_exists(tracked v: &Self, shadow_data: ShadowData<Self>) -> (b: Seq<AbstractByte>)
        requires
            Self::can_be_encoded(),
        ensures
            Self::encode(v, shadow_data, b),
    ;

    /// Any encoding should be able to be decoded back to the same value.
    proof fn encoding_invertible(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>)
        requires
            Self::encode(v, shadow_data, b),
            Self::can_be_encoded(),
        ensures
            Self::decode(b, v, shadow_data),
    ;
}

/// The abstract encoding for `bool` encodes the value as a single byte without provenance. On decoding, provenance is ignored.
impl TypeRepresentation for bool {
    open spec fn can_be_encoded() -> bool {
        true
    }

    open spec fn encoding_depends_on_shadow_data() -> bool {
        false
    }

    open spec fn encode_no_shadow_data(value: &bool, bytes: Seq<AbstractByte>) -> bool {
        &&& bytes.len() == 1
        &&& match bytes.first() {
            AbstractByte::Init(0, None) => !*value,
            AbstractByte::Init(1, None) => *value,
            _ => false,
        }
    }

    open spec fn encode_with_shadow_data(value: &bool, shadow_data: ShadowData<bool>, bytes: Seq<AbstractByte>) -> bool {
        arbitrary()
    }

    open spec fn decode_no_shadow_data(bytes: Seq<AbstractByte>, value: &bool) -> bool {
        &&& bytes.len() == 1
        &&& match bytes.first() {
            AbstractByte::Init(0, _) => !*value,
            AbstractByte::Init(1, _) => *value,
            _ => false,
        }
    }

    open spec fn decode_with_shadow_data(bytes: Seq<AbstractByte>, value: &bool, shadow_data: ShadowData<bool>) -> bool {
        arbitrary()
    }

    proof fn encoding_size(v: &bool, shadow_data: ShadowData<bool>, b: Seq<AbstractByte>) {
        // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
        assert(Self::encode(v, shadow_data, b) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
        assert(Self::decode(b, v, shadow_data) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
    }

    proof fn encoding_independent_of_shadow_data(
        v: &Self,
        shadow_data1: ShadowData<Self>,
        shadow_data2: ShadowData<Self>,
        b: Seq<AbstractByte>,
    ) {
        // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
        assert(Self::encode(v, shadow_data1, b) == Self::encode(v, shadow_data2, b));
        assert(Self::decode(b, v, shadow_data1) == Self::decode(b, v, shadow_data2));
    }

    proof fn encoding_exists(tracked v: &bool, shadow_data: ShadowData<bool>) -> (b: Seq<AbstractByte>) {
        let b = seq![
            AbstractByte::Init(
                if *v {
                    1
                } else {
                    0
                },
                None,
            ),
        ];
        // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
        assert(Self::encode(v, shadow_data, b));
        b
    }

    proof fn encoding_invertible(v: &bool, shadow_data: ShadowData<bool>, b: Seq<AbstractByte>) {
        // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
        assert(Self::decode(b, v, shadow_data));
    }
}

// We utilize the EndianNat type to transform an unsigned int to its byte representation.
/// Convert the given `EndianNat` representation to `AbtractByte`s with the given provenance.
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
        #![trigger endian_to_bytes(EndianNat::<u8>::from_nat(n, len), prov)]
        ({
            let endian = EndianNat::<u8>::from_nat(n, len);
            let bytes = endian_to_bytes(endian, prov);
            &&& bytes_to_endian(bytes) == endian
            &&& endian.len() == bytes.len() == len
            &&& AbstractByte::all_init(bytes)
            &&& endian.wf()
        }),
{
    broadcast use EndianNat::from_nat_properties;

    let endian = EndianNat::<u8>::from_nat(n, len);
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
            == Provenance::None,
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
            /// The type representation for `$int` encodes the value as a sequence of bytes of length `size_of::<$int>()`,
            /// with endianness matching the axiomatized `endianness()` for this platform, and without provenance.
            /// On decoding, provenance is ignored.
            impl TypeRepresentation for $int {
                open spec fn can_be_encoded() -> bool {
                    true
                }

                open spec fn encoding_depends_on_shadow_data() -> bool {
                    false
                }

                open spec fn encode_no_shadow_data(value: &$int, bytes: Seq<AbstractByte>) -> bool {
                    bytes == endian_to_bytes(
                        EndianNat::<u8>::from_nat(value as nat, size_of::<$int>()),
                        // integer types have no provenance
                        None,
                    )
                }

                open spec fn encode_with_shadow_data(value: &$int, shadow_data: ShadowData<$int>, bytes: Seq<AbstractByte>) -> bool {
                    arbitrary()
                }

                open spec fn decode_with_shadow_data(bytes: Seq<AbstractByte>, value: &$int, shadow_data: ShadowData<$int>) -> bool {
                    arbitrary()
                }

                open spec fn decode_no_shadow_data(bytes: Seq<AbstractByte>, value: &$int) -> bool {
                    // fail if any byte is uninitalized or if the byte sequence is not the necessary length
                    &&& bytes.len() == size_of::<$int>()
                    &&& AbstractByte::all_init(bytes)
                    &&& {
                        let endian = bytes_to_endian(bytes);
                        &&& endian.wf()
                        &&& (endian.to_nat() as $int) == value
                    }
                }

                proof fn encoding_size(v: &$int, shadow_data: ShadowData<$int>, b: Seq<AbstractByte>) {
                    broadcast use endian_to_bytes_to_endian;

                    unsigned_int_max_values();
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                    assert(Self::decode(b, v, shadow_data) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data1, b) == Self::encode(v, shadow_data2, b));
                    assert(Self::decode(b, v, shadow_data1) == Self::decode(b, v, shadow_data2));
                }

                proof fn encoding_exists(tracked v: &$int, shadow_data: ShadowData<$int>) -> (b: Seq<AbstractByte>) {
                    let b = endian_to_bytes(EndianNat::<u8>::from_nat(v as nat, size_of::<$int>()), None);
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b));
                    b
                }

                proof fn encoding_invertible(v: &$int, shadow_data: ShadowData<$int>, b: Seq<AbstractByte>) {
                    broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

                    unsigned_int_max_values();
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::decode(b, v, shadow_data));
                }
            }

            /// Useful properties about `$int::encode(v, bytes)`.
            pub broadcast proof fn $lemma_name(v: $int, bytes: Seq<AbstractByte>)
                requires
                    #[trigger] $int::encode(&v, arbitrary(), bytes),
                ensures
                    bytes.len() == size_of::<$int>(),
                    AbstractByte::all_init(bytes),
                    AbstractByte::shared_provenance(bytes) == Provenance::None,
                    bytes_to_endian(bytes).to_nat() as $int == v,
                    bytes_to_endian(bytes).wf(),
            {
                broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

                unsigned_int_max_values();
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
/// <https://en.wikipedia.org/wiki/Two%27s_complement#Subtraction_from_2N>
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
            /// The type representation for `$int` encodes the value as a sequence of bytes of length `size_of::<$int>()`,
            /// with endianness matching the axiomatized `endianness()` for this platform, and without provenance.
            /// Negative numbers are first converted to their unsigned bitwise equivalent and then encoded into bytes.
            /// On decoding, provenance is ignored.
            impl TypeRepresentation for $int {
                open spec fn can_be_encoded() -> bool {
                    true
                }

                open spec fn encoding_depends_on_shadow_data() -> bool {
                    false
                }

                open spec fn encode_no_shadow_data(value: &$int, bytes: Seq<AbstractByte>) -> bool {
                    bytes == endian_to_bytes(
                        EndianNat::<u8>::from_nat(signed_to_unsigned(value as int, size_of::<$int>()), size_of::<$int>()),
                        // integer types have no provenance
                        None,
                    )
                }

                open spec fn encode_with_shadow_data(value: &$int, shadow_data: ShadowData<$int>, bytes: Seq<AbstractByte>) -> bool {
                    arbitrary()
                }

                open spec fn decode_with_shadow_data(bytes: Seq<AbstractByte>, value: &$int, shadow_data: ShadowData<$int>) -> bool {
                    arbitrary()
                }

                open spec fn decode_no_shadow_data(bytes: Seq<AbstractByte>, value: &$int) -> bool {
                    // fail if any byte is uninitalized or if the byte sequence is not the necessary length
                    &&& bytes.len() == size_of::<$int>()
                    &&& AbstractByte::all_init(bytes)
                    &&& {
                        let endian = bytes_to_endian(bytes);
                        &&& endian.wf()
                        &&& endian.to_nat() == signed_to_unsigned(value as int, size_of::<$int>())
                    }
                }

                proof fn encoding_size(v: &$int, shadow_data: ShadowData<$int>, b: Seq<AbstractByte>) {
                    broadcast use endian_to_bytes_to_endian;

                    unsigned_int_max_values();
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                    assert(Self::decode(b, v, shadow_data) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data1, b) == Self::encode(v, shadow_data2, b));
                    assert(Self::decode(b, v, shadow_data1) == Self::decode(b, v, shadow_data2));
                }

                proof fn encoding_exists(tracked v: &$int, shadow_data: ShadowData<$int>) -> (b: Seq<AbstractByte>) {
                    let b = endian_to_bytes(EndianNat::<u8>::from_nat(signed_to_unsigned(v as int, size_of::<$int>()), size_of::<$int>()), None);
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b));
                    b
                }

                proof fn encoding_invertible(v: &$int, shadow_data: ShadowData<$int>, b: Seq<AbstractByte>) {
                    broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

                    unsigned_int_max_values();
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::decode(b, v, shadow_data));
                }
            }

            /// Useful properties about `$int::encode(v, bytes)`.
            pub broadcast proof fn $lemma_name(v: $int, bytes: Seq<AbstractByte>)
                requires
                    #[trigger] $int::encode(&v, arbitrary(), bytes),
                ensures
                    bytes.len() == size_of::<$int>(),
                    AbstractByte::all_init(bytes),
                    AbstractByte::shared_provenance(bytes) == Provenance::None,
                    bytes_to_endian(bytes).to_nat() == signed_to_unsigned(v as int, size_of::<$int>()),
                    bytes_to_endian(bytes).wf(),
            {
                broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

                unsigned_int_max_values()
            }

            pub broadcast proof fn $signed_to_unsigned_lemma_name(v: $int, w: $int)
                requires
                    #[trigger] signed_to_unsigned(v as int, size_of::<$int>()) == #[trigger] signed_to_unsigned(w as int, size_of::<$int>())
                ensures
                    v == w
            {
                signed_int_min_max_values();
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

/// Is there an `AbstractByte` encoding for this value?
pub open spec fn encoding_exists<T: TypeRepresentation>(value: T) -> bool {
    exists|bytes| #[trigger] T::encode(&value, arbitrary(), bytes)
}

/// Implements `AbstractByteEncodingFor` for raw pointers.
///
/// This encoding is intended to be shared across `*const T` and `*mut T`, as both types have the same layout 
/// (see: [Raw pointer type layout](https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer)).
/// The encoding is defined for `<T as core::ptr::Pointee>::Metadata: TypeRepresentation`.
///
/// *Note:* This encoding assumes that the pointer address is encoded first, followed by the pointer metadata. 
/// This is, to our knowledge, not a stable assumption.
///
/// The encoding for raw pointers is divided into two parts:
///
/// The first `size_of::<usize>()` bytes encode the pointer's address and per-byte provenance.
/// On decoding, all of the first `size_of::<usize>()` bytes must have the same provenance 
/// in order for the resulting pointer to have non-null provenance.
///
/// The next `size_of::<*mut T>() - size_of::<usize>()` bytes encode the pointer's metadata.
/// This is specified using `<<T as core::ptr::Pointee>::Metadata>::encode` and `<<T as core::ptr::Pointee>::Metadata>::decode`.
/// - For `T: Sized`, the metadata is always `()`, so the metadata encoding is a sequence of length 0.
///
/// The encoding for the pointer's metadata must not depend on the shadow data of the metadata. 
/// This is because there is no way to extract the shadow data from a spec-mode value of type `<T as core::ptr::Pointee>::Metadata`.
macro_rules! raw_ptr_encoding_from_type_representation {
    ($(
        ($mutability:tt, $lemma_name:ident);
    )+) => {$(
        verus! {
            impl<T: core::marker::PointeeSized> TypeRepresentation for *$mutability T where <T as core::ptr::Pointee>::Metadata: TypeRepresentation {
                open spec fn can_be_encoded() -> bool {
                    &&& <<T as core::ptr::Pointee>::Metadata as TypeRepresentation>::can_be_encoded()
                    // the metadata's encoding must not depend on shadow data, since a pointer's
                    // encoding carries no shadow data of its own to pass down to it
                    &&& !<<T as core::ptr::Pointee>::Metadata as TypeRepresentation>::encoding_depends_on_shadow_data()
                    &&& (forall |metadata| #[trigger] encoding_exists::<<T as core::ptr::Pointee>::Metadata>(metadata))
                }

                open spec fn encoding_depends_on_shadow_data() -> bool {
                    false
                }

                open spec fn encode_with_shadow_data(value: &Self, shadow_data: ShadowData<Self>, bytes: Seq<AbstractByte>) -> bool {
                    arbitrary()
                }

                open spec fn decode_with_shadow_data(bytes: Seq<AbstractByte>, value: &Self, shadow_data: ShadowData<Self>) -> bool {
                    arbitrary()
                }

                open spec fn encode_no_shadow_data(value: &Self, bytes: Seq<AbstractByte>) -> bool {
                    let prefix = bytes.subrange(0, size_of::<usize>() as int);
                    let suffix = bytes.subrange(size_of::<usize>() as int, size_of::<*mut T>() as int);
                    &&& bytes.len() == size_of::<*mut T>()
                    &&& prefix == endian_to_bytes(
                        EndianNat::<u8>::from_nat(value@.addr as nat, size_of::<usize>()),
                        // the abstract encoding preserves the provenance from this pointer
                        Some(value@.provenance),
                    )
                    &&& <<T as core::ptr::Pointee>::Metadata>::encode(&value@.metadata, arbitrary(), suffix)
                }

                open spec fn decode_no_shadow_data(bytes: Seq<AbstractByte>, value: &Self) -> bool {
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
                    &&& <<T as core::ptr::Pointee>::Metadata>::decode(suffix, &value@.metadata, arbitrary())
                }

                proof fn encoding_size(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                    assert(Self::decode(b, v, shadow_data) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data1, b) == Self::encode(v, shadow_data2, b));
                    assert(Self::decode(b, v, shadow_data1) == Self::decode(b, v, shadow_data2));
                }

                proof fn encoding_exists(tracked v: &Self, shadow_data: ShadowData<Self>) -> (b: Seq<AbstractByte>) {
                    let tracked m = *v as *mut T;
                    broadcast use endian_to_bytes_to_endian;

                    unsigned_int_max_values();
                    let prefix = endian_to_bytes(
                        EndianNat::<u8>::from_nat(v@.addr as nat, size_of::<usize>()),
                        Some(v@.provenance),
                    );

                    assert(encoding_exists::<<T as core::ptr::Pointee>::Metadata>(v@.metadata));
                    let suffix = choose|bytes|
                        <<T as core::ptr::Pointee>::Metadata>::encode(&v@.metadata, arbitrary(), bytes);
                    <<T as core::ptr::Pointee>::Metadata as TypeRepresentation>::encoding_size(
                        &v@.metadata,
                        arbitrary(),
                        suffix,
                    );
                    // the metadata type is `Sized`, so its value size is its type size
                    layout_of_sized::<<T as core::ptr::Pointee>::Metadata>(&v@.metadata);
                    let b = prefix.add(suffix);
                    assert(b.subrange(0, size_of::<usize>() as int) == prefix);
                    assert(b.subrange(size_of::<usize>() as int, size_of::<*mut T>() as int) == suffix);
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b));
                    b
                }

                proof fn encoding_invertible(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    broadcast use
                        EndianNat::from_nat_to_nat,
                        endian_to_bytes_to_endian,
                        endian_to_bytes_shared_provenance,
                    ;

                    unsigned_int_max_values();
                    <<T as core::ptr::Pointee>::Metadata as TypeRepresentation>::encoding_invertible(
                        &v@.metadata,
                        arbitrary(),
                        b.subrange(size_of::<usize>() as int, size_of::<*mut T>() as int),
                    );
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::decode(b, v, shadow_data));
                }
            }

            /// Useful properties for `<*$mutability T as TypeRepresentation>::encode(v, bytes)`.
            pub broadcast proof fn $lemma_name<T: ?Sized>(v: *$mutability T, bytes: Seq<AbstractByte>) where
                <T as core::ptr::Pointee>::Metadata: TypeRepresentation,
                requires
                    #[trigger] <*$mutability T as TypeRepresentation>::encode(&v, arbitrary(), bytes),
                    <*$mutability T as TypeRepresentation>::can_be_encoded()
                ensures
                    ({
                        let prefix = bytes.subrange(0, size_of::<usize>() as int);
                        let suffix = bytes.subrange(size_of::<usize>() as int, size_of::<*$mutability T>() as int);
                        &&& bytes.len() == size_of::<*$mutability T>()
                        &&& AbstractByte::all_init(prefix)
                        &&& AbstractByte::shared_provenance(prefix) == v@.provenance
                        &&& bytes_to_endian(prefix).to_nat() as usize == v@.addr
                        &&& bytes_to_endian(prefix).wf()
                        &&& <<T as core::ptr::Pointee>::Metadata>::encode(&v@.metadata, arbitrary(), suffix)
                        &&& <<T as core::ptr::Pointee>::Metadata>::decode(suffix, &v@.metadata, arbitrary())
                    }),
            {
                broadcast use
                    EndianNat::from_nat_to_nat,
                    endian_to_bytes_to_endian,
                    endian_to_bytes_shared_provenance,
                ;

                unsigned_int_max_values();

                let suffix = bytes.subrange(size_of::<usize>() as int, size_of::<*mut T>() as int);
                <<T as core::ptr::Pointee>::Metadata as TypeRepresentation>::encoding_invertible(
                    &v@.metadata,
                    arbitrary(),
                    suffix,
                );
            }
        }
    )+};
}

raw_ptr_encoding_from_type_representation! {
    (mut, mut_ptr_encode);
    (const, const_ptr_encode);
}

/// For `T: Sized`, `*mut T` and `*const T` can always be encoded.
pub broadcast proof fn sized_ptr_can_be_encoded<T: Sized>()
    ensures
        #![trigger <*mut T as TypeRepresentation>::can_be_encoded()] 
        #![trigger <*const T as TypeRepresentation>::can_be_encoded()] 
        <*mut T as TypeRepresentation>::can_be_encoded(),
        <*const T as TypeRepresentation>::can_be_encoded()
{
    assert forall|value| #[trigger]
        encoding_exists::<<T as core::ptr::Pointee>::Metadata>(value) by {
        assert(<<T as core::ptr::Pointee>::Metadata as TypeRepresentation>::encode(
            &value,
            arbitrary(),
            Seq::<AbstractByte>::empty(),
        ));
    }
}

/// For `T = [T]`, `*mut T` and `*const T` can always be encoded.
pub broadcast proof fn slice_ptr_can_be_encoded<T>()
    ensures
        #![trigger <*mut [T] as TypeRepresentation>::can_be_encoded()] 
        #![trigger <*const [T] as TypeRepresentation>::can_be_encoded()] 
        <*mut [T] as TypeRepresentation>::can_be_encoded(),
        <*const [T] as TypeRepresentation>::can_be_encoded()
{
    assert forall|value| #[trigger]
        encoding_exists::<usize>(value) by {
        broadcast use usize_encode;

        let bytes = endian_to_bytes(
            EndianNat::<u8>::from_nat(value as nat, size_of::<usize>()),
            None,
        );
        assert(<usize as TypeRepresentation>::encode(
            &value,
            arbitrary(),
            bytes,
        ));
    }
}

/// For `T = str`, `*mut T` and `*const T` can always be encoded.
pub broadcast proof fn str_ptr_can_be_encoded()
    ensures
        #![trigger <*mut str as TypeRepresentation>::can_be_encoded()] 
        #![trigger <*const str as TypeRepresentation>::can_be_encoded()] 
        <*mut str as TypeRepresentation>::can_be_encoded(),
        <*const str as TypeRepresentation>::can_be_encoded()
{
    broadcast use slice_ptr_can_be_encoded;

    assert(<*mut [u8] as TypeRepresentation>::can_be_encoded());
}

/// The layout for shared references is the same as that for pointers
/// (see: <https://doc.rust-lang.org/reference/type-layout.html#pointers-and-references-layout>).
/// See the documentation for `raw_ptr_encoding_from_type_representation`.
///
/// To implement this encoding, we rely on the shadow data of the shared reference to get the underlying pointer.
impl<T: ?Sized> TypeRepresentation for &T
    where <T as core::ptr::Pointee>::Metadata: TypeRepresentation
{
    open spec fn can_be_encoded() -> bool {
        <*const T as TypeRepresentation>::can_be_encoded()
    }

    // a shared reference's encoding is the encoding of the pointer it was derived from,
    // which is only recoverable from its shadow data
    open spec fn encoding_depends_on_shadow_data() -> bool {
        true
    }

    open spec fn encode_no_shadow_data(value: &Self, bytes: Seq<AbstractByte>) -> bool {
        arbitrary()
    }

    open spec fn decode_no_shadow_data(bytes: Seq<AbstractByte>, value: &Self) -> bool {
        arbitrary()
    }

    open spec fn encode_with_shadow_data(value: &Self, shadow_data: ShadowData<Self>, bytes: Seq<AbstractByte>) -> bool {
        <*const T as TypeRepresentation>::encode(&shared_ref_ptr(shadow_data), arbitrary(), bytes)
    }

    open spec fn decode_with_shadow_data(bytes: Seq<AbstractByte>, value: &Self, shadow_data: ShadowData<Self>) -> bool {
        <*const T as TypeRepresentation>::decode(bytes, &shared_ref_ptr(shadow_data), arbitrary())
    }

    proof fn encoding_size(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
        // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
        assert(Self::encode(v, shadow_data, b) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
        assert(Self::decode(b, v, shadow_data) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
    }

    proof fn encoding_independent_of_shadow_data(
        v: &Self,
        shadow_data1: ShadowData<Self>,
        shadow_data2: ShadowData<Self>,
        b: Seq<AbstractByte>,
    ) {
        // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
        assert(Self::encode(v, shadow_data1, b) == Self::encode(v, shadow_data2, b));
        assert(Self::decode(b, v, shadow_data1) == Self::decode(b, v, shadow_data2));
    }

    proof fn encoding_exists(tracked v: &Self, shadow_data: ShadowData<Self>) -> (b: Seq<AbstractByte>) {
        broadcast use endian_to_bytes_to_endian;

        unsigned_int_max_values();
        let prefix = endian_to_bytes(
            EndianNat::<u8>::from_nat(shared_ref_ptr(shadow_data)@.addr as nat, size_of::<usize>()),
            Some(shared_ref_ptr(shadow_data)@.provenance),
        );

        assert(encoding_exists::<<T as core::ptr::Pointee>::Metadata>(shared_ref_ptr(shadow_data)@.metadata));
        let suffix = choose|bytes| <<T as core::ptr::Pointee>::Metadata>::encode(&shared_ref_ptr(shadow_data)@.metadata, arbitrary(), bytes);
        <<T as core::ptr::Pointee>::Metadata as TypeRepresentation>::encoding_size(
            &shared_ref_ptr(shadow_data)@.metadata,
            arbitrary(),
            suffix,
        );
        // the metadata type is `Sized`, so its value size is its type size
        layout_of_sized::<<T as core::ptr::Pointee>::Metadata>(&shared_ref_ptr(shadow_data)@.metadata);
        let b = prefix.add(suffix);
        assert(b.subrange(0, size_of::<usize>() as int) == prefix);
        assert(b.subrange(size_of::<usize>() as int, size_of::<*mut T>() as int) == suffix);
        // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
        assert(Self::encode(v, shadow_data, b));
        b
    }

    proof fn encoding_invertible(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
        <*const T as TypeRepresentation>::encoding_invertible(&shared_ref_ptr(shadow_data), arbitrary(), b);
        // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
        assert(Self::decode(b, v, shadow_data));
    }
}

/// This trait can be implemented on types which are zero-sized and therefore have a trivial `AbstractByte` encoding (i.e., the empty sequence).
/// Intended to be used in conjunction with the `impl_type_representation_for_zero_sized_type` macro.
pub trait ZeroSizedTypeRepresentation where Self: Sized {
    proof fn layout_of_zero_sized_repr()
        ensures
            crate::vstd::layout::size_of::<Self>() == 0,
    ;
}

macro_rules! impl_type_representation_for_zero_sized_type {
    ($(
        ($name:ty, $spec_mod:tt);
    )+) => {$(
        verus! {
            /// The type representation for `$name` ensures that values of type `$name` are encoded and decoded as an empty sequence of abstract bytes.
            /// This is because `$name` is a zero-sized type.
            impl TypeRepresentation for $name {
                open spec fn can_be_encoded() -> bool {
                    true
                }

                open spec fn encoding_depends_on_shadow_data() -> bool {
                    false
                }

                $spec_mod spec fn encode_no_shadow_data(value: &Self, bytes: Seq<AbstractByte>) -> bool {
                    bytes == Seq::<AbstractByte>::empty()
                }

                $spec_mod spec fn encode_with_shadow_data(value: &Self, shadow_data: ShadowData<Self>, bytes: Seq<AbstractByte>) -> bool {
                    arbitrary()
                }

                $spec_mod spec fn decode_no_shadow_data(bytes: Seq<AbstractByte>, value: &Self) -> bool {
                    bytes == Seq::<AbstractByte>::empty()
                }

                $spec_mod spec fn decode_with_shadow_data(bytes: Seq<AbstractByte>, value: &Self, shadow_data: ShadowData<Self>) -> bool {
                    arbitrary()
                }

                proof fn encoding_size(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    <Self as ZeroSizedTypeRepresentation>::layout_of_zero_sized_repr();
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                    assert(Self::decode(b, v, shadow_data) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data1, b) == Self::encode(v, shadow_data2, b));
                    assert(Self::decode(b, v, shadow_data1) == Self::decode(b, v, shadow_data2));
                }

                proof fn encoding_exists(tracked v: &Self, shadow_data: ShadowData<Self>) -> (b: Seq<AbstractByte>) {
                    let b = Seq::<AbstractByte>::empty();
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b));
                    b
                }

                proof fn encoding_invertible(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::decode(b, v, shadow_data));
                }
            }
        }
    )+};
}

pub(crate) use impl_type_representation_for_zero_sized_type;

impl ZeroSizedTypeRepresentation for () {
    proof fn layout_of_zero_sized_repr() {
        broadcast use group_layout_axioms;

    }
}

impl_type_representation_for_zero_sized_type! {
    ((), open);
}

/// This trait is intended to be implemented on types a primitive type representation,
/// i.e. types defined with the `#[repr(<primitive>)]` attribute
/// (see: [Primitive representations](https://doc.rust-lang.org/reference/type-layout.html#primitive-representation-of-field-less-enums)).
/// Intended to be used in conjunction with the `impl_type_representation_for_primitive_repr` macro.
pub trait PrimitiveTypeRepresentation<Primitive: TypeRepresentation> where Self: Sized {
    spec fn to_primitive(v: Self) -> Primitive;

    proof fn to_primitive_tracked(tracked v: &Self) -> (tracked p: Primitive)
        ensures
            p == Self::to_primitive(*v),
    ;

    proof fn layout_of_primitive_repr()
        ensures
            crate::vstd::layout::size_of::<Self>() == crate::vstd::layout::size_of::<Primitive>(),
            crate::vstd::layout::align_of::<Self>() == crate::vstd::layout::align_of::<Primitive>(),
    ;
}

#[allow(unused_macros)]
macro_rules! impl_type_representation_for_primitive_repr {
    ($(
        ([$($generics:tt)*] $name:ty, [$($where_clause:tt)*], $spec_mod:tt, $primitive:ty);
    )+) => {$(
        verus! {
            /// The type representation for `$name` ensures that values of type `$name` are encoded and decoded 
            /// as specified in the type representation for the underlying `$primitive` value.
            /// This is because `$name` has a primitive type representation
            /// (see: [Primitive representations](https://doc.rust-lang.org/reference/type-layout.html#primitive-representation-of-field-less-enums)).
            impl<$($generics)*> TypeRepresentation for $name where $($where_clause)* {
                $spec_mod spec fn can_be_encoded() -> bool {
                    &&& <$primitive as TypeRepresentation>::can_be_encoded()
                    // the inner encoding must not depend on shadow data, since this wrapper's
                    // encoding carries no shadow data of its own to pass down to it
                    &&& !<$primitive as TypeRepresentation>::encoding_depends_on_shadow_data()
                }

                open spec fn encoding_depends_on_shadow_data() -> bool {
                    false
                }

                $spec_mod spec fn encode_with_shadow_data(value: &Self, shadow_data: ShadowData<Self>, bytes: Seq<AbstractByte>) -> bool {
                    arbitrary()
                }

                $spec_mod spec fn decode_with_shadow_data(bytes: Seq<AbstractByte>, value: &Self, shadow_data: ShadowData<Self>) -> bool {
                    arbitrary()
                }

                proof fn encoding_exists(tracked v: &Self, shadow_data: ShadowData<Self>) -> (b: Seq<AbstractByte>) {
                    let tracked p = <$name as PrimitiveTypeRepresentation<$primitive>>::to_primitive_tracked(v);
                    let b = <$primitive as TypeRepresentation>::encoding_exists(&p, arbitrary());
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b));
                    b
                }

                proof fn encoding_invertible(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    <$primitive as TypeRepresentation>::encoding_invertible(&<$name as PrimitiveTypeRepresentation<$primitive>>::to_primitive(*v), arbitrary(), b);
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::decode(b, v, shadow_data));
                }

                $spec_mod spec fn encode_no_shadow_data(value: &Self, bytes: Seq<AbstractByte>) -> bool {
                    <$primitive as TypeRepresentation>::encode(&<$name as PrimitiveTypeRepresentation<$primitive>>::to_primitive(*value), arbitrary(), bytes)
                }

                $spec_mod spec fn decode_no_shadow_data(bytes: Seq<AbstractByte>, value: &Self) -> bool {
                    <$primitive as TypeRepresentation>::decode(bytes, &<$name as PrimitiveTypeRepresentation<$primitive>>::to_primitive(*value), arbitrary())
                }

                proof fn encoding_size(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    <$name as PrimitiveTypeRepresentation<$primitive>>::layout_of_primitive_repr();
                    <$primitive as TypeRepresentation>::encoding_size(&<$name as PrimitiveTypeRepresentation<$primitive>>::to_primitive(*v), arbitrary(), b);
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                    assert(Self::decode(b, v, shadow_data) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data1, b) == Self::encode(v, shadow_data2, b));
                    assert(Self::decode(b, v, shadow_data1) == Self::decode(b, v, shadow_data2));
                }
            }
        }
    )+};
    ($(
        ($name:ty, $spec_mod:tt, $primitive:ty);
    )+) => {$(
        impl_type_representation_for_primitive_repr! {
            ([] $name, [], $spec_mod, $primitive);
        }
    )+};
}

pub(crate) use impl_type_representation_for_primitive_repr;

/// This trait is intended to be implemented on types a transparent type representation,
/// i.e. types defined with the `#[repr(<transparent>)]` attribute
/// (see: [Transparent representations](https://doc.rust-lang.org/reference/type-layout.html#the-transparent-representation)).
/// Intended to be used in conjunction with the `impl_type_representation_for_transparent_repr` macro.
pub trait TransparentTypeRepresentation<Inner: TypeRepresentation> where Self: Sized {
    spec fn to_inner(v: Self) -> Inner;

    proof fn to_inner_tracked(tracked v: &Self) -> (tracked i: Inner)
        ensures
            i == Self::to_inner(*v),
    ;

    proof fn layout_of_transparent_repr()
        ensures
            crate::vstd::layout::size_of::<Self>() == crate::vstd::layout::size_of::<Inner>(),
            crate::vstd::layout::align_of::<Self>() == crate::vstd::layout::align_of::<Inner>(),
    ;
}

#[allow(unused_macros)]
macro_rules! impl_type_representation_for_transparent_repr {
    ($(
        ([$($generics:tt)*] $name:ty, [$($where_clause:tt)*], $spec_mod:tt, $inner:ty);
    )+) => {$(
        verus! {
            /// The type representation for `$name` ensures that values of type `$name` are encoded and decoded 
            /// as specified in the type representation for the underlying `$inner` value.
            /// This is because `$name` has a transparent type representation
            /// (see: [Transparent representations](https://doc.rust-lang.org/reference/type-layout.html#the-transparent-representation)).
            impl<$($generics)*> TypeRepresentation for $name where $($where_clause)* {
                $spec_mod spec fn can_be_encoded() -> bool {
                    &&& <$inner as TypeRepresentation>::can_be_encoded()
                    // the inner encoding must not depend on shadow data, since this wrapper's
                    // encoding carries no shadow data of its own to pass down to it
                    &&& !<$inner as TypeRepresentation>::encoding_depends_on_shadow_data()
                }

                open spec fn encoding_depends_on_shadow_data() -> bool {
                    false
                }

                $spec_mod spec fn encode_with_shadow_data(value: &Self, shadow_data: ShadowData<Self>, bytes: Seq<AbstractByte>) -> bool {
                    arbitrary()
                }

                $spec_mod spec fn decode_with_shadow_data(bytes: Seq<AbstractByte>, value: &Self, shadow_data: ShadowData<Self>) -> bool {
                    arbitrary()
                }

                proof fn encoding_exists(tracked v: &Self, shadow_data: ShadowData<Self>) -> (b: Seq<AbstractByte>) {
                    let tracked i = <$name as TransparentTypeRepresentation<$inner>>::to_inner_tracked(v);
                    let b = <$inner as TypeRepresentation>::encoding_exists(&i, arbitrary());
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b));
                    b
                }

                proof fn encoding_invertible(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    <$inner as TypeRepresentation>::encoding_invertible(&<$name as TransparentTypeRepresentation<$inner>>::to_inner(*v), arbitrary(), b);
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::decode(b, v, shadow_data));
                }

                $spec_mod spec fn encode_no_shadow_data(value: &Self, bytes: Seq<AbstractByte>) -> bool {
                    <$inner as TypeRepresentation>::encode(&<$name as TransparentTypeRepresentation<$inner>>::to_inner(*value), arbitrary(), bytes)
                }

                $spec_mod spec fn decode_no_shadow_data(bytes: Seq<AbstractByte>, value: &Self) -> bool {
                    <$inner as TypeRepresentation>::decode(bytes, &<$name as TransparentTypeRepresentation<$inner>>::to_inner(*value), arbitrary())
                }

                proof fn encoding_size(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    <$name as TransparentTypeRepresentation<$inner>>::layout_of_transparent_repr();
                    <$inner as TypeRepresentation>::encoding_size(&<$name as TransparentTypeRepresentation<$inner>>::to_inner(*v), arbitrary(), b);
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                    assert(Self::decode(b, v, shadow_data) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data1, b) == Self::encode(v, shadow_data2, b));
                    assert(Self::decode(b, v, shadow_data1) == Self::decode(b, v, shadow_data2));
                }
            }
        }
    )+};
    ($(
        ($name:ty, $spec_mod:tt, $inner:ty);
    )+) => {$(
        impl_type_representation_for_transparent_repr! {
            ([] $name, [], $spec_mod, $inner);
        }
    )+};
}

pub(crate) use impl_type_representation_for_transparent_repr;

/// This trait is intended to be implemented on types with a scalar valid range, i.e. types defined with the
/// `#[rustc_layout_scalar_valid_range_start(...)]` and `#[rustc_layout_scalar_valid_range_end(...)]` attributes
/// (or, equivalently, a transparent wrapper around a pattern type such as `pattern_type!(u32 is 1..)`).
/// The compiler uses the valid range to perform the niche optimization (see: <https://doc.rust-lang.org/std/option/#representation>).
///
/// Such a type is represented exactly like its `Inner` type (see `TransparentTypeRepresentation`),
/// except that only `Inner` values within the valid range may be encoded or decoded.
/// `in_scalar_range` must hold exactly for the `Inner` values in the type's valid range.
/// Intended to be used in conjunction with the `impl_type_representation_for_scalar_range_repr` macro.
pub trait ScalarRangeTypeRepresentation<Inner: TypeRepresentation>: TransparentTypeRepresentation<Inner> {
    /// Does the `Inner` value lie within the valid scalar range for `Self`?
    spec fn in_scalar_range(v: Inner) -> bool;

    /// Every value of `Self` lies within the valid scalar range. The `Self` argument is tracked to allow type invariants to be invoked.
    proof fn valid_scalar_range_repr(tracked v: &Self)
        ensures
            Self::in_scalar_range(Self::to_inner(*v)),
    ;
}

#[allow(unused_macros)]
macro_rules! impl_type_representation_for_scalar_range_repr {
    ($(
        ([$($generics:tt)*] $name:ty, [$($where_clause:tt)*], $spec_mod:tt, $inner:ty);
    )+) => {$(
        verus! {
            /// The type representation for `$name` ensures that values of type `$name` are encoded and decoded
            /// as specified in the type representation for the underlying `$inner` value,
            /// provided that the `$inner` value lies within the valid scalar range for `$name`.
            impl<$($generics)*> TypeRepresentation for $name where $($where_clause)* {
                $spec_mod spec fn can_be_encoded() -> bool {
                    &&& <$inner as TypeRepresentation>::can_be_encoded()
                    // the inner encoding must not depend on shadow data, since this wrapper's
                    // encoding carries no shadow data of its own to pass down to it
                    &&& !<$inner as TypeRepresentation>::encoding_depends_on_shadow_data()
                }

                open spec fn encoding_depends_on_shadow_data() -> bool {
                    false
                }

                $spec_mod spec fn encode_with_shadow_data(value: &Self, shadow_data: ShadowData<Self>, bytes: Seq<AbstractByte>) -> bool {
                    arbitrary()
                }

                $spec_mod spec fn decode_with_shadow_data(bytes: Seq<AbstractByte>, value: &Self, shadow_data: ShadowData<Self>) -> bool {
                    arbitrary()
                }

                proof fn encoding_exists(tracked v: &Self, shadow_data: ShadowData<Self>) -> (b: Seq<AbstractByte>) {
                    <$name as ScalarRangeTypeRepresentation<$inner>>::valid_scalar_range_repr(v);
                    let tracked i = <$name as TransparentTypeRepresentation<$inner>>::to_inner_tracked(v);
                    let b = <$inner as TypeRepresentation>::encoding_exists(&i, arbitrary());
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b));
                    b
                }

                proof fn encoding_invertible(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    <$inner as TypeRepresentation>::encoding_invertible(&<$name as TransparentTypeRepresentation<$inner>>::to_inner(*v), arbitrary(), b);
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::decode(b, v, shadow_data));
                }

                $spec_mod spec fn encode_no_shadow_data(value: &Self, bytes: Seq<AbstractByte>) -> bool {
                    let inner = <$name as TransparentTypeRepresentation<$inner>>::to_inner(*value);
                    &&& <$inner as TypeRepresentation>::encode(&inner, arbitrary(), bytes)
                    &&& <$name as ScalarRangeTypeRepresentation<$inner>>::in_scalar_range(inner)
                }

                $spec_mod spec fn decode_no_shadow_data(bytes: Seq<AbstractByte>, value: &Self) -> bool {
                    let inner = <$name as TransparentTypeRepresentation<$inner>>::to_inner(*value);
                    &&& <$inner as TypeRepresentation>::decode(bytes, &inner, arbitrary())
                    &&& <$name as ScalarRangeTypeRepresentation<$inner>>::in_scalar_range(inner)
                }

                proof fn encoding_size(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    <$name as TransparentTypeRepresentation<$inner>>::layout_of_transparent_repr();
                    <$inner as TypeRepresentation>::encoding_size(&<$name as TransparentTypeRepresentation<$inner>>::to_inner(*v), arbitrary(), b);
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data, b) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                    assert(Self::decode(b, v, shadow_data) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
                    // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
                    assert(Self::encode(v, shadow_data1, b) == Self::encode(v, shadow_data2, b));
                    assert(Self::decode(b, v, shadow_data1) == Self::decode(b, v, shadow_data2));
                }
            }
        }
    )+};
    ($(
        ($name:ty, $spec_mod:tt, $inner:ty);
    )+) => {$(
        impl_type_representation_for_scalar_range_repr! {
            ([] $name, [], $spec_mod, $inner);
        }
    )+};
}

pub(crate) use impl_type_representation_for_scalar_range_repr;

// TODO: Define type representation for any slice.

/// The abstract encoding for a `[u8]` maps each value in the slice to a corresponding abtract byte with no provenance.
impl TypeRepresentation for [u8] {
    open spec fn can_be_encoded() -> bool {
        true
    }

    open spec fn encoding_depends_on_shadow_data() -> bool {
        false
    }

    open spec fn encode_no_shadow_data(value: &[u8], bytes: Seq<AbstractByte>) -> bool {
        &&& value@.len() == bytes.len()
        &&& forall|i| #![trigger value@[i]] 0 <= i < value@.len() ==> u8::encode(&value@[i], arbitrary(), seq![bytes[i]])
    }

    open spec fn encode_with_shadow_data(value: &[u8], shadow_data: ShadowData<[u8]>, bytes: Seq<AbstractByte>) -> bool {
        arbitrary()
    }

    open spec fn decode_no_shadow_data(bytes: Seq<AbstractByte>, value: &[u8]) -> bool {
        &&& value@.len() == bytes.len()
        &&& forall|i| #![trigger value@[i]] 0 <= i < value@.len() ==> u8::decode(seq![bytes[i]], &value@[i], arbitrary())
    }

    open spec fn decode_with_shadow_data(bytes: Seq<AbstractByte>, value: &[u8], shadow_data: ShadowData<[u8]>) -> bool {
        arbitrary()
    }

    proof fn encoding_independent_of_shadow_data(
        v: &[u8],
        shadow_data1: ShadowData<[u8]>,
        shadow_data2: ShadowData<[u8]>,
        b: Seq<AbstractByte>,
    ) {
        // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
        assert(Self::encode(v, shadow_data1, b) == Self::encode(v, shadow_data2, b));
        assert(Self::decode(b, v, shadow_data1) == Self::decode(b, v, shadow_data2));
    }

    proof fn encoding_size(v: &[u8], shadow_data: ShadowData<[u8]>, b: Seq<AbstractByte>) {
        // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
        assert(Self::encode(v, shadow_data, b) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
        assert(Self::decode(b, v, shadow_data) ==> b.len() == crate::vstd::layout::spec_size_of_val::<Self>(v));
    }

    proof fn encoding_exists(tracked v: &[u8], shadow_data: ShadowData<[u8]>) -> (b: Seq<AbstractByte>) {
        broadcast use endian_to_bytes_to_endian, EndianNat::from_nat_to_nat;

        unsigned_int_max_values();
        let bytes = v@.map_values(
            |e| endian_to_bytes(EndianNat::<u8>::from_nat(e as nat, size_of::<u8>()), None)[0],
        );
        assert forall|i| #![trigger v@[i]] 0 <= i < v@.len() implies u8::encode(&v@[i], arbitrary(), seq![bytes[i]]) by {
            assert(seq![bytes[i]] == endian_to_bytes(
                EndianNat::<u8>::from_nat(v@[i] as nat, size_of::<u8>()),
                None,
            ));
        }
        let b = bytes;
        // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
        assert(Self::encode(v, shadow_data, b));
        b
    }

    proof fn encoding_invertible(v: &[u8], shadow_data: ShadowData<[u8]>, b: Seq<AbstractByte>) {
        assert forall|i| #![trigger v@[i]] 0 <= i < v@.len() implies u8::decode(seq![b[i]], &v@[i], arbitrary()) by {
            u8::encoding_invertible(&v@[i], arbitrary(), seq![b[i]]);
        }
        // Workaround for a Verus definition-ordering issue (see note on `TypeRepresentation`)
        assert(Self::decode(b, v, shadow_data));
    }
}

/// True when all `AbstractByte` encodings of `src` and `src_shadow_data` can be decoded to `dst` and `dst_shadow_data`.
pub open spec fn encode_decode<T: ?Sized + TypeRepresentation, U: ?Sized + TypeRepresentation>(src: &T, src_shadow_data: ShadowData<T>, dst: &U, dst_shadow_data: ShadowData<U>) -> bool {
    &&& forall|bytes|
        #![trigger <T as TypeRepresentation>::encode(src, src_shadow_data, bytes)]
        #![trigger <U as TypeRepresentation>::decode(bytes, dst, dst_shadow_data)]
        <T as TypeRepresentation>::encode(src, src_shadow_data, bytes) ==> <U as TypeRepresentation>::decode(bytes, dst, dst_shadow_data)
}

/// True when for any `AbstractByte` sequence, if that sequence can be decoded to `src` and `src_shadow_data`,
/// then it can also decoded to `dst` and `dst_shadow_data`.
pub open spec fn decode_decode<T: ?Sized + TypeRepresentation, U: ?Sized + TypeRepresentation>(src: &T, src_shadow_data: ShadowData<T>, dst: &U, dst_shadow_data: ShadowData<U>) -> bool {
    &&& forall|bytes|
        #![trigger <T as TypeRepresentation>::decode(bytes, src, src_shadow_data)]
        #![trigger <U as TypeRepresentation>::decode(bytes, dst, dst_shadow_data)]
        <T as TypeRepresentation>::decode(bytes, src, src_shadow_data) ==> <U as TypeRepresentation>::decode(bytes, dst, dst_shadow_data)
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
    mut_ptr_encode,
    const_ptr_encode,
    sized_ptr_can_be_encoded,
    slice_ptr_can_be_encoded,
    str_ptr_can_be_encoded,
}

} // verus!
