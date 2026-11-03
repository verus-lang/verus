//! This module defines (i.e., axiomatizes) the Rust abstract machine's representation for many primitive types (integers, boolean, raw pointers, shared references, slices),
//! as well as helpers for defining the representation for structs and enums derived from these primitive types.
//!
//! The representation is defined on a `Seq<AbstractByte>`, which encodes byte values as well as an optional `Provenance` for initialized memory.
//!
//! The `TypeRepresentation` trait is implemented on a given type in order to add axioms defining how that type can be encoded into and decoded from a `Seq<AbstractByte>`.
//! The trait is used to ensure that the encoding axioms satisfy certain validity properties, e.g. that the resulting byte sequence is the correct length for the value/type,
//! and that a value's encoding can be decoded back to the same value (see: <https://github.com/minirust/minirust/blob/master/spec/lang/representation.md#generic-properties>).
#![allow(unused_imports)]

use super::arithmetic::mul::*;
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
broadcast use {group_layout_axioms, super::seq::group_seq_axioms};

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
    }

    proof fn encoding_independent_of_shadow_data(
        v: &Self,
        shadow_data1: ShadowData<Self>,
        shadow_data2: ShadowData<Self>,
        b: Seq<AbstractByte>,
    ) {
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
        b
    }

    proof fn encoding_invertible(v: &bool, shadow_data: ShadowData<bool>, b: Seq<AbstractByte>) {
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
    broadcast use group_vstd_default;
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
    broadcast use group_vstd_default;

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
    broadcast use group_vstd_default;

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

                open spec fn encode(value: &Self, shadow_data: ShadowData<Self>, bytes: Seq<AbstractByte>) -> bool {
                    if Self::encoding_depends_on_shadow_data() {
                        Self::encode_with_shadow_data(value, shadow_data, bytes)
                    } else {
                        Self::encode_no_shadow_data(value, bytes)
                    }
                }

                open spec fn decode(bytes: Seq<AbstractByte>, value: &Self, shadow_data: ShadowData<Self>) -> bool {
                    if Self::encoding_depends_on_shadow_data() {
                        Self::decode_with_shadow_data(bytes, value, shadow_data)
                    } else {
                        Self::decode_no_shadow_data(bytes, value)
                    }
                }

                proof fn encoding_size(v: &$int, shadow_data: ShadowData<$int>, b: Seq<AbstractByte>) {
                    broadcast use endian_to_bytes_to_endian;

                    unsigned_int_max_values();
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
                }

                proof fn encoding_exists(tracked v: &$int, shadow_data: ShadowData<$int>) -> (b: Seq<AbstractByte>) {
                    endian_to_bytes(EndianNat::<u8>::from_nat(v as nat, size_of::<$int>()), None)
                }

                proof fn encoding_invertible(v: &$int, shadow_data: ShadowData<$int>, b: Seq<AbstractByte>) {
                    broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

                    unsigned_int_max_values();
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
                broadcast use group_vstd_default;
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

/// Types where every initialized byte sequence of length `size_of::<Self>()` decodes to a valid value of that type.
/// This value is given by the natural number represented by the byte values
/// (with respect to the endianness of the platform),
/// regardless of any provenance the bytes carry.
///
/// Implemented by the unsigned primitive integers: `u8`, `u16`, `u32`, `u64`, `u128` and `usize`.
/// Note that raw pointers are *not* included, since their bytes do carry provenance;
/// similarly, signed integers are also excluded, since they are represented using two's complement.
pub trait DecodesToNat: TypeRepresentation + BasePow2 + Integer {
    /// Constructs a `Self` from a natural number `n`, for `n` below `Self::base()`.
    // Needed so `lemma_from_nat` can name the value:
    // `exists|v: Self| v as int == n` has no valid trigger.
    spec fn from_nat(n: nat) -> Self
        recommends
            n < Self::base(),
    ;

    /// The bytes decode to `v` exactly when they are `size_of::<Self>()` initialized bytes
    /// whose `EndianNat` is `v`.
    /// The encoding does not depend on shadow data.
    proof fn lemma_decode(bytes: Seq<AbstractByte>, v: Self)
        ensures
            !Self::encoding_depends_on_shadow_data(),
            Self::decode(bytes, &v, arbitrary()) <==> {
                &&& bytes.len() == size_of::<Self>()
                &&& AbstractByte::all_init(bytes)
                &&& bytes_to_endian(bytes).wf()
                &&& bytes_to_endian(bytes).to_nat() == v as int
            },
    ;

    /// A value fills its `size_of::<Self>()` bytes:
    /// it has 8 bits per byte, so its base is 256 to the power of its size.
    proof fn lemma_base_size()
        ensures
            Self::bits() == 8 * size_of::<Self>(),
            Self::base() == pow(u8::base() as int, size_of::<Self>()),
    ;

    /// Every natural number below `Self::base()` is the value of some `Self`.
    proof fn lemma_from_nat(n: nat)
        requires
            n < Self::base(),
        ensures
            Self::from_nat(n) as int == n,
    ;
}

macro_rules! decodes_to_nat {
    ($($uint:ty),+) => {$(
        verus! {
            impl DecodesToNat for $uint {
                proof fn lemma_decode(bytes: Seq<AbstractByte>, v: Self) {
                    broadcast use layout_of_primitives;

                    unsigned_int_max_values();
                    let endian = bytes_to_endian(bytes);
                    if bytes.len() == size_of::<$uint>() && endian.wf() {
                        endian.to_nat_properties();
                    }
                }

                proof fn lemma_base_size() {
                    broadcast use layout_of_primitives;

                    unsigned_int_max_values();
                }

                open spec fn from_nat(n: nat) -> Self {
                    n as $uint
                }

                proof fn lemma_from_nat(n: nat) {
                }
            }
        }
    )+};
}

decodes_to_nat!(u8, u16, u32, u64, u128, usize);

/// The bytes of `digits.len()` consecutive `B`s, each decoding to its digit,
/// are initialized, and their `EndianNat` is the digits' `EndianNat` in base `B`.
proof fn lemma_bytes_to_endian_digits<B: DecodesToNat>(bytes: Seq<AbstractByte>, digits: Seq<B>)
    requires
        bytes.len() == digits.len() * size_of::<B>(),
        forall|i: int| 0 <= i < digits.len() ==> #[trigger] B::decode(
            bytes.subrange(i * size_of::<B>(), (i + 1) * size_of::<B>()),
            &digits[i],
            arbitrary(),
        ),
    ensures
        AbstractByte::all_init(bytes),
        EndianNat::<B>::in_bounds(digits.map(|i, d| d as int)),
        bytes_to_endian(bytes).to_nat() == to_endian_from_digits(digits).to_nat(),
    decreases digits.len(),
{
    reveal(EndianNat::to_nat);
    let s = size_of::<B>() as int;
    let k = digits.len() as int;
    B::lemma_base_size();
    if k == 0 {
        assert(bytes.len() == 0) by (nonlinear_arith)
            requires
                bytes.len() == k * s,
                k == 0,
        ;
    } else {
        assert(0 <= s <= k * s && (k - 1) * s == k * s - s) by (nonlinear_arith)
            requires
                k > 0,
                s >= 0,
        ;
        // The chunk of the least significant digit, and the rest
        let (least_i, least, rest, rest_digits) = match endianness() {
            Endian::Little => (0int, bytes.subrange(0, s), bytes.subrange(s, k * s), digits.skip(1)),
            Endian::Big => (k - 1, bytes.subrange(k * s - s, k * s), bytes.subrange(0, k * s - s), digits.drop_last()),
        };
        assert forall|i: int| 0 <= i < k - 1 implies #[trigger] B::decode(
            rest.subrange(i * s, (i + 1) * s),
            &rest_digits[i],
            arbitrary(),
        ) by {
            assert((i + 1) * s == i * s + s && (i + 2) * s == (i + 1) * s + s && 0 <= i * s
                && (i + 2) * s <= k * s) by (nonlinear_arith)
                requires
                    0 <= i < k - 1,
                    s >= 0,
            ;
            let j = if endianness() is Little { i + 1 } else { i };
            assert(rest.subrange(i * s, (i + 1) * s) =~= bytes.subrange(j * s, (j + 1) * s));
        }
        lemma_bytes_to_endian_digits(rest, rest_digits);
        lemma_mul_is_distributive_add_other_way(s, least_i, 1);
        lemma_mul_is_distributive_sub_other_way(s, k, 1);
        lemma_mul_basics(s);
        assert(least =~= bytes.subrange(least_i * s, (least_i + 1) * s));
        B::lemma_decode(least, digits[least_i]);
        bytes_to_endian(least).to_nat_properties();

        // The bytes are the rest's bytes with the least chunk appended in the least significant position
        let e = bytes_to_endian(bytes);
        let e_rest = bytes_to_endian(rest);
        let e_least = bytes_to_endian(least);
        assert(e =~= e_rest.append_least(e_least));
        EndianNat::<u8>::to_nat_append_least(e_rest, e_least);

        // The digits are the rest's digits with the least digit in the least significant position
        let d = to_endian_from_digits(digits);
        assert(d.drop_least() =~= to_endian_from_digits(rest_digits));
        assert forall|i: int| 0 <= i < k implies 0 <= #[trigger] d.digits[i] < B::base() by {
            if i != least_i {
                let j = if endianness() is Little { i - 1 } else { i };
                assert(to_endian_from_digits(rest_digits).digits[j] == d.digits[i]);
            }
        }
        assert(bytes =~= if endianness() is Little { least + rest } else { rest + least });
    }
}

/// If the bytes decode to `digits` (one `B` per `size_of::<B>()` bytes),
/// they decode to the `BIG` whose digits are `digits`.
pub proof fn lemma_decode_to_big<BIG, B>(bytes: Seq<AbstractByte>, digits: Seq<B>, v: BIG)
    where BIG: DecodesToNat, B: DecodesToNat + CompatibleSmallerBaseFor<BIG>
    requires
        digits.len() * size_of::<B>() == size_of::<BIG>(),
        bytes.len() == size_of::<BIG>(),
        forall|i: int| 0 <= i < digits.len() ==> #[trigger] B::decode(
            bytes.subrange(i * size_of::<B>(), (i + 1) * size_of::<B>()),
            &digits[i],
            arbitrary(),
        ),
        v as int == to_big_from_digits::<BIG, B>(digits).index(0),
    ensures
        BIG::decode(bytes, &v, arbitrary()),
{
    lemma_bytes_to_endian_digits(bytes, digits);
    B::lemma_base_size();
    BIG::lemma_base_size();
    B::bits_to_base();
    // `digits` is one digit in base `BIG`
    assert(digits.len() == EndianNat::<B>::exp::<BIG>()) by {
        let k = digits.len() as int;
        let s = size_of::<B>() as int;
        assert(s > 0) by (nonlinear_arith)
            requires
                B::bits() == 8 * s,
                B::bits() > 1,
        ;
        assert((8 * (k * s)) / (8 * s) == k) by (nonlinear_arith)
            requires
                s > 0,
        ;
    }
    broadcast use EndianNat::exp_properties;

    to_big_from_digits_single::<BIG, B>(digits);
    BIG::lemma_decode(bytes, v);
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

                open spec fn encode(value: &Self, shadow_data: ShadowData<Self>, bytes: Seq<AbstractByte>) -> bool {
                    if Self::encoding_depends_on_shadow_data() {
                        Self::encode_with_shadow_data(value, shadow_data, bytes)
                    } else {
                        Self::encode_no_shadow_data(value, bytes)
                    }
                }

                open spec fn decode(bytes: Seq<AbstractByte>, value: &Self, shadow_data: ShadowData<Self>) -> bool {
                    if Self::encoding_depends_on_shadow_data() {
                        Self::decode_with_shadow_data(bytes, value, shadow_data)
                    } else {
                        Self::decode_no_shadow_data(bytes, value)
                    }
                }

                proof fn encoding_size(v: &$int, shadow_data: ShadowData<$int>, b: Seq<AbstractByte>) {
                    broadcast use endian_to_bytes_to_endian;

                    unsigned_int_max_values();
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
                }

                proof fn encoding_exists(tracked v: &$int, shadow_data: ShadowData<$int>) -> (b: Seq<AbstractByte>) {
                    endian_to_bytes(EndianNat::<u8>::from_nat(signed_to_unsigned(v as int, size_of::<$int>()), size_of::<$int>()), None)
                }

                proof fn encoding_invertible(v: &$int, shadow_data: ShadowData<$int>, b: Seq<AbstractByte>) {
                    broadcast use EndianNat::from_nat_to_nat, endian_to_bytes_to_endian;

                    unsigned_int_max_values();
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
                broadcast use group_vstd_default;
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

                open spec fn encode(value: &Self, shadow_data: ShadowData<Self>, bytes: Seq<AbstractByte>) -> bool {
                    if Self::encoding_depends_on_shadow_data() {
                        Self::encode_with_shadow_data(value, shadow_data, bytes)
                    } else {
                        Self::encode_no_shadow_data(value, bytes)
                    }
                }

                open spec fn decode(bytes: Seq<AbstractByte>, value: &Self, shadow_data: ShadowData<Self>) -> bool {
                    if Self::encoding_depends_on_shadow_data() {
                        Self::decode_with_shadow_data(bytes, value, shadow_data)
                    } else {
                        Self::decode_no_shadow_data(bytes, value)
                    }
                }

                proof fn encoding_size(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
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
    }

    proof fn encoding_independent_of_shadow_data(
        v: &Self,
        shadow_data1: ShadowData<Self>,
        shadow_data2: ShadowData<Self>,
        b: Seq<AbstractByte>,
    ) {
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
        b
    }

    proof fn encoding_invertible(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
        <*const T as TypeRepresentation>::encoding_invertible(&shared_ref_ptr(shadow_data), arbitrary(), b);
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

                open spec fn encode(value: &Self, shadow_data: ShadowData<Self>, bytes: Seq<AbstractByte>) -> bool {
                    if Self::encoding_depends_on_shadow_data() {
                        Self::encode_with_shadow_data(value, shadow_data, bytes)
                    } else {
                        Self::encode_no_shadow_data(value, bytes)
                    }
                }

                open spec fn decode(bytes: Seq<AbstractByte>, value: &Self, shadow_data: ShadowData<Self>) -> bool {
                    if Self::encoding_depends_on_shadow_data() {
                        Self::decode_with_shadow_data(bytes, value, shadow_data)
                    } else {
                        Self::decode_no_shadow_data(bytes, value)
                    }
                }

                proof fn encoding_size(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    <Self as ZeroSizedTypeRepresentation>::layout_of_zero_sized_repr();
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
                }

                proof fn encoding_exists(tracked v: &Self, shadow_data: ShadowData<Self>) -> (b: Seq<AbstractByte>) {
                    Seq::<AbstractByte>::empty()
                }

                proof fn encoding_invertible(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
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
                    <$primitive as TypeRepresentation>::encoding_exists(&p, arbitrary())
                }

                proof fn encoding_invertible(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    <$primitive as TypeRepresentation>::encoding_invertible(&<$name as PrimitiveTypeRepresentation<$primitive>>::to_primitive(*v), arbitrary(), b);
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
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
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
                    <$inner as TypeRepresentation>::encoding_exists(&i, arbitrary())
                }

                proof fn encoding_invertible(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    <$inner as TypeRepresentation>::encoding_invertible(&<$name as TransparentTypeRepresentation<$inner>>::to_inner(*v), arbitrary(), b);
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
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
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
                    <$inner as TypeRepresentation>::encoding_exists(&i, arbitrary())
                }

                proof fn encoding_invertible(v: &Self, shadow_data: ShadowData<Self>, b: Seq<AbstractByte>) {
                    <$inner as TypeRepresentation>::encoding_invertible(&<$name as TransparentTypeRepresentation<$inner>>::to_inner(*v), arbitrary(), b);
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
                }

                proof fn encoding_independent_of_shadow_data(
                    v: &Self,
                    shadow_data1: ShadowData<Self>,
                    shadow_data2: ShadowData<Self>,
                    b: Seq<AbstractByte>,
                ) {
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

/// The abstract encoding for a `[T]` encodes `T` elements in sequence.
/// Encoding `[T]` is only supported for types `T` whose encoding does not depend on shadow data.
impl<T: TypeRepresentation> TypeRepresentation for [T] {
    open spec fn can_be_encoded() -> bool {
        &&& T::can_be_encoded()
        &&& !T::encoding_depends_on_shadow_data()
    }

    open spec fn encoding_depends_on_shadow_data() -> bool {
        T::encoding_depends_on_shadow_data()
    }

    open spec fn encode_no_shadow_data(value: &[T], bytes: Seq<AbstractByte>) -> bool {
        &&& bytes.len() == value@.len() * size_of::<T>()
        &&& forall|i: int| #![trigger value@[i]] 0 <= i < value@.len() ==> T::encode(
            &value@[i],
            arbitrary(),
            bytes.subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
        )
    }

    open spec fn encode_with_shadow_data(value: &[T], shadow_data: ShadowData<[T]>, bytes: Seq<AbstractByte>) -> bool {
        arbitrary()
    }

    open spec fn decode_no_shadow_data(bytes: Seq<AbstractByte>, value: &[T]) -> bool {
        &&& bytes.len() == value@.len() * size_of::<T>()
        &&& forall|i: int| #![trigger value@[i]] 0 <= i < value@.len() ==> T::decode(
            bytes.subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
            &value@[i],
            arbitrary(),
        )
    }

    open spec fn decode_with_shadow_data(bytes: Seq<AbstractByte>, value: &[T], shadow_data: ShadowData<[T]>) -> bool {
        arbitrary()
    }

    proof fn encoding_independent_of_shadow_data(
        v: &[T],
        shadow_data1: ShadowData<[T]>,
        shadow_data2: ShadowData<[T]>,
        b: Seq<AbstractByte>,
    ) {
    }

    proof fn encoding_size(v: &[T], shadow_data: ShadowData<[T]>, b: Seq<AbstractByte>) {
        broadcast use layout_of_slices;

    }

    proof fn encoding_exists(tracked v: &[T], shadow_data: ShadowData<[T]>) -> (b: Seq<AbstractByte>) {
        slice_encoding_exists_prefix(v, v@.len() as int)
    }

    proof fn encoding_invertible(v: &[T], shadow_data: ShadowData<[T]>, b: Seq<AbstractByte>) {
        let s = size_of::<T>() as int;
        assert forall|i: int| #![trigger v@[i]] 0 <= i < v@.len() implies T::decode(
            b.subrange(i * s, (i + 1) * s),
            &v@[i],
            arbitrary(),
        ) by {
            T::encoding_invertible(&v@[i], arbitrary(), b.subrange(i * s, (i + 1) * s));
        }
    }
}

/// Encodes the first `n` elements of `v`, one `size_of::<T>()`-byte slot per element.
proof fn slice_encoding_exists_prefix<T: TypeRepresentation>(tracked v: &[T], n: int) -> (b: Seq<
    AbstractByte,
>)
    requires
        T::can_be_encoded(),
        !T::encoding_depends_on_shadow_data(),
        0 <= n <= v@.len(),
    ensures
        b.len() == n * size_of::<T>(),
        forall|i: int| #![trigger v@[i]] 0 <= i < n ==> T::encode(
            &v@[i],
            arbitrary(),
            b.subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
        ),
    decreases n,
{
    broadcast use layout_of_sized;

    let s = size_of::<T>() as int;
    lemma_mul_basics(s);
    if n == 0 {
        Seq::empty()
    } else {
        let prev = slice_encoding_exists_prefix(v, n - 1);
        let tracked e = super::slice::tracked_slice_index(v, n - 1);
        let e_bytes = T::encoding_exists(e, arbitrary());
        T::encoding_size(e, arbitrary(), e_bytes);
        assert(e_bytes.len() == s);
        let b = prev + e_bytes;
        lemma_mul_is_distributive_add_other_way(s, n - 1, 1);
        assert(b.len() == n * s);
        assert forall|i: int| #![trigger v@[i]] 0 <= i < n implies T::encode(
            &v@[i],
            arbitrary(),
            b.subrange(i * s, (i + 1) * s),
        ) by {
            if i < n - 1 {
                lemma_mul_nonnegative(i, s);
                lemma_mul_inequality(i, i + 1, s);
                lemma_mul_inequality(i + 1, n - 1, s);
                assert(b.subrange(i * s, (i + 1) * s) =~= prev.subrange(i * s, (i + 1) * s));
            } else {
                assert(b.subrange(i * s, (i + 1) * s) =~= e_bytes);
            }
        }
        b
    }
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
