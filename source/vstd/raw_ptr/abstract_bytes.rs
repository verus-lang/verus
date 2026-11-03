#![allow(unused_imports)]

use super::super::layout::*;
use super::super::prelude::*;
#[cfg(verus_keep_ghost)]
use super::super::type_representation::*;

verus! {

/// Can the given value be encoded into the abstract bytes?
pub uninterp spec fn abstract_bytes_encode<T: ?Sized>(value: &T, bytes: Seq<AbstractByte>) -> bool;

// TODO - explain how related to type representation
/// Can the given abstract bytes be decoded to the given value?
pub uninterp spec fn abstract_bytes_decode<T: ?Sized>(bytes: Seq<AbstractByte>, value: &T) -> bool;

/// For any type `T`, the abstract byte encoding must match the size of the type.
pub broadcast axiom fn abstract_bytes_encode_decode_len<T: ?Sized>(value: &T, bytes: Seq<AbstractByte>)
    ensures
        #![trigger abstract_bytes_encode::<T>(value, bytes)]
        #![trigger abstract_bytes_decode::<T>(bytes, value)]
        abstract_bytes_encode::<T>(&value, bytes) ==> bytes.len() == spec_size_of_val::<T>(value),
        abstract_bytes_decode::<T>(bytes, &value) ==> bytes.len() == spec_size_of_val::<T>(value),
;

// TODO
// does this need a tracked input?
pub axiom fn encode_decode_inverse<T: ?Sized>(tracked value: &T)
    ensures
        forall|bytes| #[trigger] abstract_bytes_encode::<T>(value, bytes) ==> abstract_bytes_decode::<T>(bytes, value),
;


// TODO - how to tie abstract_bytes_decode to TypeRepresentation?
// note: currently not supported = types whose encoding depends on shadow data. This includes &T
// PointsTo<&T>
// &&T
// *const &T

// &T -> *const T, &PointsTo<T>
// &PointsTo<str> -> &PointsToUntyped -> &PointsTo<[u8]>
// PointsTo<&str> -> PointsToUntyped -> PointsTo<&[u8]>

// PointsTo<&u8> -> PointsTo<&bool>
// PointsTo<&u8> -> PointsToUntyped + Tracked<&u8>
// PointsToUntyped + Tracked<&bool> -> PointsTo<&bool>

// &str -> &[u8]
// - encode ptr (shadow data)
// - encode the str (pointed-to data)

// &3 -> &bool
// UB: when trying to deref the &bool
// &T represented as T

// PointsTo<T> where T: TypeRepresentation
pub broadcast axiom fn type_representation_implements_encode_decode<T: ?Sized + TypeRepresentation>(value: &T, bytes: Seq<AbstractByte>)
    requires
        !T::encoding_depends_on_shadow_data()
    ensures
        #![trigger abstract_bytes_encode::<T>(value, bytes)]
        #![trigger abstract_bytes_decode::<T>(bytes, value)]
        #![trigger T::encode(value, arbitrary(), bytes)]
        #![trigger T::decode(bytes, value, arbitrary())]
        abstract_bytes_encode::<T>(value, bytes) <==> T::encode(value, arbitrary(), bytes),
        abstract_bytes_decode::<T>(bytes, value) <==> T::decode(bytes, value, arbitrary())
    ;

/// The bytes decode to a slice exactly when there is one `size_of::<T>()`-byte slot per element,
/// and each slot decodes to its element.
/// This follows the same pattern as the `[u8]` encoding (`TypeRepresentation` for `[u8]`).
pub broadcast axiom fn abstract_bytes_decode_slice<T>(bytes: Seq<AbstractByte>, v: &[T])
    ensures
        #[trigger] abstract_bytes_decode::<[T]>(bytes, v) <==> {
            &&& bytes.len() == v@.len() * size_of::<T>()
            &&& forall|i: int|
                #![trigger v@[i]]
                0 <= i < v@.len() ==> abstract_bytes_decode::<T>(
                    bytes.subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
                    &v@[i],
                )
        },
;

pub broadcast group group_abstract_bytes_axioms {
    abstract_bytes_encode_decode_len,
    type_representation_implements_encode_decode,
    abstract_bytes_decode_slice,
}

} // verus!
