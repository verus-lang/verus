#![allow(unused_imports)]

use super::arithmetic::power::*;
use super::arithmetic::power2::*;
use super::endian::*;
use super::layout::*;
use super::math::*;
use super::prelude::*;
use super::raw_ptr::*;
use super::seq::*;
use super::type_representation::*;
use crate::vstd::group_vstd_default;

verus! {

broadcast use {group_layout_axioms, group_vstd_default};

pub trait TransmuteSpec where Self: TypeRepresentation {
    spec fn transmute_req<Dst: TypeRepresentation>(src: Self, dst: Dst, shadow_data: ShadowData<Self>) -> bool;
}

pub open spec fn transmute_req_default<Src: TypeRepresentation, Dst: TypeRepresentation>(src: Src, dst: Dst) -> bool {
    &&& forall|bytes|
        #![trigger Src::encode(src, arbitrary(), bytes)]
        #![trigger Dst::decode(bytes, dst, arbitrary())]
        Src::encode(src, arbitrary(), bytes) ==> Dst::decode(bytes, dst, arbitrary())
    &&& Src::can_be_encoded()
}

// TODO - use "default" impl to all the necessary types
/*impl TransmuteSpec for bool {
    open spec fn transmute_req<Dst: TypeRepresentation>(src: bool, dst: Dst, shadow_data: ShadowData<bool>) -> bool {
        //transmute_req_default::<bool, Dst>(src, dst)
        false
    }
}*/

//TODO - will delete
// The below spec functions define the `AbstractByte` encoding _abstractly_ for each type.
// This means that, e.g., we can state the specification for transmutes over all types.
// However, in order to reason meaningfully about this encoding, we must provide a concrete specification for it.
/// Is encoding allowed for this type?
pub uninterp spec fn abs_can_be_encoded<T: ?Sized>() -> bool;

/// Can 'value' be encoded to the given bytes?
pub uninterp spec fn abs_encode<T: ?Sized>(value: &T, bytes: Seq<AbstractByte>) -> bool;

/// Can the given bytes always be decoded to the given value?
pub uninterp spec fn abs_decode<T: ?Sized>(bytes: Seq<AbstractByte>, value: &T) -> bool;

/// For any type `T`, the encoding must correctly translate the size of the type.
/*pub broadcast axiom fn encode_decode_len<T>(value: T, bytes: Seq<AbstractByte>)
    ensures
        #![trigger abs_encode::<T>(&value, bytes)]
        #![trigger abs_decode::<T>(bytes, &value)]
        abs_encode::<T>(&value, bytes) ==> bytes.len() == size_of::<T>(),
        abs_decode::<T>(bytes, &value) ==> bytes.len() == size_of::<T>(),
;

pub axiom fn encode_decode_inverse<T>(tracked value: &T)
    ensures
        forall|bytes| #[trigger] abs_encode::<T>(value, bytes) ==> abs_decode::<T>(bytes, value),
;
*/


/// Generic precondition on transmute.
pub open spec fn transmute_pre<T, U>(src: T, dst: U) -> bool {
    &&& forall|bytes|
        #![trigger abs_encode::<T>(&src, bytes)]
        #![trigger abs_decode::<U>(bytes, &dst)]
        abs_encode::<T>(&src, bytes) ==> abs_decode::<U>(bytes, &dst)
    &&& abs_can_be_encoded::<T>()
}

/// Generic postcondition on transmute.
pub open spec fn transmute_post<U>(dst_ghost: U, dst: U) -> bool {
    dst_ghost == dst
}

/// Generic precondition on transmute for "pointed-to" values of the given types.
pub open spec fn transmute_pre_points_to<T: ?Sized, U: ?Sized>(src: &T, dst: &U) -> bool {
    &&& forall|bytes| #[trigger] abs_decode::<T>(bytes, src) ==> abs_decode::<U>(bytes, dst)
    &&& abs_can_be_encoded::<T>()
}

pub broadcast group group_transmute_axioms {
    group_type_representation_axioms,
}

/*
/* "Test cases" on transmute to validate the encoding specs */

macro_rules! transmute_refl_unique_lemma {
    ($(
        ($typ:ty, $refl_lemma_name:ident, $unique_lemma_name:ident);
    )+) => {$(
        verus! {
            /// A value `x: $typ` can be transmuted to itself.
            pub proof fn $refl_lemma_name(tracked x: $typ, y: $typ)
                requires
                    x == y
                ensures
                    transmute_pre(x, y),
            {
                broadcast use group_transmute_axioms;

                assert forall|bytes| abs_encode::<$typ>(&x, bytes) implies abs_decode::<$typ>(bytes, &(y@)) by {
                    <$typ as TypeRepresentation>::encoding_invertible(x, bytes);
                }
            }

            /// When a `$typ` is transmuted to a `$typ`, the value can only be transmuted to itself.
            pub proof fn $unique_lemma_name(tracked x: $typ, y: $typ)
                requires
                    transmute_pre(x, y)
                ensures
                    x == y
            {
                broadcast use group_transmute_axioms;

                let bytes = <$typ as TypeRepresentation>::encoding_exists(x);
            }
        }
    )+};
}

transmute_refl_unique_lemma! {
    ((), transmute_unit_refl, transmute_unit_unique);
    (bool, transmute_bool_refl, transmute_bool_unique);
    (u8, transmute_u8_refl, transmute_u8_unique);
    (u16, transmute_u16_refl, transmute_u16_unique);
    (u32, transmute_u32_refl, transmute_u32_unique);
    (u64, transmute_u64_refl, transmute_u64_unique);
    (u128, transmute_u128_refl, transmute_u128_unique);
    (usize, transmute_usize_refl, transmute_usize_unique);
    (i8, transmute_i8_refl, transmute_i8_unique);
    (i16, transmute_i16_refl, transmute_i16_unique);
    (i32, transmute_i32_refl, transmute_i32_unique);
    (i64, transmute_i64_refl, transmute_i64_unique);
    (i128, transmute_i128_refl, transmute_i128_unique);
    (isize, transmute_isize_refl, transmute_isize_unique);
}

/// A value `x: *mut T` for `T: Sized` can be transmuted to itself.
pub proof fn transmute_mut_ptr_sized_refl<T: Sized>(tracked x: *mut T, y: *mut T)
    requires
        x@ == y@,
    ensures
        transmute_pre(x, y),
{
    broadcast use group_transmute_axioms;

    assert forall|bytes| abs_encode::<*mut T>(&x, bytes) implies abs_decode::<*mut T>(
        bytes,
        &y,
    ) by {
        <*mut T as TypeRepresentation>::encoding_invertible(x, bytes);
    }
}

/// When a `*mut T` is transmuted to a `*mut T` for `T: Sized`, a value can only be transmuted to itself.
pub proof fn transmute_mut_ptr_sized_unique<T: Sized>(tracked x: *mut T, y: *mut T)
    requires
        transmute_pre(x, y),
    ensures
        x@ == y@,
{
    broadcast use group_transmute_axioms;

    let bytes = <*mut T as TypeRepresentation>::encoding_exists(x);
}

/// A value `x: *const T` for `T: Sized` can be transmuted to itself.
pub proof fn transmute_const_ptr_sized_refl<T: Sized>(tracked x: *const T, y: *const T)
    requires
        x@ == y@,
    ensures
        transmute_pre(x, y),
{
    broadcast use group_transmute_axioms;

    assert forall|bytes| abs_encode::<*const T>(&x, bytes) implies abs_decode::<*const T>(
        bytes,
        &y,
    ) by {
        <*const T as TypeRepresentation>::encoding_invertible(x, bytes);
    }
}

/// When a `*const T` is transmuted to a `*const T` for `T: Sized`, a value can only be transmuted to itself.
pub proof fn transmute_const_ptr_sized_unique<T: Sized>(tracked x: *const T, y: *const T)
    requires
        transmute_pre(x, y),
    ensures
        x@ == y@,
{
    broadcast use group_transmute_axioms;

    let bytes = <*const T as TypeRepresentation>::encoding_exists(x);
}

// we cannot prove that x can only be transmuted to y because that would need stronger properties from the metadata encoding
/// When transmuting a `*mut T` to a `*mut T` for `T: ?Sized`, a value `x: *mut T` can be transmuted to itself.
pub proof fn transmute_mut_ptr_unsized_refl<T: ?Sized>(tracked x: *mut T, y: *mut T)
    requires
        ptr_metadata_encoding_well_defined::<T>(),
        x == y,
    ensures
        transmute_pre(x, y),
{
    broadcast use group_transmute_axioms;

    assert forall|bytes| abs_encode::<*mut T>(&x, bytes) implies abs_decode::<*mut T>(
        bytes,
        &y,
    ) by {
        <*mut T as TypeRepresentation>::encoding_invertible(x, bytes);
    }
}

/// When transmuting a `*const T` to a `*const T` for `T: ?Sized`, a value `x: *const T` can be transmuted to itself.
pub proof fn transmute_const_ptr_unsized_refl<T: ?Sized>(tracked x: *const T, y: *const T)
    requires
        ptr_metadata_encoding_well_defined::<T>(),
        x == y,
    ensures
        transmute_pre(x, y),
{
    broadcast use group_transmute_axioms;

    assert forall|bytes| abs_encode::<*const T>(&x, bytes) implies abs_decode::<*const T>(
        bytes,
        &y,
    ) by {
        <*const T as TypeRepresentation>::encoding_invertible(x, bytes);
    }
}

/// A `usize` can be transmuted to a `*mut T` for `T: Sized`. The resulting pointer has an address corresponding to the source value and a null `Provenance`.
pub proof fn transmute_usize_mut_ptr<T: Sized>(tracked src: usize) -> (tracked dst: *mut T)
    ensures
        transmute_pre(src, dst),
        dst == ptr_mut_from_data(
            PtrData::<T> { addr: src, provenance: Provenance::None, metadata: () },
        ),
{
    broadcast use group_transmute_axioms;

    let tracked dst = tracked_ptr_mut_from_data(
        PtrData { addr: src, provenance: Provenance::None, metadata: () },
    );
    assert forall|bytes| #[trigger] abs_encode::<usize>(&src, bytes) implies abs_decode::<*mut T>(
        bytes,
        &dst,
    ) by {
        assert(bytes =~= bytes.subrange(0, size_of::<usize>() as int));
        assert(Seq::<AbstractByte>::empty() =~= bytes.subrange(
            size_of::<usize>() as int,
            size_of::<*mut T>() as int,
        ));
    }
    dst
}
    */

} // verus!
