#![allow(unused_imports)]

use super::prelude::*;
use super::type_representation::*;
use crate::vstd::group_vstd_default;
use super::raw_ptr::shared_ref_ptr;

verus! {

broadcast use {group_vstd_default};


/// True when all `AbstractByte` encodings of `src` and `src_shadow_data` can be decoded to `dst` and `dst_shadow_data`.
pub open spec fn encode_decode<T: ?Sized + TypeRepresentation, U: ?Sized + TypeRepresentation>(src: &T, src_shadow_data: ShadowData<T>, dst: &U, dst_shadow_data: ShadowData<U>) -> bool {
    &&& forall|bytes|
        #![trigger <T as TypeRepresentation>::encode(src, src_shadow_data, bytes)]
        #![trigger <U as TypeRepresentation>::decode(bytes, dst, dst_shadow_data)]
        <T as TypeRepresentation>::encode(src, src_shadow_data, bytes) ==> <U as TypeRepresentation>::decode(bytes, dst, dst_shadow_data)
}

/// True when for any `AbstractByte` sequence, if that sequence can be decoded to `src` and `src_shadow_data`,
/// then it can also be decoded to `dst` and `dst_shadow_data`.
pub open spec fn decode_decode<T: ?Sized + TypeRepresentation, U: ?Sized + TypeRepresentation>(src: &T, src_shadow_data: ShadowData<T>, dst: &U, dst_shadow_data: ShadowData<U>) -> bool {
    &&& forall|bytes|
        #![trigger <T as TypeRepresentation>::decode(bytes, src, src_shadow_data)]
        #![trigger <U as TypeRepresentation>::decode(bytes, dst, dst_shadow_data)]
        <T as TypeRepresentation>::decode(bytes, src, src_shadow_data) ==> <U as TypeRepresentation>::decode(bytes, dst, dst_shadow_data)
}

pub trait TransmuteSpec<Dst: TypeRepresentation> where Self: TypeRepresentation + Sized {
    open spec fn transmute_req(src: Self, src_shadow_data: ShadowData<Self>, dst: Dst, dst_shadow_data: ShadowData<Dst>) -> bool {
        &&& encode_decode::<Self, Dst>(&src, arbitrary(), &dst, arbitrary())
        &&& Self::can_be_encoded()
    }
}

impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for bool {}
impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for u8 {}
impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for u16 {}
impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for u32 {}
impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for u64 {}
impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for u128 {}
impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for usize {}
impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for i8 {}
impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for i16 {}
impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for i32 {}
impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for i64 {}
impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for i128 {}
impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for isize {}
impl<T: ?Sized, Dst: TypeRepresentation> TransmuteSpec<Dst> for *mut T where <T as core::ptr::Pointee>::Metadata: TypeRepresentation {}
impl<T: ?Sized, Dst: TypeRepresentation> TransmuteSpec<Dst> for *const T where <T as core::ptr::Pointee>::Metadata: TypeRepresentation {}
impl<Dst: TypeRepresentation> TransmuteSpec<Dst> for () {}
// the transmute precondition on shared references is stronger:
// we also require that the pointed-to data satisfies the type representation invariants
// currently, this can only be expressed for types whose encoding does not depend on shadow data
impl<'a, T: ?Sized, U: ?Sized> TransmuteSpec<&'a U> for &'a T 
    where T: TypeRepresentation, 
    U: TypeRepresentation,
    <T as core::ptr::Pointee>::Metadata: TypeRepresentation,
    <U as core::ptr::Pointee>::Metadata: TypeRepresentation
{
    open spec fn transmute_req(src: &'a T, src_shadow_data: ShadowData<&'a T>, dst: &'a U, dst_shadow_data: ShadowData<&'a U>) -> bool {
        &&& encode_decode::<&'a T, &'a U>(&src, src_shadow_data, &dst, dst_shadow_data)
        &&& decode_decode::<T, U>(src, arbitrary(), dst, arbitrary())
        &&& Self::can_be_encoded()
        &&& T::can_be_encoded()
        &&& !T::encoding_depends_on_shadow_data()
    }
}

/* "Test cases" on transmute to validate the encoding specs */

macro_rules! transmute_reflexive_injective_lemma {
    ($(
        ($typ:ty, $reflexive_lemma:ident, $injective_lemma:ident);
    )+) => {$(
        verus! {
            /// A value `x: $typ` can be transmuted to itself.
            pub proof fn $reflexive_lemma(tracked x: $typ, y: $typ)
                requires
                    x == y
                ensures
                    <$typ as TransmuteSpec<$typ>>::transmute_req(x, arbitrary(), y, arbitrary()),
            {
                assert forall|bytes| <$typ as TypeRepresentation>::encode(&x, arbitrary(), bytes) implies <$typ as TypeRepresentation>::decode(bytes, &y, arbitrary()) by {
                    <$typ as TypeRepresentation>::encoding_invertible(&x, arbitrary(), bytes);
                }
            }

            /// When a `$typ` is transmuted to a `$typ`, the value can only be transmuted to itself.
            pub proof fn $injective_lemma(tracked x: $typ, y: $typ)
                requires
                    <$typ as TransmuteSpec<$typ>>::transmute_req(x, arbitrary(), y, arbitrary())
                ensures
                    x == y
            {
                broadcast use group_type_representation_axioms;

                let bytes = <$typ as TypeRepresentation>::encoding_exists(&x, arbitrary());
            }
        }
    )+};
}

transmute_reflexive_injective_lemma! {
    ((), transmute_unit_reflexive, transmute_unit_injective);
    (bool, transmute_bool_reflexive, transmute_bool_injective);
    (u8, transmute_u8_reflexive, transmute_u8_injective);
    (u16, transmute_u16_reflexive, transmute_u16_injective);
    (u32, transmute_u32_reflexive, transmute_u32_injective);
    (u64, transmute_u64_reflexive, transmute_u64_injective);
    (u128, transmute_u128_reflexive, transmute_u128_injective);
    (usize, transmute_usize_reflexive, transmute_usize_injective);
    (i8, transmute_i8_reflexive, transmute_i8_injective);
    (i16, transmute_i16_reflexive, transmute_i16_injective);
    (i32, transmute_i32_reflexive, transmute_i32_injective);
    (i64, transmute_i64_reflexive, transmute_i64_injective);
    (i128, transmute_i128_reflexive, transmute_i128_injective);
    (isize, transmute_isize_reflexive, transmute_isize_injective);
}

macro_rules! transmute_ptr_reflexive_injective_lemmas {
    ($(
        ($mutability:tt, $reflexive_lemma:ident, $sized_injective_lemma:ident, $metasized_usize_injective_lemma:ident);
    )+) => {$(
        verus! {
            /// A value `x: *$mutability T` can be transmuted to itself.
            pub proof fn $reflexive_lemma<T: ?Sized>(tracked x: *$mutability T, y: *$mutability T)
                where <T as core::ptr::Pointee>::Metadata: TypeRepresentation
                requires
                    <*$mutability T as TypeRepresentation>::can_be_encoded(),
                    x@ == y@,
                ensures
                    <*$mutability T as TransmuteSpec<*$mutability T>>::transmute_req(x, arbitrary(), y, arbitrary()),
            {
                assert forall|bytes| <*$mutability T as TypeRepresentation>::encode(&x, arbitrary(), bytes) implies <*$mutability T as TypeRepresentation>::decode(
                    bytes,
                    &y,
                    arbitrary()
                ) by {
                    <*$mutability T as TypeRepresentation>::encoding_invertible(&x, arbitrary(), bytes);
                }
            }

            /// When a `*$mutability T` is transmuted to a `*$mutability T` for `T: Sized`, it can only be transmuted to itself.
            pub proof fn $sized_injective_lemma<T>(tracked x: *$mutability T, y: *$mutability T)
                requires
                    <*$mutability T as TransmuteSpec<*$mutability T>>::transmute_req(x, arbitrary(), y, arbitrary()),
                ensures
                    x@ == y@,
            {
                broadcast use group_type_representation_axioms;

                let bytes = <*$mutability T as TypeRepresentation>::encoding_exists(&x, arbitrary());
            }

            /// When a `*$mutability T` is transmuted to a `*$mutability T` for `T: core::ptr::Pointee<Metadata = usize>`, it can only be transmuted to itself.
            pub proof fn $metasized_usize_injective_lemma<T: core::ptr::Pointee<Metadata = usize>>(tracked x: *$mutability T, y: *$mutability T)
                requires
                    <*$mutability T as TransmuteSpec<*$mutability T>>::transmute_req(x, arbitrary(), y, arbitrary()),
                ensures
                    x@ == y@,
            {
                broadcast use group_type_representation_axioms;

                let bytes = <*$mutability T as TypeRepresentation>::encoding_exists(&x, arbitrary());
            }
        }
    )+};
}

transmute_ptr_reflexive_injective_lemmas! {
    (mut, transmute_mut_ptr_reflexive, transmute_mut_ptr_sized_injective, transmute_mut_ptr_metasized_usize_injective);
    (const, transmute_const_ptr_reflexive, transmute_const_ptr_sized_injective, transmute_const_ptr_metasized_usize_injective);
}

/// A value `x: &T` can be transmuted to itself.
#[verifier::shadow_data]
pub proof fn transmute_shr_ref_reflexive<T: ?Sized + TypeRepresentation>(tracked x: &T, tracked y: &T)
    where <T as core::ptr::Pointee>::Metadata: TypeRepresentation
    requires
        <*const T as TypeRepresentation>::can_be_encoded(),
        T::can_be_encoded(),
        !T::encoding_depends_on_shadow_data(),
        x == y,
        shared_ref_ptr(shadow_data(x)) == shared_ref_ptr(shadow_data(y))
    ensures
        <&T as TransmuteSpec<&T>>::transmute_req(x, shadow_data(x), y, shadow_data(y)),
{
    let sd_x = shadow_data(x);
    let sd_y = shadow_data(y);
    assert forall|bytes| #[trigger] <&T as TypeRepresentation>::encode(&x, sd_x, bytes) implies <&T as TypeRepresentation>::decode(
        bytes,
        &y,
        sd_y
    ) by {
        <&T as TypeRepresentation>::encoding_invertible(&x, sd_x, bytes);
    }
}

} // verus!
