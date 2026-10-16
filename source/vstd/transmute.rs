#![allow(unused_imports)]

use super::prelude::*;
use super::type_representation::*;
use crate::vstd::group_vstd_default;
use core::marker::MetaSized;

verus! {

broadcast use {group_vstd_default};

pub trait TransmuteSpec<Dst: TypeRepresentation> where Self: TypeRepresentation {
    open spec fn transmute_req(src: Self, src_shadow_data: ShadowData<Self>, dst: Dst, dst_shadow_data: ShadowData<Dst>) -> bool {
        &&& encode_decode::<Self, Dst>(src, arbitrary(), dst, arbitrary())
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
// TODO - impl for sized types as well?
impl<'a, T, U> TransmuteSpec<&'a U> for &'a T 
    where T: TypeRepresentationMetaSized + MetaSized, 
    U: TypeRepresentationMetaSized + MetaSized,
    <T as core::ptr::Pointee>::Metadata: TypeRepresentation,
    <U as core::ptr::Pointee>::Metadata: TypeRepresentation
{
    open spec fn transmute_req(src: &'a T, src_shadow_data: ShadowData<&'a T>, dst: &'a U, dst_shadow_data: ShadowData<&'a U>) -> bool {
        &&& encode_decode::<&'a T, &'a U>(src, src_shadow_data, dst, dst_shadow_data)
        &&& decode_decode_metasized::<T, U>(src, dst)
        &&& Self::can_be_encoded()
        &&& T::can_be_encoded()
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
                broadcast use group_type_representation_axioms;

                assert forall|bytes| <$typ as TypeRepresentation>::encode(x, arbitrary(), bytes) implies <$typ as TypeRepresentation>::decode(bytes, y, arbitrary()) by {
                    <$typ as TypeRepresentation>::encoding_invertible(x, arbitrary(), bytes);
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

                let bytes = <$typ as TypeRepresentation>::encoding_exists(x, arbitrary());
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

// TODO
/// A value `x: *mut T` for `T: Sized` can be transmuted to itself.
pub proof fn transmute_mut_ptr_reflexive<T: ?Sized>(tracked x: *mut T, y: *mut T)
    where <T as core::ptr::Pointee>::Metadata: TypeRepresentation
    requires
        <*mut T as TypeRepresentation>::can_be_encoded(),
        x@ == y@,
    ensures
        <*mut T as TransmuteSpec<*mut T>>::transmute_req(x, arbitrary(), y, arbitrary()),
{
    broadcast use group_type_representation_axioms;

    assert forall|bytes| <*mut T as TypeRepresentation>::encode(x, arbitrary(), bytes) implies <*mut T as TypeRepresentation>::decode(
        bytes,
        y,
        arbitrary()
    ) by {
        <*mut T as TypeRepresentation>::encoding_invertible(x, arbitrary(), bytes);
    }
}

/// When a `*mut T` is transmuted to a `*mut T` for `T: Sized`, a value can only be transmuted to itself.
pub proof fn transmute_mut_ptr_sized_injective<T>(tracked x: *mut T, y: *mut T)
    requires
        <*mut T as TransmuteSpec<*mut T>>::transmute_req(x, arbitrary(), y, arbitrary()),
    ensures
        x@ == y@,
{
    broadcast use group_type_representation_axioms;

    let bytes = <*mut T as TypeRepresentation>::encoding_exists(x, arbitrary());
}

// TODO
/// When a `*mut T` is transmuted to a `*mut T` for `T: Sized`, a value can only be transmuted to itself.
pub proof fn transmute_mut_ptr_metasized_usize_injective<T: core::ptr::Pointee<Metadata = usize>>(tracked x: *mut T, y: *mut T)
    requires
        <*mut T as TransmuteSpec<*mut T>>::transmute_req(x, arbitrary(), y, arbitrary()),
    ensures
        x@ == y@,
{
    broadcast use group_type_representation_axioms;

    let bytes = <*mut T as TypeRepresentation>::encoding_exists(x, arbitrary());
}

// TODO
/// A value `x: *const T` for `T: Sized` can be transmuted to itself.
pub proof fn transmute_const_ptr_reflexive<T: ?Sized>(tracked x: *const T, y: *const T)
    where <T as core::ptr::Pointee>::Metadata: TypeRepresentation
    requires
        <*const T as TypeRepresentation>::can_be_encoded(),
        x@ == y@,
    ensures
        <*const T as TransmuteSpec<*const T>>::transmute_req(x, arbitrary(), y, arbitrary()),
{
    broadcast use group_type_representation_axioms;

    assert forall|bytes| <*const T as TypeRepresentation>::encode(x, arbitrary(), bytes) implies <*const T as TypeRepresentation>::decode(
        bytes,
        y,
        arbitrary()
    ) by {
        <*const T as TypeRepresentation>::encoding_invertible(x, arbitrary(), bytes);
    }
}

/// When a `*const T` is transmuted to a `*const T` for `T: Sized`, a value can only be transmuted to itself.
pub proof fn transmute_const_ptr_sized_injective<T: Sized>(tracked x: *const T, y: *const T)
    requires
        <*const T as TransmuteSpec<*const T>>::transmute_req(x, arbitrary(), y, arbitrary()),
    ensures
        x@ == y@,
{
    broadcast use group_type_representation_axioms;

    let bytes = <*const T as TypeRepresentation>::encoding_exists(x, arbitrary());
}

// TODO
pub proof fn transmute_const_ptr_metasized_usize_injective<T: core::ptr::Pointee<Metadata = usize>>(tracked x: *const T, y: *const T)
    requires
        <*const T as TransmuteSpec<*const T>>::transmute_req(x, arbitrary(), y, arbitrary()),
    ensures
        x@ == y@,
{
    broadcast use group_type_representation_axioms;

    let bytes = <*const T as TypeRepresentation>::encoding_exists(x, arbitrary());
}

// TODO - test cases for &T, &U

} // verus!
