use super::prelude::*;

verus! {

// Specs defining wrapping add and sub semantics for unsigned integers
macro_rules! define_uint_wrapping_ops {
    ([$(($value_ty: ty, $wrap_add:ident, $wrap_sub:ident))*]) => {
        $(
            verus! {

            pub open spec fn $wrap_add(a: int, b: int) -> int {
                if a + b > (<$value_ty>::MAX as int) {
                    a + b - ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
                } else {
                    a + b
                }
            }

            pub open spec fn $wrap_sub(a: int, b: int) -> int {
                if a - b < (<$value_ty>::MIN as int) {
                    a - b + ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
                } else {
                    a - b
                }
            }

            } // verus!
        )*
    }
}

// Specs defining wrapping add and sub semanantics for signed integers
macro_rules! define_int_wrapping_ops {
    ([$(($value_ty: ty, $wrap_add:ident, $wrap_sub:ident))*]) => {
        $(
            verus! {

            pub open spec fn $wrap_add(a: int, b: int) -> int {
                if a + b > (<$value_ty>::MAX as int) {
                    a + b - ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
                } else if a + b < (<$value_ty>::MIN as int) {
                    a + b + ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
                } else {
                    a + b
                }
            }

            pub open spec fn $wrap_sub(a: int, b: int) -> int {
                if a - b > (<$value_ty>::MAX as int) {
                    a - b - ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
                } else if a - b < (<$value_ty>::MIN as int) {
                    a - b + ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
                } else {
                    a - b
                }
            }

            } // verus!
        )*
    }
}

define_uint_wrapping_ops!([
    (u8, wrapping_add_u8, wrapping_sub_u8)
    (u16, wrapping_add_u16, wrapping_sub_u16)
    (u32, wrapping_add_u32, wrapping_sub_u32)
    (u64, wrapping_add_u64, wrapping_sub_u64)
    (u128, wrapping_add_u128, wrapping_sub_u128)
    (usize, wrapping_add_usize, wrapping_sub_usize)
]);

define_int_wrapping_ops!([
    (i8, wrapping_add_i8, wrapping_sub_i8)
    (i16, wrapping_add_i16, wrapping_sub_i16)
    (i32, wrapping_add_i32, wrapping_sub_i32)
    (i64, wrapping_add_i64, wrapping_sub_i64)
    (i128, wrapping_add_i128, wrapping_sub_i128)
    (isize, wrapping_add_isize, wrapping_sub_isize)
]);

} // verus!
