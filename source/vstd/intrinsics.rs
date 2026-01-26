use super::prelude::*;

verus! {

pub uninterp spec fn spec_add<T: Copy>(x: T, y: T) -> T;

pub uninterp spec fn spec_sub<T: Copy>(x: T, y: T) -> T;

pub uninterp spec fn spec_max<T>() -> T;

pub uninterp spec fn spec_min<T>() -> T;

pub uninterp spec fn spec_lt<T>(x: T, y: T) -> bool;

pub uninterp spec fn spec_le<T>(x: T, y: T) -> bool;

pub uninterp spec fn spec_gt<T>(x: T, y: T) -> bool;

pub uninterp spec fn spec_ge<T>(x: T, y: T) -> bool;

macro_rules! impl_intrinsics_arith_specs {
    ([$(($t:ty, $fn_ops:ident, $fn_mm:ident))*]) => {
        $(
            verus! {
                pub broadcast axiom fn $fn_ops(x: $t, y: $t)
                    ensures
                        #![trigger spec_add::<$t>(x, y)]
                        #![trigger spec_sub::<$t>(x, y)]
                        #![trigger spec_lt::<$t>(x, y)]
                        #![trigger spec_le::<$t>(x, y)]
                        #![trigger spec_gt::<$t>(x, y)]
                        #![trigger spec_ge::<$t>(x, y)]
                        spec_add::<$t>(x, y) == (x + y) as $t,
                        spec_sub::<$t>(x, y) == (x - y) as $t,
                        spec_lt::<$t>(x, y) == (x < y),
                        spec_le::<$t>(x, y) == (x <= y),
                        spec_gt::<$t>(x, y) == (x > y),
                        spec_ge::<$t>(x, y) == (x >= y),
                ;

                pub broadcast axiom fn $fn_mm()
                    ensures
                        #![trigger spec_min::<$t>()]
                        #![trigger spec_max::<$t>()]
                        spec_min::<$t>() == $t::MIN,
                        spec_max::<$t>() == $t::MAX,
                ;
            }
        )*
    }
}

impl_intrinsics_arith_specs!([
    (usize, spec_bin_ops_usize, spec_min_max_usize)
    (u8, spec_bin_ops_u8, spec_min_max_u8)
    (u16, spec_bin_ops_u16, spec_min_max_u16)
    (u32, spec_bin_ops_u32, spec_min_max_u32)
    (u64, spec_bin_ops_u64, spec_min_max_u64)
    (u128, spec_bin_ops_u128, spec_min_max_u128)
    (isize, spec_bin_ops_isize, spec_min_max_isize)
    (i8, spec_bin_ops_i8, spec_min_max_i8)
    (i16, spec_bin_ops_i16, spec_min_max_i16)
    (i32, spec_bin_ops_i32, spec_min_max_i32)
    (i64, spec_bin_ops_i64, spec_min_max_i64)
    (i128, spec_bin_ops_i128, spec_min_max_i128)
]);

pub broadcast group group_intrinsics_arith_axioms {
    spec_bin_ops_usize,
    spec_min_max_usize,
    spec_bin_ops_u8,
    spec_min_max_u8,
    spec_bin_ops_u16,
    spec_min_max_u16,
    spec_bin_ops_u32,
    spec_min_max_u32,
    spec_bin_ops_u64,
    spec_min_max_u64,
    spec_bin_ops_u128,
    spec_min_max_u128,
    spec_bin_ops_isize,
    spec_min_max_isize,
    spec_bin_ops_i8,
    spec_min_max_i8,
    spec_bin_ops_i16,
    spec_min_max_i16,
    spec_bin_ops_i32,
    spec_min_max_i32,
    spec_bin_ops_i64,
    spec_min_max_i64,
    spec_bin_ops_i128,
    spec_min_max_i128,
}

} // verus!
