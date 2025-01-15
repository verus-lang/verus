#![allow(unused_imports)]
use super::super::prelude::*;
use core::sync::atomic::*;

// Supports the core::sync::atomic functions
// This provides NO support for reasoning about the values inside the atomics.
// If you need to do that, see `vstd::atomic` or `vstd::atomic_ghost` instead.

#[verifier::external_type_specification]
pub struct ExOrdering(Ordering);

macro_rules! atomic_specs_common {
    ($at:ty, $ty:ty) => {
        #[verifier::external_type_specification]
        #[verifier::external_body]
        pub struct ExAtomic($at);

        verus!{

        pub assume_specification [ <$at>::new ](v: $ty) -> $at;

        pub assume_specification [ <$at>::compare_exchange ](
            atomic: &$at,
            current: $ty,
            new: $ty,
            success: Ordering,
            failure: Ordering,
        ) -> Result<$ty, $ty>;

        pub assume_specification [ <$at>::compare_exchange_weak ](
            atomic: &$at,
            current: $ty,
            new: $ty,
            success: Ordering,
            failure: Ordering,
        ) -> Result<$ty, $ty>;

        pub assume_specification [ <$at>::fetch_and ](atomic: &$at, val: $ty, order: Ordering) -> $ty;

        pub assume_specification [ <$at>::fetch_nand ](atomic: &$at, val: $ty, order: Ordering) -> $ty;

        pub assume_specification [ <$at>::fetch_or ](atomic: &$at, val: $ty, order: Ordering) -> $ty;

        pub assume_specification [ <$at>::fetch_xor ](atomic: &$at, val: $ty, order: Ordering) -> $ty;

        pub assume_specification [ <$at>::load ](atomic: &$at, order: Ordering) -> $ty;

        pub assume_specification [ <$at>::store ](atomic: &$at, val: $ty, order: Ordering);

        pub assume_specification [ <$at>::swap ](atomic: &$at, val: $ty, order: Ordering) -> $ty;

        }
    };
}

macro_rules! atomic_specs_int_specific {
    ($at:ty, $ty:ty) => {
        verus!{

        pub assume_specification [ <$at>::fetch_add ](atomic: &$at, val: $ty, order: Ordering) -> $ty;

        pub assume_specification [ <$at>::fetch_sub ](atomic: &$at, val: $ty, order: Ordering) -> $ty;

        pub assume_specification [ <$at>::fetch_min ](atomic: &$at, val: $ty, order: Ordering) -> $ty;

        pub assume_specification [ <$at>::fetch_max ](atomic: &$at, val: $ty, order: Ordering) -> $ty;

        }
    };
}

macro_rules! atomic_specs_int {
    ($modname:ident, $at:ty, $ty:ty) => {
        mod $modname {
            use super::*;
            atomic_specs_common!($at, $ty);
            atomic_specs_int_specific!($at, $ty);
        }
    };
}

macro_rules! atomic_specs_bool {
    ($modname:ident, $at:ty, $ty:ty) => {
        mod $modname {
            use super::*;
            atomic_specs_common!($at, $ty);
        }
    };
}

atomic_specs_int!(atomic_specs_u8, AtomicU8, u8);
atomic_specs_int!(atomic_specs_u16, AtomicU16, u16);
atomic_specs_int!(atomic_specs_u32, AtomicU32, u32);
atomic_specs_int!(atomic_specs_u64, AtomicU64, u64);
atomic_specs_int!(atomic_specs_usize, AtomicUsize, usize);

atomic_specs_int!(atomic_specs_i8, AtomicI8, i8);
atomic_specs_int!(atomic_specs_i16, AtomicI16, i16);
atomic_specs_int!(atomic_specs_i32, AtomicI32, i32);
atomic_specs_int!(atomic_specs_i64, AtomicI64, i64);
atomic_specs_int!(atomic_specs_isize, AtomicIsize, isize);

atomic_specs_bool!(atomic_specs_bool, AtomicBool, bool);
