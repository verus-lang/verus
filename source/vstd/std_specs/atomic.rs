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

        #[verifier::external_fn_specification]
        pub fn ex_new(v: $ty) -> $at {
            <$at>::new(v)
        }

        #[verifier::external_fn_specification]
        pub fn ex_compare_exchange(
            atomic: &$at,
            current: $ty,
            new: $ty,
            success: Ordering,
            failure: Ordering,
        ) -> Result<$ty, $ty> {
            atomic.compare_exchange(current, new, success, failure)
        }

        #[verifier::external_fn_specification]
        pub fn ex_compare_exchange_weak(
            atomic: &$at,
            current: $ty,
            new: $ty,
            success: Ordering,
            failure: Ordering,
        ) -> Result<$ty, $ty> {
            atomic.compare_exchange_weak(current, new, success, failure)
        }

        #[verifier::external_fn_specification]
        pub fn ex_fetch_and(atomic: &$at, val: $ty, order: Ordering) -> $ty {
            atomic.fetch_and(val, order)
        }

        #[verifier::external_fn_specification]
        pub fn ex_fetch_nand(atomic: &$at, val: $ty, order: Ordering) -> $ty {
            atomic.fetch_nand(val, order)
        }

        #[verifier::external_fn_specification]
        pub fn ex_fetch_or(atomic: &$at, val: $ty, order: Ordering) -> $ty {
            atomic.fetch_or(val, order)
        }

        #[verifier::external_fn_specification]
        pub fn ex_fetch_xor(atomic: &$at, val: $ty, order: Ordering) -> $ty {
            atomic.fetch_xor(val, order)
        }

        #[verifier::external_fn_specification]
        pub fn ex_load(atomic: &$at, order: Ordering) -> $ty {
            atomic.load(order)
        }

        #[verifier::external_fn_specification]
        pub fn ex_store(atomic: &$at, val: $ty, order: Ordering) {
            atomic.store(val, order)
        }

        #[verifier::external_fn_specification]
        pub fn ex_swap(atomic: &$at, val: $ty, order: Ordering) -> $ty {
            atomic.swap(val, order)
        }
    };
}

macro_rules! atomic_specs_int_specific {
    ($at:ty, $ty:ty) => {
        #[verifier::external_fn_specification]
        pub fn ex_fetch_add(atomic: &$at, val: $ty, order: Ordering) -> $ty {
            atomic.fetch_add(val, order)
        }

        #[verifier::external_fn_specification]
        pub fn ex_fetch_sub(atomic: &$at, val: $ty, order: Ordering) -> $ty {
            atomic.fetch_sub(val, order)
        }

        #[verifier::external_fn_specification]
        pub fn ex_fetch_min(atomic: &$at, val: $ty, order: Ordering) -> $ty {
            atomic.fetch_min(val, order)
        }

        #[verifier::external_fn_specification]
        pub fn ex_fetch_max(atomic: &$at, val: $ty, order: Ordering) -> $ty {
            atomic.fetch_max(val, order)
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
