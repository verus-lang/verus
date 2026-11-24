//! This module contains exec implementations of the fixed-width arithmetic
//! builtins `add`, `sub`, and `mul`.
//!
//! Unlike `a + b` (which has type `int` in spec code), `add(a, b)` stays in
//! the operand type and wraps on overflow, so it has a direct exec
//! counterpart. The macros rename a call `add(a, b)` to `exec_add(a, b)`,
//! which resolves to the [`exec_add`] defined here. For example,
//!
//! ```rust
//! exec_spec_verified! {
//!     spec fn add_u8(a: u8, b: u8) -> u8 {
//!         add(a, b)
//!     }
//! }
//! ```
//!
//! generates (simplified)
//!
//! ```rust
//! fn exec_add_u8(a: u8, b: u8) -> (res: u8)
//!     ensures res == add_u8(a, b)
//! {
//!     exec_add(a, b)
//! }
//! ```
//!
//! where `exec_add_u8(200, 100) == 44`. Each operation is computed in
//! `u128`/`i128` (which cannot overflow for operands of at most 64 bits) and
//! then truncated back to the operand type.
use crate::contrib::exec_spec::*;
use crate::prelude::*;

#[cfg(verus_keep_ghost)]
macro_rules! truncating_cast {
    ($e:expr, $t:ty) => {
        #[verifier::truncate]
        ($e as $t)
    };
}

#[cfg(not(verus_keep_ghost))]
macro_rules! truncating_cast {
    ($e:expr, $t:ty) => {
        ($e as $t)
    };
}

verus! {

pub trait ExecSpecFixedWidthArith: Sized {
    spec fn spec_fixed_add(self, rhs: Self) -> Self;

    spec fn spec_fixed_sub(self, rhs: Self) -> Self;

    spec fn spec_fixed_mul(self, rhs: Self) -> Self;

    fn exec_fixed_add(self, rhs: Self) -> (res: Self)
        ensures
            res == self.spec_fixed_add(rhs),
    ;

    fn exec_fixed_sub(self, rhs: Self) -> (res: Self)
        ensures
            res == self.spec_fixed_sub(rhs),
    ;

    fn exec_fixed_mul(self, rhs: Self) -> (res: Self)
        ensures
            res == self.spec_fixed_mul(rhs),
    ;
}

macro_rules! impl_unsigned_fixed_width_arith {
    ($($t:ty),*) => {
        $(
            verus! {
                impl ExecSpecFixedWidthArith for $t {
                    open spec fn spec_fixed_add(self, rhs: $t) -> $t {
                        add(self, rhs)
                    }

                    open spec fn spec_fixed_sub(self, rhs: $t) -> $t {
                        sub(self, rhs)
                    }

                    open spec fn spec_fixed_mul(self, rhs: $t) -> $t {
                        mul(self, rhs)
                    }

                    #[inline(always)]
                    fn exec_fixed_add(self, rhs: $t) -> (res: $t) {
                        truncating_cast!(self as u128 + rhs as u128, $t)
                    }

                    #[inline(always)]
                    fn exec_fixed_sub(self, rhs: $t) -> (res: $t) {
                        truncating_cast!(self as i128 - rhs as i128, $t)
                    }

                    #[inline(always)]
                    fn exec_fixed_mul(self, rhs: $t) -> (res: $t) {
                        assert((self as int) * (rhs as int) <= (u64::MAX as int) * (u64::MAX as int))
                            by (nonlinear_arith)
                            requires
                                0 <= self <= u64::MAX,
                                0 <= rhs <= u64::MAX,
                        ;
                        truncating_cast!(self as u128 * rhs as u128, $t)
                    }
                }
            }
        )*
    };
}

macro_rules! impl_signed_fixed_width_arith {
    ($($t:ty),*) => {
        $(
            verus! {
                impl ExecSpecFixedWidthArith for $t {
                    open spec fn spec_fixed_add(self, rhs: $t) -> $t {
                        add(self, rhs)
                    }

                    open spec fn spec_fixed_sub(self, rhs: $t) -> $t {
                        sub(self, rhs)
                    }

                    open spec fn spec_fixed_mul(self, rhs: $t) -> $t {
                        mul(self, rhs)
                    }

                    #[inline(always)]
                    fn exec_fixed_add(self, rhs: $t) -> (res: $t) {
                        truncating_cast!(self as i128 + rhs as i128, $t)
                    }

                    #[inline(always)]
                    fn exec_fixed_sub(self, rhs: $t) -> (res: $t) {
                        truncating_cast!(self as i128 - rhs as i128, $t)
                    }

                    #[inline(always)]
                    fn exec_fixed_mul(self, rhs: $t) -> (res: $t) {
                        assert(i64::MIN * i64::MIN >= (self as int) * (rhs as int) >= i64::MIN
                            * i64::MAX) by (nonlinear_arith)
                            requires
                                i64::MIN <= self <= i64::MAX,
                                i64::MIN <= rhs <= i64::MAX,
                        ;
                        truncating_cast!(self as i128 * rhs as i128, $t)
                    }
                }
            }
        )*
    };
}

impl_unsigned_fixed_width_arith!(u8, u16, u32, u64, usize);

impl_signed_fixed_width_arith!(i8, i16, i32, i64, isize);

#[inline(always)]
pub fn exec_add<T: ExecSpecFixedWidthArith>(a: T, b: T) -> (res: T)
    ensures
        res == a.spec_fixed_add(b),
{
    a.exec_fixed_add(b)
}

#[inline(always)]
pub fn exec_sub<T: ExecSpecFixedWidthArith>(a: T, b: T) -> (res: T)
    ensures
        res == a.spec_fixed_sub(b),
{
    a.exec_fixed_sub(b)
}

#[inline(always)]
pub fn exec_mul<T: ExecSpecFixedWidthArith>(a: T, b: T) -> (res: T)
    ensures
        res == a.spec_fixed_mul(b),
{
    a.exec_fixed_mul(b)
}

} // verus!
