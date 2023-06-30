#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::pervasive::runtime_assert;

verus!{

fn test_u32_checked_add() {
    runtime_assert(u32::MAX.checked_add(1).is_none());
    runtime_assert((u32::MAX - 1).checked_add(1).unwrap() == u32::MAX);
    runtime_assert(5u32.checked_add(10).unwrap() == 15);
}

fn test_u32_checked_add_signed() {
    runtime_assert(1u32.checked_add_signed(-2).is_none());
    runtime_assert(1u32.checked_add_signed(-1).unwrap() == 0);
    runtime_assert(5u32.checked_add_signed(10).unwrap() == 15);
}

fn test_u32_checked_sub() {
    runtime_assert(1u32.checked_sub(2).is_none());
    runtime_assert(1u32.checked_sub(1).unwrap() == 0);
    runtime_assert(u32::MAX.checked_sub(u32::MAX).unwrap() == 0);
    runtime_assert(10u32.checked_sub(5).unwrap() == 5);
}

fn test_u32_checked_mul() {
    runtime_assert(u32::MAX.checked_mul(2).is_none());
    runtime_assert(u32::MAX.checked_mul(1).unwrap() == u32::MAX);
    runtime_assert(u32::MAX.checked_mul(0).unwrap() == 0);
    runtime_assert((u32::MAX / 2).checked_mul(4).is_none());
    runtime_assert(5u32.checked_mul(10).unwrap() == 50);
}

fn test_u32_checked_div() {
    runtime_assert(u32::MAX.checked_div(0).is_none());
    runtime_assert(u32::MAX.checked_div(1).unwrap() == u32::MAX);
    runtime_assert(10u32.checked_div(5).unwrap() == 2);
}

fn test_u32_checked_div_euclid() {
    runtime_assert(u32::MAX.checked_div_euclid(0).is_none());
    runtime_assert(u32::MAX.checked_div_euclid(1).unwrap() == u32::MAX);
    runtime_assert(10u32.checked_div_euclid(5).unwrap() == 2);
}

fn test_u32_checked_rem() {
    runtime_assert(u32::MAX.checked_rem(0).is_none());
    runtime_assert(0u32.checked_rem(0).is_none());
    runtime_assert(0u32.checked_rem(1).unwrap() == 0);
    runtime_assert(7u32.checked_rem(2).unwrap() == 1);
}

fn test_u32_checked_rem_euclid() {
    runtime_assert(u32::MAX.checked_rem_euclid(0).is_none());
    runtime_assert(0u32.checked_rem_euclid(0).is_none());
    runtime_assert(0u32.checked_rem_euclid(1).unwrap() == 0);
    runtime_assert(7u32.checked_rem_euclid(2).unwrap() == 1);
}

fn test_i32_checked_add() {
    let neg_one: i32 = -1;
    let neg_five: i32 = -5;
    let neg_ten: i32 = -10;
    let neg_fifteen: i32 = -15;
    runtime_assert(i32::MAX.checked_add(1).is_none());
    runtime_assert((i32::MAX - 2).checked_add(1).unwrap() == i32::MAX - 1);
    runtime_assert(i32::MIN.checked_add(neg_one).is_none());
    runtime_assert(i32::MIN.checked_add(1).unwrap() == i32::MIN + 1);
    runtime_assert(neg_ten.checked_add(5).unwrap() == neg_five);
    runtime_assert(10i32.checked_add(5).unwrap() == 15);
    runtime_assert(10i32.checked_add(neg_five).unwrap() == 5);
    runtime_assert(neg_ten.checked_add(neg_five).unwrap() == neg_fifteen);
}

fn test_i32_checked_add_unsigned() {
    let neg_five: i32 = -5;
    let neg_ten: i32 = -10;
    runtime_assert(i32::MAX.checked_add_unsigned(1).is_none());
    runtime_assert((i32::MAX - 1).checked_add_unsigned(1).unwrap() == i32::MAX);
    runtime_assert(i32::MIN.checked_add_unsigned(10).unwrap() == i32::MIN + 10);
    runtime_assert(i32::MIN.checked_add_unsigned(u32::MAX).unwrap() == i32::MAX);
    runtime_assert(neg_ten.checked_add_unsigned(5).unwrap() == neg_five);
}

fn test_i32_checked_sub() {
    runtime_assert((i32::MIN + 2).checked_sub(1).unwrap() == i32::MIN + 1);
    runtime_assert((i32::MIN + 2).checked_sub(3).is_none());
    runtime_assert(i32::MIN.checked_sub(i32::MIN).unwrap() == 0);
    runtime_assert(i32::MIN.checked_sub(i32::MAX).is_none());
    runtime_assert(0i32.checked_sub(i32::MIN).is_none());
    runtime_assert(0i32.checked_sub(i32::MAX).unwrap() == i32::MIN + 1);
}

fn main() {}

}