#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::prelude::*;

verus!{

// == u32 methods ==

#[verifier::external_fn_specification]
pub fn ex_u32_checked_add(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        lhs + rhs > u32::MAX ==> result.is_None(),
        lhs + rhs <= u32::MAX ==> {
            match result {
                Some(result) => result == lhs + rhs,
                None => false
            }
        }
{
    lhs.checked_add(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_add_signed(lhs: u32, rhs: i32) -> (result: Option<u32>)
    ensures
        lhs + rhs > u32::MAX || lhs + rhs < 0 ==> result.is_None(),
        0 <= lhs + rhs <= u32::MAX ==> {
            match result {
                Some(result) => result == lhs + rhs,
                None => false
            }
        }
{
    lhs.checked_add_signed(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_sub(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        lhs - rhs < 0 ==> result.is_None(),
        lhs - rhs >= 0 ==> {
            match result {
                Some(result) => result == lhs - rhs,
                None => false
            }
        }
{
    lhs.checked_sub(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_mul(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        lhs * rhs > u64::MAX ==> result.is_None(),
        lhs * rhs <= u64::MAX ==> {
            match result {
                Some(result) => result == lhs * rhs,
                None => false
            }
        }
{
    lhs.checked_mul(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_div(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> {
            match result {
                Some(result) => result == lhs / rhs,
                None => false
            }
        }
{
    lhs.checked_div(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_div_euclid(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> {
            match result {
                Some(result) => result == lhs / rhs,
                None => false
            }
        }
{
    lhs.checked_div_euclid(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_rem(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> {
            match result {
                Some(result) => result == lhs % rhs,
                None => false 
            }
        }
{
    lhs.checked_rem(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_rem_euclid(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures 
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> {
            match result {
                Some(result) => result == lhs % rhs,
                None => false 
            }
        }
{
    lhs.checked_rem_euclid(rhs)
}

// == i32 methods ==

#[verifier::external_fn_specification]
pub fn ex_i32_checked_add(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures 
        lhs + rhs > i32::MAX || lhs + rhs < i32::MIN ==> result.is_None(),
        i32::MIN <= lhs + rhs <= i32::MAX ==> {
            match result {
                Some(result) => result == lhs + rhs,
                None => false
            }
        }
{
    lhs.checked_add(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_add_unsigned(lhs: i32, rhs: u32) -> (result: Option<i32>)
    ensures 
        lhs + rhs > i32::MAX ==> result.is_None(),
        lhs + rhs <= i32::MAX ==> {
            match result {
                Some(result) => result == lhs + rhs,
                None => false
            }
        }
{
    lhs.checked_add_unsigned(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_sub(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures 
        lhs - rhs > i32::MAX || lhs - rhs < i32::MIN ==> result.is_None(),
        i32::MIN <= lhs - rhs <= i32::MAX ==>
            match result {
                Some(result) => result == lhs - rhs,
                None => false
            }
{
    lhs.checked_sub(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_sub_unsigned(lhs: i32, rhs: u32) -> (result: Option<i32>)
    ensures
        lhs - rhs < i32::MIN ==> result.is_None(),
        i32::MIN <= lhs - rhs ==> 
            match result {
                Some(result) => result == lhs - rhs,
                None => false
            }
{
    lhs.checked_sub_unsigned(rhs)
}
// spec checked euclidean operations for signed ints as well. 
// test well with prime numbers to make sure you don't mess it up

} // verus!