#![allow(unused_imports)]
use crate::prelude::*;

use core::option::Option;
use core::option::Option::Some;
use core::option::Option::None;

use core::result::Result;
use core::result::Result::Ok;
use core::result::Result::Err;

verus!{

////// Add is_variant-style spec functions

mod getters {
    #[verus::internal(is_variant("Ok"))]
    #[allow(non_snake_case)]
    #[verus::internal(spec)]
    #[verus::internal(verus_macro)]
    pub fn is_Ok<T, E>(res: &Result<T, E>) -> bool {
        unimplemented!()
    }

    #[allow(non_snake_case)]
    #[verus::internal(get_variant("Ok", 0))]
    #[verus::internal(spec)]
    #[verus::internal(verus_macro)]
    pub fn get_Ok_0<T, E>(res: Result<T, E>) -> T {
        unimplemented!()
    }

    #[verus::internal(is_variant("Err"))]
    #[allow(non_snake_case)]
    #[verus::internal(spec)]
    #[verus::internal(verus_macro)]
    pub fn is_Err<T, E>(res: &Result<T, E>) -> bool {
        unimplemented!()
    }

    #[allow(non_snake_case)]
    #[verus::internal(get_variant("Err", 0))]
    #[verus::internal(spec)]
    #[verus::internal(verus_macro)]
    pub fn get_Err_0<T, E>(res: Result<T, E>) -> E {
        unimplemented!()
    }
}

pub trait ResultAdditionalSpecFns<T, E> {
    #[allow(non_snake_case)] spec fn is_Ok(&self) -> bool;
    #[allow(non_snake_case)] spec fn get_Ok_0(&self) -> T;
    #[allow(non_snake_case)] spec fn is_Err(&self) -> bool;
    #[allow(non_snake_case)] spec fn get_Err_0(&self) -> E;
}

impl<T, E> ResultAdditionalSpecFns<T, E> for Result<T, E> {
    #[verifier(inline)]
    open spec fn is_Ok(&self) -> bool { getters::is_Ok(self) }

    #[verifier(inline)]
    open spec fn get_Ok_0(&self) -> T { getters::get_Ok_0(*self) }

    #[verifier(inline)]
    open spec fn is_Err(&self) -> bool { getters::is_Err(self) }

    #[verifier(inline)]
    open spec fn get_Err_0(&self) -> E { getters::get_Err_0(*self) }
}

////// Specs for std methods

// is_ok

#[verifier(inline)]
pub open spec fn is_ok<T, E>(result: &Result<T, E>) -> bool {
    getters::is_Ok(result)
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_ok)]
pub fn ex_result_is_ok<T, E>(result: &Result<T, E>) -> (b: bool)
    ensures b == is_ok(result)
{
    result.is_ok()
}

// is_err

#[verifier(inline)]
pub open spec fn is_err<T, E>(result: &Result<T, E>) -> bool {
    getters::is_Err(result)
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_err)]
pub fn ex_result_is_err<T, E>(result: &Result<T, E>) -> (b: bool)
    ensures b == is_err(result)
{
    result.is_err()
}

// as_ref

#[verifier::external_fn_specification]
pub fn as_ref<T, E>(result: &Result<T, E>) -> (r: Result<&T, &E>)
    ensures
        r.is_Ok() <==> result.is_Ok(),
        r.is_Ok() ==> result.get_Ok_0() == r.get_Ok_0(),
        r.is_Err() <==> result.is_Err(),
        r.is_Err() ==> result.get_Err_0() == r.get_Err_0(),
{
    result.as_ref()
}

// unwrap

#[verifier(inline)]
pub open spec fn spec_unwrap<T, E: core::fmt::Debug>(result: Result<T, E>) -> T
    recommends result.is_Ok()
{
    result.get_Ok_0()
}

#[verifier(when_used_as_spec(spec_unwrap))]
#[verifier::external_fn_specification]
pub fn unwrap<T, E: core::fmt::Debug>(result: Result<T, E>) -> (t: T)
    requires
        result.is_Ok(),
    ensures
        t == result.get_Ok_0(),
{
    result.unwrap()
}

// unwrap_err

#[verifier(inline)]
pub open spec fn spec_unwrap_err<T: core::fmt::Debug, E>(result: Result<T, E>) -> E
    recommends result.is_Err()
{
    result.get_Err_0()
}

#[verifier(when_used_as_spec(spec_unwrap_err))]
#[verifier::external_fn_specification]
pub fn unwrap_err<T: core::fmt::Debug, E>(result: Result<T, E>) -> (e: E)
    requires
        result.is_Err(),
    ensures
        e == result.get_Err_0(),
{
    result.unwrap_err()
}

}
