#![allow(unused_imports)]
use super::super::prelude::*;

use core::option::Option;
use core::option::Option::None;
use core::option::Option::Some;

use core::result::Result;
use core::result::Result::Err;
use core::result::Result::Ok;

verus! {

////// Add is_variant-style spec functions
pub trait ResultAdditionalSpecFns<T, E> {
    #[allow(non_snake_case)]
    spec fn is_Ok(&self) -> bool;

    #[allow(non_snake_case)]
    spec fn get_Ok_0(&self) -> T;

    #[allow(non_snake_case)]
    spec fn is_Err(&self) -> bool;

    #[allow(non_snake_case)]
    spec fn get_Err_0(&self) -> E;
}

impl<T, E> ResultAdditionalSpecFns<T, E> for Result<T, E> {
    #[verifier::inline]
    open spec fn is_Ok(&self) -> bool {
        is_variant(self, "Ok")
    }

    #[verifier::inline]
    open spec fn get_Ok_0(&self) -> T {
        get_variant_field(self, "Ok", "0")
    }

    #[verifier::inline]
    open spec fn is_Err(&self) -> bool {
        is_variant(self, "Err")
    }

    #[verifier::inline]
    open spec fn get_Err_0(&self) -> E {
        get_variant_field(self, "Err", "0")
    }
}

////// Specs for std methods
// is_ok
#[verifier::inline]
pub open spec fn is_ok<T, E>(result: &Result<T, E>) -> bool {
    is_variant(result, "Ok")
}

#[verifier::when_used_as_spec(is_ok)]
pub assume_specification<T, E>[ Result::<T, E>::is_ok ](r: &Result<T, E>) -> (b: bool)
    ensures
        b == is_ok(r),
;

// is_err
#[verifier::inline]
pub open spec fn is_err<T, E>(result: &Result<T, E>) -> bool {
    is_variant(result, "Err")
}

#[verifier::when_used_as_spec(is_err)]
pub assume_specification<T, E>[ Result::<T, E>::is_err ](r: &Result<T, E>) -> (b: bool)
    ensures
        b == is_err(r),
;

// as_ref
pub assume_specification<T, E>[ Result::<T, E>::as_ref ](result: &Result<T, E>) -> (r: Result<
    &T,
    &E,
>)
    ensures
        r.is_Ok() <==> result.is_Ok(),
        r.is_Ok() ==> result.get_Ok_0() == r.get_Ok_0(),
        r.is_Err() <==> result.is_Err(),
        r.is_Err() ==> result.get_Err_0() == r.get_Err_0(),
;

// unwrap
#[verifier::inline]
pub open spec fn spec_unwrap<T, E: core::fmt::Debug>(result: Result<T, E>) -> T
    recommends
        result.is_Ok(),
{
    result.get_Ok_0()
}

#[verifier::when_used_as_spec(spec_unwrap)]
pub assume_specification<T, E: core::fmt::Debug>[ Result::<T, E>::unwrap ](
    result: Result<T, E>,
) -> (t: T)
    requires
        result.is_Ok(),
    ensures
        t == result.get_Ok_0(),
;

// unwrap_err
#[verifier::inline]
pub open spec fn spec_unwrap_err<T: core::fmt::Debug, E>(result: Result<T, E>) -> E
    recommends
        result.is_Err(),
{
    result.get_Err_0()
}

#[verifier::when_used_as_spec(spec_unwrap_err)]
pub assume_specification<T: core::fmt::Debug, E>[ Result::<T, E>::unwrap_err ](
    result: Result<T, E>,
) -> (e: E)
    requires
        result.is_Err(),
    ensures
        e == result.get_Err_0(),
;

// map
pub assume_specification<T, E, U, F: FnOnce(T) -> U>[ Result::<T, E>::map ](
    result: Result<T, E>,
    op: F,
) -> (mapped_result: Result<U, E>)
    requires
        result.is_ok() ==> op.requires((result.get_Ok_0(),)),
    ensures
        result.is_ok() ==> mapped_result.is_ok() && op.ensures(
            (result.get_Ok_0(),),
            mapped_result.get_Ok_0(),
        ),
        result.is_err() ==> mapped_result == Result::<U, E>::Err(result.get_Err_0()),
;

// map_err
#[verusfmt::skip]
pub assume_specification<T, E, F, O: FnOnce(E) -> F>[Result::<T, E>::map_err](result: Result<T, E>, op: O) -> (mapped_result: Result<T, F>)
    requires
        result.is_err() ==> op.requires((result.get_Err_0(),)),
    ensures
        result.is_err() ==> mapped_result.is_err() && op.ensures(
            (result.get_Err_0(),),
            mapped_result.get_Err_0(),
        ),
        result.is_ok() ==> mapped_result == Result::<T, F>::Ok(result.get_Ok_0());

// ok
#[verifier::inline]
pub open spec fn ok<T, E>(result: Result<T, E>) -> Option<T> {
    match result {
        Ok(t) => Some(t),
        Err(_) => None,
    }
}

#[verifier::when_used_as_spec(ok)]
pub assume_specification<T, E>[ Result::<T, E>::ok ](result: Result<T, E>) -> (opt: Option<T>)
    ensures
        opt == ok(result),
;

// err
#[verifier::inline]
pub open spec fn err<T, E>(result: Result<T, E>) -> Option<E> {
    match result {
        Ok(_) => None,
        Err(e) => Some(e),
    }
}

#[verifier::when_used_as_spec(err)]
pub assume_specification<T, E>[ Result::<T, E>::err ](result: Result<T, E>) -> (opt: Option<E>)
    ensures
        opt == err(result),
;

} // verus!
