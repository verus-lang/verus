#![allow(unused_imports)]
use super::super::prelude::*;

use core::option::Option;

use core::result::Result;

verus! {

////// Add is_variant-style spec functions
pub trait ResultAdditionalSpecFns<T, E> {
    #[cfg_attr(not(verus_verify_core), deprecated = "is_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
    #[allow(non_snake_case)]
    spec fn is_Ok(&self) -> bool;

    #[cfg_attr(not(verus_verify_core), deprecated = "get_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
    #[allow(non_snake_case)]
    spec fn get_Ok_0(&self) -> T;

    #[allow(non_snake_case)]
    spec fn arrow_Ok_0(&self) -> T;

    #[cfg_attr(not(verus_verify_core), deprecated = "is_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
    #[allow(non_snake_case)]
    spec fn is_Err(&self) -> bool;

    #[cfg_attr(not(verus_verify_core), deprecated = "get_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
    #[allow(non_snake_case)]
    spec fn get_Err_0(&self) -> E;

    #[allow(non_snake_case)]
    spec fn arrow_Err_0(&self) -> E;

    #[allow(deprecated)]
    proof fn tracked_unwrap(tracked self) -> (tracked t: T)
        requires
            self.is_Ok(),
        ensures
            t == self->Ok_0,
    ;

    #[allow(deprecated)]
    proof fn tracked_unwrap_err(tracked self) -> (tracked t: E)
        requires
            self.is_Err(),
        ensures
            t == self->Err_0,
    ;

    #[allow(deprecated)]
    proof fn tracked_expect(tracked self, msg: &str) -> (tracked t: T)
        requires
            self.is_Ok(),
        ensures
            t == self->Ok_0,
    ;

    #[allow(deprecated)]
    proof fn tracked_expect_err(tracked self, msg: &str) -> (tracked t: E)
        requires
            self.is_Err(),
        ensures
            t == self->Err_0,
    ;
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
    open spec fn arrow_Ok_0(&self) -> T {
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

    #[verifier::inline]
    open spec fn arrow_Err_0(&self) -> E {
        get_variant_field(self, "Err", "0")
    }

    proof fn tracked_unwrap(tracked self) -> (tracked t: T) {
        match self {
            Result::Ok(t) => t,
            Result::Err(_) => proof_from_false(),
        }
    }

    proof fn tracked_unwrap_err(tracked self) -> (tracked t: E) {
        match self {
            Result::Ok(_) => proof_from_false(),
            Result::Err(e) => e,
        }
    }

    proof fn tracked_expect(tracked self, msg: &str) -> (tracked t: T) {
        match self {
            Result::Ok(t) => t,
            Result::Err(_) => proof_from_false(),
        }
    }

    proof fn tracked_expect_err(tracked self, msg: &str) -> (tracked t: E) {
        match self {
            Result::Ok(_) => proof_from_false(),
            Result::Err(e) => e,
        }
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
    no_unwind
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
    no_unwind
;

// as_ref
pub assume_specification<T, E>[ Result::<T, E>::as_ref ](result: &Result<T, E>) -> (r: Result<
    &T,
    &E,
>)
    ensures
        r is Ok <==> result is Ok,
        r is Ok ==> result->Ok_0 == r->Ok_0,
        r is Err <==> result is Err,
        r is Err ==> result->Err_0 == r->Err_0,
    no_unwind
;

// unwrap
#[verifier::inline]
pub open spec fn spec_unwrap<T, E: core::fmt::Debug>(result: Result<T, E>) -> T
    recommends
        result is Ok,
{
    result->Ok_0
}

#[verifier::when_used_as_spec(spec_unwrap)]
pub assume_specification<T, E: core::fmt::Debug>[ Result::<T, E>::unwrap ](
    result: Result<T, E>,
) -> (t: T)
    requires
        result is Ok,
    ensures
        t == result->Ok_0,
;

// unwrap_err
#[verifier::inline]
pub open spec fn spec_unwrap_err<T: core::fmt::Debug, E>(result: Result<T, E>) -> E
    recommends
        result is Err,
{
    result->Err_0
}

#[verifier::when_used_as_spec(spec_unwrap_err)]
pub assume_specification<T: core::fmt::Debug, E>[ Result::<T, E>::unwrap_err ](
    result: Result<T, E>,
) -> (e: E)
    requires
        result is Err,
    ensures
        e == result->Err_0,
;

// unwrap_unchecked
pub assume_specification<T, E>[ Result::<T, E>::unwrap_unchecked ](result: Result<T, E>) -> T
    requires
        result is Ok,
    returns
        result->Ok_0,
;

// unwrap_err_unchecked
pub assume_specification<T, E>[ Result::<T, E>::unwrap_err_unchecked ](result: Result<T, E>) -> E
    requires
        result is Err,
    returns
        result->Err_0,
;

// expect
#[verifier::inline]
pub open spec fn spec_expect<T, E: core::fmt::Debug>(result: Result<T, E>, msg: &str) -> T
    recommends
        result is Ok,
{
    result->Ok_0
}

#[verifier::when_used_as_spec(spec_expect)]
pub assume_specification<T, E: core::fmt::Debug>[ Result::<T, E>::expect ](
    result: Result<T, E>,
    msg: &str,
) -> (t: T)
    requires
        result is Ok,
    ensures
        t == result->Ok_0,
;

// expect_err
/// Returns the error value when `result` is `Err`.
#[verifier::inline]
pub open spec fn spec_expect_err<T: core::fmt::Debug, E>(result: Result<T, E>, msg: &str) -> E
    recommends
        result is Err,
{
    result->Err_0
}

#[verifier::when_used_as_spec(spec_expect_err)]
pub assume_specification<T: core::fmt::Debug, E>[ Result::<T, E>::expect_err ](
    result: Result<T, E>,
    msg: &str,
) -> E
    requires
        result is Err,
    returns
        result->Err_0,
;

// map
pub assume_specification<T, E, U, F: FnOnce(T) -> U>[ Result::<T, E>::map ](
    result: Result<T, E>,
    op: F,
) -> (mapped_result: Result<U, E>)
    requires
        result.is_ok() ==> op.requires((result->Ok_0,)),
    ensures
        result.is_ok() ==> mapped_result.is_ok() && op.ensures(
            (result->Ok_0,),
            mapped_result->Ok_0,
        ),
        result.is_err() ==> mapped_result == Result::<U, E>::Err(result->Err_0),
;

// map_err
#[verusfmt::skip]
pub assume_specification<T, E, F, O: FnOnce(E) -> F>[Result::<T, E>::map_err](result: Result<T, E>, op: O) -> (mapped_result: Result<T, F>)
    requires
        result.is_err() ==> op.requires((result->Err_0,)),
    ensures
        result.is_err() ==> mapped_result.is_err() && op.ensures(
            (result->Err_0,),
            mapped_result->Err_0,
        ),
        result.is_ok() ==> mapped_result == Result::<T, F>::Ok(result->Ok_0);

// map_or
pub assume_specification<T, E, U, F: FnOnce(T) -> U>[ Result::<T, E>::map_or ](
    result: Result<T, E>,
    default: U,
    f: F,
) -> (res: U)
    requires
        result is Ok ==> f.requires((result->Ok_0,)),
    ensures
        result is Ok ==> f.ensures((result->Ok_0,), res),
        result is Err ==> res == default,
;

// map_or_else
pub assume_specification<T, E, U, D: FnOnce(E) -> U, F: FnOnce(T) -> U>[ Result::map_or_else ](
    result: Result<T, E>,
    default: D,
    f: F,
) -> (res: U)
    requires
        result is Err ==> default.requires((result->Err_0,)),
        result is Ok ==> f.requires((result->Ok_0,)),
    ensures
        result is Err ==> default.ensures((result->Err_0,), res),
        result is Ok ==> f.ensures((result->Ok_0,), res),
;

// is_ok_and
pub assume_specification<T, E, F: FnOnce(T) -> bool>[ Result::<T, E>::is_ok_and ](
    result: Result<T, E>,
    f: F,
) -> (res: bool)
    requires
        result is Ok ==> f.requires((result->Ok_0,)),
    ensures
        result is Err ==> !res,
        result is Ok ==> f.ensures((result->Ok_0,), res),
;

// is_err_and
pub assume_specification<T, E, F: FnOnce(E) -> bool>[ Result::<T, E>::is_err_and ](
    result: Result<T, E>,
    f: F,
) -> (res: bool)
    requires
        result is Err ==> f.requires((result->Err_0,)),
    ensures
        result is Ok ==> !res,
        result is Err ==> f.ensures((result->Err_0,), res),
;

// inspect
pub assume_specification<T, E, F: FnOnce(&T)>[ Result::<T, E>::inspect ](
    result: Result<T, E>,
    f: F,
) -> (res: Result<T, E>)
    requires
        result is Ok ==> f.requires((&result->Ok_0,)),
    ensures
        res == result,
        result is Ok ==> f.ensures((&result->Ok_0,), ()),
;

// inspect_err
pub assume_specification<T, E, F: FnOnce(&E)>[ Result::<T, E>::inspect_err ](
    result: Result<T, E>,
    f: F,
) -> (res: Result<T, E>)
    requires
        result is Err ==> f.requires((&result->Err_0,)),
    ensures
        res == result,
        result is Err ==> f.ensures((&result->Err_0,), ()),
;

// and
/// Denotes `next` when `result` is `Ok`, otherwise the `Err` of `result`.
#[verifier::inline]
pub open spec fn spec_and<T, E, U>(result: Result<T, E>, next: Result<U, E>) -> Result<U, E> {
    match result {
        Ok(_) => next,
        Err(e) => Err(e),
    }
}

#[verifier::when_used_as_spec(spec_and)]
pub assume_specification<T, E, U>[ Result::<T, E>::and ](
    result: Result<T, E>,
    next: Result<U, E>,
) -> Result<U, E>
    returns
        spec_and(result, next),
;

// and_then
pub assume_specification<T, E, U, F: FnOnce(T) -> Result<U, E>>[ Result::<T, E>::and_then ](
    result: Result<T, E>,
    op: F,
) -> (res: Result<U, E>)
    requires
        result is Ok ==> op.requires((result->Ok_0,)),
    ensures
        result is Ok ==> op.ensures((result->Ok_0,), res),
        result is Err ==> res == Err(result->Err_0),
;

// or
/// Denotes the `Ok` of `result` when `result` is `Ok`, otherwise `next`.
#[verifier::inline]
pub open spec fn spec_or<T, E, F>(result: Result<T, E>, next: Result<T, F>) -> Result<T, F> {
    match result {
        Ok(t) => Ok(t),
        Err(_) => next,
    }
}

#[verifier::when_used_as_spec(spec_or)]
pub assume_specification<T, E, F>[ Result::<T, E>::or ](
    result: Result<T, E>,
    next: Result<T, F>,
) -> Result<T, F>
    returns
        spec_or(result, next),
;

// or_else
pub assume_specification<T, E, F, O: FnOnce(E) -> Result<T, F>>[ Result::<T, E>::or_else ](
    result: Result<T, E>,
    op: O,
) -> (res: Result<T, F>)
    requires
        result is Err ==> op.requires((result->Err_0,)),
    ensures
        result is Ok ==> res == Ok(result->Ok_0),
        result is Err ==> op.ensures((result->Err_0,), res),
;

// unwrap_or
/// Denotes the `Ok` payload, or `default` when `result` is `Err`.
#[verifier::inline]
pub open spec fn spec_unwrap_or<T, E>(result: Result<T, E>, default: T) -> T {
    match result {
        Ok(t) => t,
        Err(_) => default,
    }
}

#[verifier::when_used_as_spec(spec_unwrap_or)]
pub assume_specification<T, E>[ Result::<T, E>::unwrap_or ](result: Result<T, E>, default: T) -> T
    returns
        spec_unwrap_or(result, default),
;

// unwrap_or_else
pub assume_specification<T, E, F: FnOnce(E) -> T>[ Result::<T, E>::unwrap_or_else ](
    result: Result<T, E>,
    op: F,
) -> (res: T)
    requires
        result is Err ==> op.requires((result->Err_0,)),
    ensures
        result is Ok ==> res == result->Ok_0,
        result is Err ==> op.ensures((result->Err_0,), res),
;

// unwrap_or_default
pub assume_specification<T: core::default::Default, E>[ Result::<T, E>::unwrap_or_default ](
    result: Result<T, E>,
) -> (res: T)
    ensures
        result is Ok ==> res == result->Ok_0,
        result is Err ==> T::default.ensures((), res),
;

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
    no_unwind
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
    no_unwind
;

// transpose
/// Swaps the `Result` and the inner `Option`; `Ok(None)` becomes `None`.
#[verifier::inline]
pub open spec fn spec_transpose<T, E>(result: Result<Option<T>, E>) -> Option<Result<T, E>> {
    match result {
        Ok(Some(t)) => Some(Ok(t)),
        Ok(None) => None,
        Err(e) => Some(Err(e)),
    }
}

#[verifier::when_used_as_spec(spec_transpose)]
pub assume_specification<T, E>[ Result::<Option<T>, E>::transpose ](
    result: Result<Option<T>, E>,
) -> Option<Result<T, E>>
    returns
        spec_transpose(result),
;

// flatten
/// Denotes the inner `Result` when `result` is `Ok`, otherwise the outer `Err`.
#[verifier::inline]
pub open spec fn spec_flatten<T, E>(result: Result<Result<T, E>, E>) -> Result<T, E> {
    match result {
        Ok(inner) => inner,
        Err(e) => Err(e),
    }
}

#[verifier::when_used_as_spec(spec_flatten)]
pub assume_specification<T, E>[ Result::<Result<T, E>, E>::flatten ](
    result: Result<Result<T, E>, E>,
) -> Result<T, E>
    returns
        spec_flatten(result),
;

} // verus!
