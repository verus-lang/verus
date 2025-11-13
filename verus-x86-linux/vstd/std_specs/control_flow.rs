use super::super::prelude::*;
use core::convert::Infallible;
use core::ops::ControlFlow;
use core::ops::FromResidual;
use core::ops::Try;

verus! {

#[verifier::external_type_specification]
#[verifier::accept_recursive_types(B)]
#[verifier::reject_recursive_types_in_ground_variants(C)]
pub struct ExControlFlow<B, C>(ControlFlow<B, C>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExInfallible(Infallible);

pub assume_specification<T, E>[ Result::<T, E>::branch ](result: Result<T, E>) -> (cf: ControlFlow<
    <Result<T, E> as Try>::Residual,
    <Result<T, E> as Try>::Output,
>)
    ensures
        cf === match result {
            Ok(v) => ControlFlow::Continue(v),
            Err(e) => ControlFlow::Break(Err(e)),
        },
;

pub assume_specification<T>[ Option::<T>::branch ](option: Option<T>) -> (cf: ControlFlow<
    <Option<T> as Try>::Residual,
    <Option<T> as Try>::Output,
>)
    ensures
        cf === match option {
            Some(v) => ControlFlow::Continue(v),
            None => ControlFlow::Break(None),
        },
;

pub assume_specification<T>[ Option::<T>::from_residual ](option: Option<Infallible>) -> (option2:
    Option<T>)
    ensures
        option.is_none(),
        option2.is_none(),
;

pub uninterp spec fn spec_from<S, T>(value: T, ret: S) -> bool;

pub broadcast proof fn spec_from_blanket_identity<T>(t: T, s: T)
    ensures
        #[trigger] spec_from::<T, T>(t, s) ==> t == s,
{
    admit();
}

pub assume_specification<T, E, F: From<E>>[ Result::<T, F>::from_residual ](
    result: Result<Infallible, E>,
) -> (result2: Result<T, F>)
    ensures
        match (result, result2) {
            (Err(e), Err(e2)) => spec_from::<F, E>(e, e2),
            _ => false,
        },
;

pub broadcast group group_control_flow_axioms {
    spec_from_blanket_identity,
}

} // verus!
