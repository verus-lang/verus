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

#[verifier::external_trait_specification]
pub trait ExResidual<O>: Sized {
    type ExternalTraitSpecificationFor: core::ops::Residual<O>;
}

/// The result of `?` need not have a canonical representation.
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(TrySpec via TrySpecImpl)]
pub trait ExTry: FromResidual<Self::Residual> {
    type ExternalTraitSpecificationFor: Try;

    type Output;

    type Residual: core::ops::Residual<Self::Output>;

    /// The result of `branch` matches its functional spec
    spec fn branch_model_is_valid() -> bool;

    spec fn branch_model(self) -> ControlFlow<Self::Residual, Self::Output> where Self: Sized;

    fn branch(self) -> (ret: ControlFlow<Self::Residual, Self::Output>) where Self: Sized
        ensures
            Self::branch_model_is_valid() ==> ret == Self::branch_model(self),
    ;

    fn from_output(output: Self::Output) -> Self where Self: Sized;
}

#[verifier::external_trait_specification]
pub trait ExFromResidual<R> {
    type ExternalTraitSpecificationFor: FromResidual<R>;

    fn from_residual(residual: R) -> Self where Self: Sized;
}

/// We can provide stronger guarantees for types that obey these laws
pub open spec fn try_laws<R: Try>() -> bool {
    &&& R::branch_model_is_valid()
    &&& forall|output: R::Output, result: R|
        #![auto]
        R::from_output.ensures((output,), result) ==> R::branch_model(result)
            == ControlFlow::Continue(output)
    &&& forall|residual: R::Residual, result: R|
        #![auto]
        <R as FromResidual<R::Residual>>::from_residual.ensures((residual,), result)
            ==> R::branch_model(result) == ControlFlow::Break(residual)
}

impl<T> TrySpecImpl for Option<T> {
    open spec fn branch_model_is_valid() -> bool {
        true
    }

    open spec fn branch_model(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            Some(v) => ControlFlow::Continue(v),
            None => ControlFlow::Break(None),
        }
    }
}

impl<T, E> TrySpecImpl for Result<T, E> {
    open spec fn branch_model_is_valid() -> bool {
        true
    }

    open spec fn branch_model(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            Ok(v) => ControlFlow::Continue(v),
            Err(e) => ControlFlow::Break(Err(e)),
        }
    }
}

impl<B, C> TrySpecImpl for ControlFlow<B, C> {
    open spec fn branch_model_is_valid() -> bool {
        true
    }

    open spec fn branch_model(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            ControlFlow::Continue(v) => ControlFlow::Continue(v),
            ControlFlow::Break(e) => ControlFlow::Break(ControlFlow::Break(e)),
        }
    }
}

pub broadcast proof fn lemma_option_try_laws<T>()
    ensures
        #[trigger] try_laws::<Option<T>>(),
{
}

pub broadcast proof fn lemma_result_try_laws<T, E>()
    ensures
        #[trigger] try_laws::<Result<T, E>>(),
{
}

pub broadcast proof fn lemma_control_flow_try_laws<B, C>()
    ensures
        #[trigger] try_laws::<ControlFlow<B, C>>(),
{
}

pub assume_specification<T, E>[ Result::<T, E>::branch ](result: Result<T, E>) -> (cf: ControlFlow<
    <Result<T, E> as Try>::Residual,
    <Result<T, E> as Try>::Output,
>)
    ensures
        cf == match result {
            Ok(v) => ControlFlow::Continue(v),
            Err(e) => ControlFlow::Break(Err(e)),
        },
;

pub assume_specification<T, E>[ Result::<T, E>::from_output ](
    output: <Result<T, E> as Try>::Output,
) -> (ret: Result<T, E>)
    ensures
        ret == Ok(output),
;

pub assume_specification<T>[ Option::<T>::from_output ](output: <Option<T> as Try>::Output) -> (ret:
    Option<T>)
    ensures
        ret == Some(output),
;

pub assume_specification<B, C>[ ControlFlow::<B, C>::from_output ](
    output: <ControlFlow<B, C> as Try>::Output,
) -> (ret: ControlFlow<B, C>)
    ensures
        ret == ControlFlow::Continue(output),
;

pub assume_specification<B, C>[ ControlFlow::<B, C>::branch ](cf: ControlFlow<B, C>) -> (ret:
    ControlFlow<<ControlFlow<B, C> as Try>::Residual, <ControlFlow<B, C> as Try>::Output>)
    ensures
        ret == match cf {
            ControlFlow::Continue(output) => ControlFlow::Continue(output),
            ControlFlow::Break(residual) => ControlFlow::Break(ControlFlow::Break(residual)),
        },
;

pub assume_specification<T>[ Option::<T>::branch ](option: Option<T>) -> (cf: ControlFlow<
    <Option<T> as Try>::Residual,
    <Option<T> as Try>::Output,
>)
    ensures
        cf == match option {
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

pub assume_specification<B, C>[ ControlFlow::<B, C>::from_residual ](
    residual: ControlFlow<B, Infallible>,
) -> (ret: ControlFlow<B, C>)
    ensures
        match residual {
            ControlFlow::Break(value) => ret == ControlFlow::Break(value),
            ControlFlow::Continue(_) => false,
        },
;

pub uninterp spec fn spec_from<S, T>(value: T, ret: S) -> bool;

pub broadcast axiom fn spec_from_blanket_identity<T>(t: T, s: T)
    ensures
        #[trigger] spec_from::<T, T>(t, s) ==> t == s,
;

pub assume_specification<T, E, F: From<E>>[ Result::<T, F>::from_residual ](
    result: Result<Infallible, E>,
) -> (result2: Result<T, F>)
    ensures
        match (result, result2) {
            (Err(e), Err(e2)) => spec_from::<F, E>(e, e2) && call_ensures(F::from, (e,), e2),
            _ => false,
        },
;

pub broadcast group group_control_flow_axioms {
    spec_from_blanket_identity,
    lemma_option_try_laws,
    lemma_result_try_laws,
    lemma_control_flow_try_laws,
}

} // verus!
