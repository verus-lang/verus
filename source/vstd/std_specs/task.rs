use super::super::prelude::*;
use core::task::{Context, Poll};

verus! {

#[verifier::external_type_specification]
#[verifier::accept_recursive_types(T)]
pub struct ExPoll<T>(Poll<T>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExContext<'a>(Context<'a>);

} // verus!
