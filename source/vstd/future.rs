#![feature(rustc_attrs)]
#![allow(unused_imports)]

use super::prelude::*;
use core::future::*;

verus! {

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(FutureSpec via FutureSpecImpl)]
pub trait ExFuture {
    type ExternalTraitSpecificationFor: core::future::Future;

    type Output;

    /// Whether awaiting this future returns its prophetic view.
    spec fn obeys_deterministic_future_laws(&self) -> bool;

    /// The value that awaiting this future will return.
    #[verifier::prophetic]
    spec fn view(&self) -> Self::Output;

    /// Whether this future has been awaited.
    #[verifier::prophetic]
    spec fn awaited(&self) -> bool;
}

// Do not call this function. Call the regular Rust `await` keyword instead.
#[verifier::external_body]
fn exec_await<F: Future>(
    #[allow(unused_variables)]
    future: F,
) -> (ret: F::Output)
    ensures
        future.awaited() == true,
        future.obeys_deterministic_future_laws() ==> ret == future@,
    opens_invariants any
{
    unimplemented!()
}

} // verus!
