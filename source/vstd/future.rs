#![feature(rustc_attrs)]
#![allow(unused_imports)]

use super::prelude::*;
use core::future::*;
verus! {

#[verifier::external_trait_specification]
pub trait ExFuture {
    type ExternalTraitSpecificationFor: core::future::Future;

    type Output;
}

pub trait FutureAdditionalSpecFns<T>: Future<Output = T> {
    #[verifier::prophetic]
    spec fn view(&self) -> T;

    #[verifier::prophetic]
    spec fn awaited(&self) -> bool;
}

impl<V, T: Future<Output = V>> FutureAdditionalSpecFns<V> for T {
    #[verifier::prophetic]
    uninterp spec fn view(&self) -> V;

    #[verifier::prophetic]
    uninterp spec fn awaited(&self) -> bool;
}

// Do not call this function. Call the regular Rust `await` keyword instead.
#[verifier::external_body]
fn exec_await<F: Future>(future: F) -> (ret: F::Output)
    ensures
        future.awaited() == true,
        ret == future@,
    opens_invariants any
{
    unimplemented!()
}

} // verus!
