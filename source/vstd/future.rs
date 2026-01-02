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
    spec fn view(&self) -> T;

    spec fn awaited(&self) -> bool;

    fn exec_await(self) -> (ret: T)
        ensures
            self.awaited() == true,
            ret == self@,
        opens_invariants any
    ;
}

impl<V, T: Future<Output = V>> FutureAdditionalSpecFns<V> for T {
    uninterp spec fn view(&self) -> V;

    uninterp spec fn awaited(&self) -> bool;

    #[verifier::external_body]
    fn exec_await(self) -> (ret: V)
        ensures
            self.awaited() == true,
            ret == self@,
    {
        unimplemented!()
    }
}

} // verus!
