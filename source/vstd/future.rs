#![feature(rustc_attrs)]
#![allow(unused_imports)]

use super::prelude::*;
#[cfg(verus_keep_ghost)]
use super::std_specs::pin::PinAdditionalSpecFns;
use core::future::*;
use core::pin::Pin;
use core::task::{Context, Poll};

verus! {

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(FutureSpec via FutureSpecImpl)]
pub trait ExFuture {
    type ExternalTraitSpecificationFor: core::future::Future;

    type Output;

    /// Whether this future obeys the specification below on `poll`,
    /// so that awaiting it returns `view()`.
    spec fn obeys_future_laws(&self) -> bool;

    /// The value that awaiting this future will return.
    #[verifier::prophetic]
    spec fn view(&self) -> Self::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> (r: Poll<Self::Output>)
        ensures
            ({
                let m = self.mut_ref();
                &&& m.future.value().obeys_future_laws() == m.current.obeys_future_laws()
                &&& m.current.obeys_future_laws() ==> match r {
                    Poll::Ready(v) => v == m.current.view(),
                    Poll::Pending => m.future.value().view() == m.current.view(),
                }
            }),
    ;
}

pub trait FutureAdditionalSpecFns<T>: Future<Output = T> {
    /// Whether this future has been awaited.
    #[verifier::prophetic]
    spec fn awaited(&self) -> bool;
}

impl<V, T: Future<Output = V>> FutureAdditionalSpecFns<V> for T {
    #[verifier::prophetic]
    uninterp spec fn awaited(&self) -> bool;
}

// Do not call this function. Call the regular Rust `await` keyword instead.
#[verifier::external_body]
fn exec_await<F: Future>(
    #[allow(unused_variables)]
    future: F,
) -> (ret: F::Output)
    ensures
        future.awaited() == true,
        future.obeys_future_laws() ==> ret == future@,
    opens_invariants any
{
    unimplemented!()
}

} // verus!
