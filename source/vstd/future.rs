#![allow(unused_imports)]

use super::pervasive::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub mod lifetime_ignore {
    use std::future::Future;
    use std::marker::PhantomData;

    #[verifier::external_trait_specification]
    #[verifier::external_trait_extension(FutureSpec via FutureSpecImpl)]
    pub trait ExFuture {
        type ExternalTraitSpecificationFor: Future;

        type Output;

        spec fn view(&self) -> Self::Output;

        spec fn awaited(&self) -> bool;
    }

    pub struct DummyFuture<T> {
        pub x: T,
    }

    #[verifier::external]
    impl<T> Future for DummyFuture<T> {
        type Output = T;

        fn poll(self: std::pin::Pin<&mut Self>, _: &mut std::task::Context<'_>) -> std::task::Poll<
            <Self as std::future::Future>::Output,
        > {
            unimplemented!()
        }
    }

    impl<T> FutureSpecImpl for DummyFuture<T> {
        uninterp spec fn view(&self) -> Self::Output;

        uninterp spec fn awaited(&self) -> bool;
    }

    pub trait VerusFuture: Future {
        fn verus_await_future(self) -> (ret: Self::Output)
            ensures
                ret == self@,
            opens_invariants none
        ;
    }

    impl<T: Future> VerusFuture for T {
        #[rustc_diagnostic_item = "verus::vstd::future::lifetime_ignore::VerusFuture::verus_await_future"]
        #[verifier::external_body]
        fn verus_await_future(self) -> (ret: Self::Output)
            ensures
                ret == self@,
                self.awaited() == true,
        {
            unimplemented!()
        }
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::external_body]
    pub fn make_future<T>(x: T) -> (ret: impl Future<Output = T>)
        opens_invariants none
    {
        DummyFuture::<T> { x: x }
    }

}

pub use lifetime_ignore::*;

} // verus!
