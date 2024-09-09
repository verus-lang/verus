use super::prelude::*;

verus! {

    // This file implements refinement types for tracked values.
    // In particular, Refined<T, P> is a tracked T for which the
    // P predicate holds.

    pub tracked struct Refined<T, P> {
        tracked v: T,
        ghost m: std::marker::PhantomData<P>,
    }

    pub trait RefinedPred<T> {
        spec fn valid(v: T) -> bool;
    }

    impl<T, P> Refined<T, P> where P: RefinedPred<T> {
        pub proof fn alloc(tracked v: T) -> (tracked r: Refined<T, P>)
            requires
                P::valid(v)
            ensures
                r@ == v
        {
            Refined::<T, P>{
                v: v,
                m: std::marker::PhantomData,
            }
        }

        pub closed spec fn view(self) -> T {
            self.v
        }

        #[verifier::external_body]
        pub proof fn validate(tracked &self)
            ensures
                P::valid(self@)
        {
        }

        pub proof fn take(tracked self) -> (tracked r: T)
            ensures
                P::valid(r)
        {
            self.validate();
            self.v
        }
    }
}
