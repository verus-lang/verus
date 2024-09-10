use super::prelude::*;

verus! {

    // This file implements refinement types using tracked values.
    // In particular, RefinedT<T, P> and RefinedG<T, P> are values
    // of type T for which the P predicate holds, for tracked and
    // ghost values, respectively.  RefinedG must be tracked, since
    // otherwise the choose operator could be used to make up a
    // value of type RefinedG<T, P> with a P that never holds.
    //
    // The implementations of RefinedT and RefinedG are trusted:
    // they rely on the fact that only the Refined{T,G}::alloc()
    // functions construct or modify values of type Refined{T,G}<>,
    // and they require that the predicate hold of the value used.
    // In particular, the Refined{T,G}<>::validate() methods are
    // assumed correct using #[verifier::external_body].

    pub tracked struct RefinedT<T, P> {
        tracked v: T,
        ghost m: std::marker::PhantomData<P>,
    }

    pub tracked struct RefinedG<T, P> {
        ghost v: T,
        ghost m: std::marker::PhantomData<P>,
    }

    pub trait RefinedPred<T> {
        spec fn valid(v: T) -> bool;
    }

    impl<T, P> RefinedT<T, P> where P: RefinedPred<T> {
        pub proof fn alloc(tracked v: T) -> (tracked r: RefinedT<T, P>)
            requires
                P::valid(v)
            ensures
                r@ == v
        {
            RefinedT::<T, P>{
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

        pub proof fn take(tracked self) -> (result: T)
            ensures
                result == self@,
                P::valid(result),
        {
            self.validate();
            self.v
        }
    }

    impl<T, P> RefinedG<T, P> where P: RefinedPred<T> {
        pub proof fn alloc(v: T) -> (tracked r: RefinedG<T, P>)
            requires
                P::valid(v)
            ensures
                r@ == v
        {
            RefinedG::<T, P>{
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

        pub proof fn take(tracked self) -> (result: T)
            ensures
                result == self@,
                P::valid(result),
        {
            self.validate();
            self.v
        }
    }
}
