#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
use std::marker::PhantomData;

#[verifier(external_body)]
pub struct Ghost<#[verifier(strictly_positive)] A> {
    phantom: PhantomData<A>,
}

#[verifier(external_body)]
pub struct Tracked<#[verifier(strictly_positive)] A> {
    phantom: PhantomData<A>,
}

impl<A> Ghost<A> {
    fndecl!(pub fn value(self) -> A);

    #[spec]
    #[verifier(external_body)]
    pub fn new(a: A) -> Ghost<A> {
        Ghost { phantom: PhantomData }
    }

    #[verifier(external_body)]
    pub fn exec(#[spec] a: A) -> Ghost<A> {
        ensures(|s: Ghost<A>| equal(a, s.value()));
        Ghost { phantom: PhantomData }
    }
}

impl<A> Tracked<A> {
    fndecl!(pub fn value(self) -> A);

    #[verifier(external_body)]
    pub fn exec(#[proof] a: A) -> Tracked<A> {
        ensures(|s: Tracked<A>| equal(a, s.value()));
        Tracked { phantom: PhantomData }
    }

    #[proof]
    #[verifier(external_body)]
    #[verifier(returns(proof))]
    pub fn get(self) -> A {
        unimplemented!()
    }
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_ghost_new<A>(a: A) {
    ensures(equal(Ghost::new(a).value(), a));
}

impl<A> Clone for Ghost<A> {
    #[verifier(external_body)]
    fn clone(&self) -> Self {
        Ghost { phantom: PhantomData }
    }
}

impl<A> Copy for Ghost<A> {
}

verus! {

pub tracked struct TrackedAndGhost<T, G>(
    pub tracked T,
    pub ghost G,
);

} // verus

// TODO: replace Spec and Proof entirely with Ghost and Tracked

#[verifier(external_body)]
pub struct Spec<#[verifier(strictly_positive)] A> {
    phantom: PhantomData<A>,
}

pub struct Proof<A>(
    #[proof] pub A,
);

impl<A> Spec<A> {
    fndecl!(pub fn value(self) -> A);

    #[verifier(external_body)]
    pub fn exec(#[spec] a: A) -> Spec<A> {
        ensures(|s: Spec<A>| equal(a, s.value()));
        Spec { phantom: PhantomData }
    }

    #[proof]
    #[verifier(returns(proof))]
    #[verifier(external_body)]
    pub fn proof(a: A) -> Spec<A> {
        ensures(|s: Spec<A>| equal(a, s.value()));
        Spec { phantom: PhantomData }
    }
}

impl<A> Clone for Spec<A> {
    #[verifier(external_body)]
    fn clone(&self) -> Self {
        Spec { phantom: PhantomData }
    }
}

impl<A> Copy for Spec<A> {
}

impl<A> PartialEq for Spec<A> {
    #[verifier(external_body)]
    fn eq(&self, _rhs: &Spec<A>) -> bool {
        true
    }
}

impl<A> Eq for Spec<A> {
}

impl<A> PartialEq for Proof<A> {
    #[verifier(external_body)]
    fn eq(&self, _rhs: &Proof<A>) -> bool {
        true
    }
}

impl<A> Eq for Proof<A> {
}

#[allow(dead_code)]
#[inline(always)]
pub fn exec_proof_from_false<A>() -> Proof<A> {
    requires(false);

    Proof(proof_from_false())
}
