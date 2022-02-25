#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
use std::marker::PhantomData;

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

impl<V> Spec<V> {
    #[spec]
    pub fn value(self) -> V {
        match self {
            spec(v) => v
        }
    }
}

#[allow(dead_code)]
#[inline(always)]
pub fn exec_proof_from_false<A>() -> Proof<A> {
    requires(false);

    Proof(proof_from_false())
}
