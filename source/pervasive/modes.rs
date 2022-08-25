#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
use std::marker::PhantomData;

// TODO: the *_exec* functions would be better in builtin,
// but it's painful to implement the support in erase.rs at the moment.
#[verifier(external_body)]
pub fn ghost_exec<A>(#[spec] a: A) -> Ghost<A> {
    ensures(|s: Ghost<A>| equal(a, s.view()));
    Ghost::assume_new()
}

#[verifier(external_body)]
pub fn tracked_exec<A>(#[proof] a: A) -> Tracked<A> {
    ensures(|s: Tracked<A>| equal(a, s.view()));
    opens_invariants_none();
    Tracked::assume_new()
}

#[verifier(external_body)]
pub fn tracked_exec_borrow<'a, A>(#[proof] a: &'a A) -> &'a Tracked<A> {
    ensures(|s: Tracked<A>| equal(*a, s.view()));
    opens_invariants_none();

    // TODO: implement this (using unsafe) or mark function as ghost (if supported by Rust)
    unimplemented!();
}

verus! {

// REVIEW: consider moving these into builtin and erasing them from the VIR
pub struct Gho<A>(pub ghost A);
pub struct Trk<A>(pub tracked A);

#[inline(always)]
#[verifier(external_body)]
pub fn ghost_unwrap_gho<A>(a: Ghost<Gho<A>>) -> (ret: Ghost<A>)
    ensures a@.0 === ret@
{
    Ghost::assume_new()
}

#[inline(always)]
#[verifier(external_body)]
pub fn tracked_unwrap_gho<A>(a: Tracked<Gho<A>>) -> (ret: Tracked<A>)
    ensures a@.0 === ret@
{
    Tracked::assume_new()
}

#[inline(always)]
#[verifier(external_body)]
pub fn tracked_unwrap_trk<A>(a: Tracked<Trk<A>>) -> (ret: Tracked<A>)
    ensures a@.0 === ret@
{
    Tracked::assume_new()
}

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
