#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use crate::pervasive::*;

#[allow(non_camel_case_types)]

pub enum Proof<V> {
    proof(#[proof] V)
}

pub use Proof::proof;

#[allow(non_camel_case_types)]

pub enum Spec<V> {
    spec(#[spec] V)
}
pub use Spec::spec;

#[allow(dead_code)]
#[inline(always)]
pub fn exec_proof_from_false<A>() -> Proof<A> {
    requires(false);

    proof(proof_from_false())
}
