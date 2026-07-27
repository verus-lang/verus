use vstd::prelude::*;

verus! {

#[verifier::external_trait_specification]
#[verifier::external_trait_private_bound(spec_def::Seal)]
trait ExT {
    type ExternalTraitSpecificationFor: spec_def::T;
}

fn t_test<A: spec_def::T>(x: A) {
}

fn vt_test<A: spec_def::VT>(x: A) {
}

pub fn concrete_b(x: u16) -> u16 
    requires spec_def::double(x) < 100,
{
    x
}


pub fn concrete_caller(x: u16) -> u16 
    requires spec_def::double(x) < 100,
{
    spec_def::concrete_a(x)
}

proof fn test(x: u16) {
    // Test using two crates with the same underlying crate name (both named "spec_def" internally)
    assert(spec_def::double(x) == spec_def2::double(x) - 1);
}

} // verus!
