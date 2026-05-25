use vstd::prelude::*;

verus! {

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
