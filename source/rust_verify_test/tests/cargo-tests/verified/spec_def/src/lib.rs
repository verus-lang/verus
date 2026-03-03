use vstd::prelude::*;

verus! {


// Spec function for use in verified functions
pub open spec fn double(x: u16) -> (z: int)
{
    x + x
}

pub fn concrete_a(x: u16) -> u16 
    requires double(x) < 100,
{
    x
}


} // verus!
