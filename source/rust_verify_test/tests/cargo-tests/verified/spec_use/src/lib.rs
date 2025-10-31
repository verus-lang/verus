use vstd::prelude::*;
use spec_def::*;

verus! {


pub fn concrete_b(x: u16) -> u16 
    requires double(x) < 100,
{
    x
}


pub fn concrete_caller(x: u16) -> u16 
    requires double(x) < 100,
{
    concrete_a(x)
}

} // verus!
