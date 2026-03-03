use vstd::prelude::*;
use transitive1::*;

verus! {

pub fn test2()
    requires test1()
{ }

#[inline(never)]
pub fn b() {
    c();
}

} // verus!
