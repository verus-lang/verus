use vstd::prelude::*;

verus! {

pub open spec fn test1() -> bool { true }   

#[inline(never)]
pub fn c() {}

} // verus!
