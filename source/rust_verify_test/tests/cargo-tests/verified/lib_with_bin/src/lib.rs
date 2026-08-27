use vstd::prelude::*;

verus! {

pub fn double(x: u16) -> (z: u32)
    ensures z == x * 2,
{
    x as u32 + x as u32
}

} // verus!
