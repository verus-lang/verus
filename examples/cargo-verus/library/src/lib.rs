use vstd::prelude::*;

verus! {

pub fn f() -> (r: u8)
    ensures
        r == 4,
{
    2 + 2
}

} // verus!
