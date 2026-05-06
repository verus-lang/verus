use vstd::prelude::*;

verus! {


// Library function for use in verified and unverified functions
pub fn double(x: u16) -> (z: u32)
    ensures z == x * 2,
{
    x as u32 + x as u32
}

// Some corner cases that have been problematic for cargo-verus in the past

trait Trait: View {}

impl<T: View> Trait for Option<T> {}

fn test(f:spec_fn(nat) -> nat) {
}


mod IsNotRegressionIssue1573 {
    enum Test {
        A,
        B,
    }

    spec fn is_not_a(t: Test) -> bool {
        t !is A
    }

    spec fn is_a(t: Test) -> bool {
        t is A
    }
}

} // verus!
