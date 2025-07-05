use vstd::pervasive::runtime_assert;
use vstd::prelude::*;

verus! {

fn a_test() {
    let a = 2;
    let b = 3;
    runtime_assert(a + b == 5);
}

} // verus!
