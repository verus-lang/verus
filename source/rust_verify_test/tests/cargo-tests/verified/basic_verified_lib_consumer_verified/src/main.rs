use vstd::prelude::*;
use basic_verified_lib::*;

verus! {

fn main() {
    let x = double(42);
    assert(x == 84);
    let _x = opaque_hidden();
}

} // verus!
