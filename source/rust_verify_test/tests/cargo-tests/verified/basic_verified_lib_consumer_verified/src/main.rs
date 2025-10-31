use vstd::prelude::*;
use basic_verified_lib::*;

verus! {

fn main() {
    let x = double(42);
    assert(x == 84);
}

} // verus!
