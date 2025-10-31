use vstd::prelude::*;
use transitive2::*;

verus! {

fn test3() {
    test2();
}

#[inline(never)]
fn a() {
    b();
    //c();
}

} // verus!
