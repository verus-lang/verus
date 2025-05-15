use vstd::prelude::*;

verus! {

use vstd::simple_pptr::PPtr;

// ** each executable line is preceded by a comment with the equivalent regular rust unsafe code **

fn main() {
    // owned ghost state

    // pptr1 = new long int
    let (pptr1, Tracked(perm1)) = PPtr::<u64>::empty();
    // let (pptr2, Tracked(perm2), Tracked(dealloc2)) = PPtr::<u64>::empty();

    // *pptr1 = 5;
    pptr1.put(Tracked(&mut perm1), 5);
    assert(perm1.value() == 5);

    // long x = *pptr1;
    let x: u64 = *pptr1.borrow(Tracked(&perm1));
    // let y: &u64 = pptr2.borrow(Tracked(&perm2));
    // let z = *x + *y;
    // assert(z == 10);

    // free pptr1
    let _ = pptr1.into_inner(Tracked(perm1));

    // long y = *pptr1; // <- read after free
    // let z: u64 = *pptr1.borrow(Tracked(&perm1));
}

} // verus!
