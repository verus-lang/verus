use vstd::prelude::*;

verus! {

#[verifier::try_broadcasts]
proof fn uses_unreferenced_dependency_broadcast() {
    let xs = seq![seq![1int, 2], seq![3]];
    assert(xs.push(seq![5]).flatten() =~= xs.flatten() + seq![5]);
}

} // verus!
