// Sample for lifetime checking of a native raw pointer dereference (assign).
// See sample_assign.mir for the (annotated) MIR used for Verus's lifetime checking.
//
// Generated with:
//   verus sample_assign.rs --no-verify --no-erasure-check -Zdump-mir=PromoteTemps -Zdump-mir-dir=<dir>
// (the MIR is the 'PromoteTemps.before' dump of `test`)

use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

struct Node {
    next: *mut Pair,
}

struct Pair {
    f: u64,
    g: u64,
}

fn test(a: *mut Node, Tracked(ma): Tracked<&PointsTo<Node>>, Tracked(mb): Tracked<PointsTo<Pair>>)
    requires
        ma.is_init(),
        ma.ptr() == a,
        mb.is_init(),
        mb.ptr() == ma.value().next,
{
    #[verifier::permission("a")]
    let tracked ma = ma;
    #[verifier::permission("a.next")]
    let tracked mut mb = mb;

    unsafe {
        (*(*a).next).f = 5;
    }
}

} // verus!

fn main() {}
