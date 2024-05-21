#[allow(unused_imports)]
use prelude::*;
#[allow(unused_imports)]
use seq::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::*;

verus! {

spec fn divides(factor: nat, candidate: nat) -> bool
    recommends
        1 <= factor,
{
    candidate % factor == 0
}

spec fn is_prime(candidate: nat) -> bool {
    &&& 1 < candidate
    &&& forall|factor: nat| 1 < factor < candidate ==> !divides(factor, candidate)
}

fn test_prime(candidate: u64) -> (result: bool)
    requires
        1 < candidate,
    ensures
        result == is_prime(candidate as nat),
{
    let mut factor: u64 = 2;
    while factor < candidate
        invariant
            1 < factor,
            forall|smallerfactor: nat|
                1 < smallerfactor < factor ==> !divides(smallerfactor, candidate as nat),
    {
        if candidate % factor == 0 {
            assert(divides(factor as nat, candidate as nat));
            return false;
        }
        factor = factor + 1;
    }
    true
}

fn main() {
}

} // verus!
