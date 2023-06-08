use vstd::prelude::*;

verus!{

pub open spec fn divides (m:int, n:int) -> bool {
    n % m == 0
}

// what does this mean? 
// error: non-private spec function must be marked open or closed 
// to indicate whether the function body is public (pub open) or private (pub closed)

pub open  spec fn prime (n:int) -> bool {
    n >= 2 && forall|i: int| 2 <= i < n ==> !divides(i, n)
}

}