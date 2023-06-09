use vstd::prelude::*;

verus!{

    pub open spec fn divides (m:int, n:int) -> bool {
        n % m == 0
    }

    pub open  spec fn prime (n:int) -> bool {
        n >= 2 && forall|i: int| 2 <= i < n ==> !divides(i, n)
    }

}