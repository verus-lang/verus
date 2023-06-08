use vstd::prelude::*;

verus! {
pub open spec fn divides (m:int, n:int) -> bool {
    n % m == 0
}
}