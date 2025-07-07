#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

/*
// ANCHOR: opaque
mod M1 {
    use builtin::*;

    #[verifier::opaque]
    spec fn min(x: int, y: int) -> int {
        if x <= y {
            x
        } else {
            y
        }
    }

    fn test() {
        assert(min(10, 20) == min(10, 20)); // succeeds
        assert(min(10, 20) == 10); // FAILS
        reveal(min);
        assert(min(10, 20) <= 10); // succeeds
    }

}
// ANCHOR_END: opaque
*/

}

