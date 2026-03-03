use vstd::prelude::*;

verus! {

spec fn fib(x: nat) -> nat
    decreases x,
{
    if x == 0 {
        0
    } else if x == 1 {
        1
    } else {
        fib((x - 1) as nat) + fib((x - 2) as nat)
    }
}

fn test() {
    // Find a setting that needs a larger than average rlimit (in debug mode)
    //assert(fib(15) == 610) by (compute_only);
    //assert(fib(20) == 6765) by (compute_only);
    //assert(fib(25) == 75025) by (compute_only);
    assert(fib(26) == 121393) by (compute_only);
    //assert(fib(27) == 196418) by (compute_only);
    //assert(fib(28) == 317811) by (compute_only);
    //assert(fib(30) == 832040) by (compute_only);
    //assert(fib(100) == 354224848179261915075) by (compute_only);
}



} // verus!
