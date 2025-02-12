use vstd::prelude::*;

verus! {
    fn a(i: u64) -> (r: u64)
        ensures r == i
        // decreases i
    {
        if i == 0 {
            return 0;
        } else {
            return 1 + a(i - 1);
        }
    }
    
}