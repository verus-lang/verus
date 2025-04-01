use vstd::prelude::*;

verus! {
    fn mutate(x: &mut u32)
        requires *old(x) > 42,
        ensures *x == *old(x) - 42,
    {
        *x -= 42;
    }
    
    fn main() {
        let mut x: u32 = 84;
        mutate(&mut x);
        assert(x == 42);
    }
}