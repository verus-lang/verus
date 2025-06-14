use builtin::*;
use builtin_macros::*;

verus! {
    struct S {
        y: bool,
    }

    fn mutate(Tracked(x): Tracked<&mut S>)
        ensures x.y == !old(x).y,
    {
        proof {
            x.y = !x.y;
        }
    }
    
    fn main() {
        let mut x: Tracked<S> = Tracked(S { y: true });
        mutate(Tracked(x.borrow_mut()));
        assert(!x@.y);
    }
}