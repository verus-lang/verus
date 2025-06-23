use builtin::*;
use builtin_macros::*;

verus! {
    struct S {
        y: bool,
    }
    
    impl S {
        proof fn mutate(tracked &mut self)
            requires old(self) == (S { y: true }),
            ensures self == (S { y: true }),
        {
        }
    }

    
    // fn main() {
    //     let mut x: Tracked<S> = Tracked(S { y: true });
    //     mutate(Tracked(x.borrow_mut()));
    //     assert(!x@.y);
    // }
}