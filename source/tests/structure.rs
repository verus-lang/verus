use builtin::*;
use builtin_macros::*;

verus! {
    // Polymorphic specification: returns a value combined with itself in a type-dependent way
    pub struct Mystery<A>{
        v: A
    }
    impl<A> Mystery<A>{
        spec fn hello<B>(self, b:B)->(A,B){
            (self.v,b)
        }
    
    }
    proof fn proof1() {
        assert(Mystery { v: 1int }.hello(2int) == (1int, 2int));        

    }


}

fn main() {}
