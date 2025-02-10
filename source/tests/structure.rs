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
        assert(Mystery { v: 1int }.hello(2int) == (1int, 2int));        // 3 + 3 = 6    // 1.5 + 1.5 = 3.0

         // 4 does not equal 5
    }

    // Proof with symbolic polymorphism involving scaling
}

fn main() {}
