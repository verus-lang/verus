use builtin::*;
use builtin_macros::*;

verus! {
    // Polymorphic specification: returns a value combined with itself in a type-dependent way
    spec fn spec0<A,B>(pair:(A,B)) -> B
    {
       pair.1
    }


    // Proof demonstrating polymorphic symbolic reasoning
    #[verifier::spinoff_prover]
    #[verifier::mono]
    proof fn proof1() {
        assert(spec0((3int, 4int)) == 4int);        // 3 + 3 = 6    // 1.5 + 1.5 = 3.0

         // 4 does not equal 5
    }

    // Proof with symbolic polymorphism involving scaling
}

fn main() {}
