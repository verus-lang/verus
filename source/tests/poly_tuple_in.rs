use builtin::*;
use builtin_macros::*;

verus! {

    spec fn spec0<A,B>(pair:(A,B)) -> B
    {
       pair.1
    }

    //We need to treat the whole krate as mono,
    proof fn proof1() {
        assert(spec0((3int, 4int)) == 4int);

    }

}

fn main() {}
