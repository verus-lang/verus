#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

mod M1 {
    use builtin::*;

    spec fn f1(i: int) -> int {
        i + 1
    }

    pub closed spec fn f2(i: int) -> int {
        f1(i) + 1
    }

}

mod M2 {
    use crate::M1::f2;
    #[allow(unused_imports)]
    use builtin::*;

    proof fn P() {
        // assert(f2(10) == 12); // FAILS, since f2 is closed (abstract)
        assert(f2(10) == f2(10));
    }

}

} // verus!
