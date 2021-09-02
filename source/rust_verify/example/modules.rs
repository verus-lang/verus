extern crate builtin;
use builtin::*;
mod pervasive;
use pervasive::*;

fn main() {}

mod M1 {
    use builtin::*;

    #[spec]
    fn f1(i: int) -> int {
        i + 1
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn f2(i: int) -> int {
        f1(i) + 1
    }
}

mod M2 {
    use M1::f2;
    use builtin::*;
    use pervasive::*;

    #[proof]
    fn P() {
        // assert(f2(10) == 12); // FAILS, since f2 is abstract
        assert(f2(10) == f2(10));
    }
}
