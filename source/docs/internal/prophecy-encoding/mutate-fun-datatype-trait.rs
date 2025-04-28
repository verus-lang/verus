use builtin::*;
use builtin_macros::*;

verus! {
// mod A {
//     use super::*;
//     pub struct Q<Y> {
//         y: Y,
//     }
// 
//     pub fn new_q() -> Q<u64> {
//         Q { y: 0 }
//     }
// } 

// mod B {
//
    struct S<A> {
        y: A,
    }

    fn mutate(x: &mut S<u64>)
        requires old(x).y > 42,
        ensures x.y == old(x).y - 42,
    {
        x.y = x.y - 42;
    }

    trait X {
        spec fn inv(&self) -> bool;

        fn mutate(&self, x: &mut S<u64>)
            requires
                self.inv(),
                old(x).y > 42,
            ensures x.y == old(x).y - 42;
    }

    struct Z {
        v: u64,
    }

    impl X for Z {
        spec fn inv(&self) -> bool {
            self.v == 42
        }

        fn mutate(&self, x: &mut S<u64>) {
            x.y = x.y - self.v;
        }
    }
    
    fn main() {
        let mut x: S<u64> = S { y: 84 };
        let z = Z { v: 42 };
        z.mutate(&mut x);
        assert(x.y == 42);
    }
// }
}