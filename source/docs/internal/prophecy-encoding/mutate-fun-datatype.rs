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
    struct S {
        y: u64,
    }

    fn mutate(x: &mut S)
        requires old(x).y > 42,
        ensures x.y == old(x).y - 42,
    {
        x.y = x.y - 42;
    }
    
    fn main() {
        let mut x: S = S { y: 84 };
        mutate(&mut x);
        assert(x.y == 42);
    }
// }
}