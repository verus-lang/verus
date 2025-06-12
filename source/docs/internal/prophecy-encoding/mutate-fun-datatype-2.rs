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
        y: u32,
        z: u32,
        q: u32,
    }

    fn mutate(x: &mut u32, y: &mut u32)
        requires *old(x) > 42, *old(y) > 21,
        ensures *x == *old(x) - 42, *y == *old(y) - 21,
    {
        *x -= 42;
        *y -= 21;
    }
    
    fn main() {
        let mut x: S = S { y: 84, z: 84, q: 84 };
        mutate(&mut x.y, &mut x.z);
        assert(x.y == 42);
        assert(x.z == 63);
    }
// }
}