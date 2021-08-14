extern crate builtin;
use builtin::*;
mod pervasive;
use pervasive::*;

fn main() {}

//fn test1(i: int, n: nat, u: u8) {
//    assert(n >= 5);
//}

fn test2(i: int, n: nat, u: u8) {
    let mut x = 5;
    x = x + i;
    x = x + n;
    x = x + u;
    assert(x >= 5);
}
