extern crate builtin;
use builtin::*;
mod pervasive;
use pervasive::*;

fn main() {}

fn test1(i: int, n: nat, u: u8) {
    assert(n >= 5);
}

