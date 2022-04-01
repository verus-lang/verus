use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::{*, option::Option, result::Result};

use pervasive::seq::*;
use crate::pervasive::vec::*;


#[derive(PartialEq, Eq, Structural)]
struct S<A> {
    a: A,
    b: bool,
}

fn add1(a: &mut u32) {
    requires([
        *old(a) < 10,
    ]);
    ensures([
        *a == *old(a) + 1,
    ]);
    *a = *a + 1;
}

fn foo(s: S<u32>) {
    // let mut s = s;
    let mut s = S { a: 5, b: false };
    add1(&mut s.a);
    assert(s.a == 6);
    assert(s.b == false);
    assert(s == S { a: 6, b: false });
}

fn main() {}

