extern crate builtin;
use builtin::{assert, assume, imply, int};

fn main() {}

extern {
    #[spec]
    fn f(i: int, j: int) -> bool;
}

fn test1() {
    assert(true);
    assert(!false);
    assert(true && true);
    assert(true || false);
    assert(true && false); // FAILS
    assert(false);
    assert(false);
    assert(true);
}

fn test2(b: bool, x: int, y: int, z: int) {
    assert(b || !b);

    assume(b);
    assert(b);

    assert(imply(x == y, f(x, y) == f(y, x)));

    assert(x + y == y + x);

    assume(x <= y && y <= z);
    assert(x <= z);
    assert(x < z); // FAILS
}

fn test_assign(a: int, b: int) {
    let c = a + b;
    assert(c == a + b);

    let d = false;
    assert(!d);

    assert(c < a + b); // FAILS
}

fn test_assign_mut(a: int, b: int) {
    let mut c = a;
    c = c + b;
    assert(c == a + b);
    assert(c == a); // FAILS
}
