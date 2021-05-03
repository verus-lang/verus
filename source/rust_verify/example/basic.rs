extern crate builtin;
use builtin::*;

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

#[spec]
fn f1(i: int, j: int) -> bool {
    i <= j
}

#[spec]
fn f2(i: int, j: int) -> bool {
    i < j
}

#[spec]
#[opaque]
fn f3(i: int, j: int) -> bool {
    f1(j, i)
}

fn test_spec_fn(a: int, b: int) {
    hide(f2);

    assume(f2(a, b));
    reveal(f2);
    assert(f1(a, b));

    reveal(f3);
    assert(f3(b, a));
    assert(f3(a, b)); // FAILS
}

fn affirm(b: bool) {
    requires(b);

    assert(b);
}

fn test_requires1(a: int, b: int, c: int) {
    requires([a <= b, b <= c]);

    assert(a <= c);
}

fn test_requires2(a: int, b: int, c: int) {
    assume(a <= b);
    assume(b <= c);
    test_requires1(a + a, b + b, c + c);
    test_requires1(a + a, b + b, a + c); // FAILS
}

fn test_requires3(a: int, b: int, c: int) {
    assume(a <= b);
    assume(b <= c);
    test_requires1(a + a, b + b, c + c);
    test_requires1(a + c, b + b, c + c); // FAILS
}

fn test_ret(a: int, b: int) -> int {
    requires(a <= b);
    ensures(|ret: int| [
        ret <= a + b,
        ret <= a + a, // FAILS
        ret <= b + b,
    ]);

    a + b
}

fn test_ret2(a: int, b: int) -> int {
    requires(a <= b);
    ensures(|ret: int| [
        ret <= a + b,
        ret <= a + a,
        ret <= b + b,
    ]);

    let mut x = test_ret(a, a);
    x = test_ret(x, x);
    assert(x <= 4 * a);
    x = test_ret(b, b);
    x = test_ret(x, x);
    assert(x <= 4 * b);
    x = test_ret(a + 1, a + 2);
    x = test_ret(x + 3, x + 4);
    assert(x <= 4 * a + 4 + 6);
    x = test_ret(a, b);
    x
}
