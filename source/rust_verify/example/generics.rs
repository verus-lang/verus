extern crate builtin;
use builtin::*;
mod pervasive;
use pervasive::*;

fn main() {}

#[spec]
fn f<A>(a1: A, a2: A) -> bool {
    true
}

#[spec]
fn id<A, B>(a: A, b: B, c: A) -> A {
    a
}

fn id_exec<A, B>(a: A, b: B, c: A) -> A {
    requires(f(a, c));
    ensures(|r: A| f(r, a));

    a
}

#[spec]
fn id_int(i: int) -> int {
    id(i, true, 10)
}

#[spec]
fn id_u64(i: u64) -> u64 {
    id(i, true, 10)
}

fn id_u64_exec(i: u64) -> u64 {
    ensures(|r: u64| r == id_u64(i));

    id(i, true, 10)
}

struct S<A> {
    n: A,
}

#[spec]
fn s_property<B>(s: S<B>) -> int {
    7
}

#[spec]
fn id_s(s: S<int>) -> S<int> {
    id(s, true, s)
}

#[proof]
fn s_prop1(x: S<int>, y: S<int>) {
    assert(s_property(x) == s_property(y));
}

#[proof]
fn s_prop2<C>(x: S<C>, y: S<C>) {
    assert(s_property(x) == s_property(y));
}

#[spec]
#[opaque]
fn g<A>(a: A) -> A {
    a
}

#[proof]
fn test_g1(u: u8) {
    reveal(g::<u8>); // REVIEW: should reveal quantify over all A?
    assert(g(u) == u);
}

#[proof]
fn test_g2(u: u8) {
    assert(g(u) < 256);
}
