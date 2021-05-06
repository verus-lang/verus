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

struct S {
    n: int,
}

#[spec]
fn id_s(s: S) -> S {
    id(s, true, s)
}
