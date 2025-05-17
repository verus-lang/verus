// rust_verify/tests/example.rs expand-errors
#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::*;

verus! {

spec fn e() -> bool;

spec fn f() -> bool;

spec fn g() -> bool;

spec fn h() -> bool;

spec fn k(i: int) -> bool;

spec fn z() -> bool {
    (e() ==> h()) && (forall|i: int| k(i))
}

spec fn stuff() -> bool {
    f() && g() && z()
}

proof fn test()
    requires
        f(),
{
    assert(stuff());
}

proof fn test_ret()
    ensures
        z(),
{
}

pub spec fn ai(i: int) -> bool;

pub spec fn bi(i: int) -> bool;

pub spec fn ci(i: int) -> bool;

pub open spec fn all_a() -> bool {
    forall|i: int| ai(i)
}

pub open spec fn all_b() -> bool {
    forall|i: int| bi(i)
}

pub open spec fn all_c() -> bool {
    forall|i: int| ci(i)
}

pub proof fn test2(j: int)
    requires
        forall|i: int| ai(i),
        forall|i: int| (#[trigger] ai(i)) ==> bi(i),
{
    assert(ai(j) && bi(j) && ci(j));
}

pub proof fn test_let(j: int)
    requires
        ai(j + 1),
{
    assert({
        let k = j + 3;
        let r = k - 2;
        ai(r) && bi(r)
    });
}

pub proof fn test_match(m: Option<int>)
    requires
        m.is_some(),
{
    assert(match m {
        Some(x) => x == 5,
        None => false,
    });
}

pub proof fn test_match3(foo: Foo) {
    assert(match foo {
        Foo::Bar => false,
        Foo::Qux(z) => z == 0,
        Foo::Duck(w, y) => w == y,
    });
}

pub proof fn test3(a: bool, b: bool) {
    assert(a <==> b);
}

pub proof fn test_xor(a: bool, b: bool) {
    assert(a ^ b);
}

pub proof fn test4(a: Option<u8>, b: Option<u8>) {
    assert(a == b);
}

pub struct X {
    pub a: u32,
    pub b: bool,
    pub c: u64,
}

pub proof fn test5(a: X, b: X) {
    assert(a == b);
}

pub proof fn test6(a: Option<u64>, b: u64) {
    assert(a == Some(b));
}

pub proof fn test7(a: Option<u64>, b: u64) {
    assert(Some(b) == a);
}

pub proof fn test8(a: Option<u64>, b: u64) {
    assert(a === None);
}

pub proof fn test9(a: Option<u64>, b: u64) {
    assert(None === a);
}

pub proof fn test10(a: Option<u64>, b: u64) {
    assert(None === Some(b));
}

pub proof fn test11(a: u64, b: u64) {
    assert(Some(a) == Some(b));
}

#[verifier::external_body]
pub struct OpaqueDT {
    u: u64,
}

pub proof fn test12(a: OpaqueDT, b: OpaqueDT) {
    assert(a == b);
}

pub enum Foo {
    Bar,
    Qux(u64),
    Duck(u64, u64),
}

pub proof fn test13(a: Foo, b: u64) {
    assert(a == Foo::Qux(b));
}

pub proof fn test14(a: Foo, b: u64, c: u64) {
    assert(Foo::Duck(b, c) == a);
}

pub proof fn test15(a: Foo) {
    assert(a === Foo::Bar);
}

pub proof fn test16(a: Foo, b: u64) {
    assert(Foo::Bar === a);
}

pub proof fn test17(a: u64, b: u64, c: u64) {
    assert(Foo::Qux(a) === Foo::Duck(b, c));
}

pub proof fn test18(b: u64, c: u64, e: u64, f: u64) {
    assert(Foo::Duck(b, c) == Foo::Duck(e, f));
}

#[verifier::opaque]
spec fn some_opaque() -> bool {
    false
}

spec fn some_non_opaque() -> bool {
    false
}

proof fn test_opaque1() {
    assert(some_opaque());
}

proof fn test_opaque2() {
    reveal(some_opaque);
    assert(some_opaque());
}

proof fn test_opaque3() {
    hide(some_non_opaque);
    assert(some_non_opaque());
}

spec fn other(i: int) -> bool;

spec fn recursive_function(i: int, base: bool) -> bool
    decreases i,
{
    if i <= 0 {
        base
    } else {
        recursive_function(i - 1, base)
    }
}

proof fn test_rec() {
    reveal_with_fuel(recursive_function, 3);
    assert(recursive_function(3, true));  // should fail with "reached fuel limit for recursion"
}

proof fn test_rec2() {
    reveal_with_fuel(recursive_function, 4);
    assert(recursive_function(3, true));  // should pass
}

proof fn test_rec3() {
    reveal_with_fuel(recursive_function, 4);
    assert(recursive_function(3, false));
}

fn main() {
}

} // verus!
