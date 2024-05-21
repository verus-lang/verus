use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn f<A>(a1: A, a2: A) -> bool {
    true
}

spec fn id<A, B>(a: A, b: B, c: A) -> A {
    a
}

fn id_exec<A, B>(a: A, b: B, c: A) -> (r: A)
    requires
        f(a, c),
    ensures
        f(r, a),
{
    a
}

spec fn id_int(i: int) -> int {
    id(i, true, 10)
}

spec fn id_u64(i: u64) -> u64 {
    id(i, true, 10)
}

fn id_u64_exec(i: u64) -> (r: u64)
    ensures
        f(r, id_u64(i)),
{
    id_exec(i, true, 10)
}

struct S<A> {
    n: A,
}

spec fn s_property<B>(s: S<B>) -> int {
    7
}

spec fn id_s(s: S<int>) -> S<int> {
    id(s, true, s)
}

proof fn s_prop1(x: S<int>, y: S<int>) {
    assert(s_property(x) == s_property(y));
}

proof fn s_prop2<C>(x: S<C>, y: S<C>) {
    assert(s_property(x) == s_property(y));
}

#[verifier::opaque]
spec fn g<A>(a: A) -> A {
    a
}

proof fn test_g1(u: u8) {
    reveal(g::<u8>);  // REVIEW: should reveal quantify over all A?
    assert(g(u) == u);
}

proof fn test_g2(u: u8) {
    assert(g(u) < 256 as int);
}

} // verus!
