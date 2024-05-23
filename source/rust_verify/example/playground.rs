use builtin::*;
use builtin_macros::*;

verus! {

#[derive(PartialEq, Eq, Structural)]
struct S<A> {
    a: A,
    b: bool,
}

fn add1(a: &mut u32)
    requires
        *old(a) < 10,
    ensures
        *a == *old(a) + 1,
{
    *a = *a + 1;
}

fn foo(s: S<u32>) {
    // let mut s = s;
    let mut s = S { a: 5, b: false };
    add1(&mut s.a);
    assert(s.a == 6);
    assert(s.b == false);
    assert(s == S { a: 6u32, b: false });
}

// The following causes a trigger loop (useful for testing rlimit-related features):
//
// spec fn f(x: nat, y: nat) -> bool;
//
// proof fn goodbye_z3()
//     requires forall|x: nat, y: nat| f(x + 1, 2 * y) && f(2 * x, y + x) || f(y, x) ==> (#[trigger] f(x, y)),
//     ensures forall|x: nat, y: nat| x > 2318 && y < 100 ==> f(x, y),
// {
// }
fn main() {
}

} // verus!
