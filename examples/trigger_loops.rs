// rust_verify/tests/example.rs ignore --- these examples are expected to timeout to test the quantifier profiler (i.e., exceed their rlimit)
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{pervasive::*, *};

verus! {

// ANCHOR: def_f_g
spec fn f(x: nat, y: nat) -> bool;

spec fn g(x: nat) -> bool;

spec fn h(x: nat, y: nat) -> bool;
// ANCHOR_END: def_f_g

spec fn j(x: nat) -> bool;

proof fn quantifier_example()
    requires
        forall|x| g(x),
    ensures
        exists|y| g(y),
{
    let w = choose|z| g(z);
    assert(g(w));
}

proof fn choose_example()
    requires
        exists|x| g(x),
{
    let z = choose|y| g(y);
    assert(g(z));
}

proof fn cost_example()
    requires
        f(1, 2),
        forall|x, y| #[trigger] f(x, y) <==> g(x) && g(y),
        forall|z| #[trigger] g(z) == j(z + 2),
{
    assert(j(3) && j(4));
}

proof fn cost_example2()
    requires
        g(1),
        g(2),
        forall|x, y| f(x, y) <==> #[trigger] g(x) && #[trigger] g(y),
        forall|z| #[trigger] g(z) == j(z + 2),
{
    assert(j(3) && j(4));
}

proof fn trigger_forever()
    requires
        forall|x: nat, y: nat| f(x + 1, 2 * y) && f(2 * x, y + x) || f(y, x) ==> #[trigger] f(x, y),
    ensures
        forall|x: nat, y: nat| x > 2318 && y < 100 ==> f(x, y),
{
}

// Split the triggering over two different quantifiers
// ANCHOR: trigger_forever2
proof fn trigger_forever2()
    requires
        forall|x: nat| g(x),
        forall|x: nat, y: nat| h(x, y) == f(x, y),
        forall|x: nat, y: nat| f(x + 1, 2 * y) && f(2 * x, y + x) || f(y, x) ==> #[trigger] f(x, y),
    ensures
        forall|x: nat, y: nat| x > 2318 && y < 100 ==> h(x, y),
{
    assert(g(4));
}
// ANCHOR_END: trigger_forever2

fn simple_loop()
    ensures
        forall|x| 0 <= x < 10 ==> g(x),
{
    let mut x: u32 = 0;
    while x < 10
        invariant
            0 <= x <= 10,
            forall|i: u32| 0 <= i < x ==> g(i as nat),
    //decreases x;
    {
        assume(g(x as nat));
        x = x + 1;
    }
}

fn bad_loop()
    requires
        forall|x: nat, y: nat| f(x + 1, 2 * y) && f(2 * x, y + x) || f(y, x) ==> #[trigger] f(x, y),
{
    let mut x = 10;
    while x > 10
        invariant
            forall|x: nat, y: nat|
                f(x + 1, 2 * y) && f(2 * x, y + x) || f(y, x) ==> #[trigger] f(x, y),
    //decreases x;
    {
        x = x - 1;
        assert(forall|x: nat, y: nat| x > 2318 && y < 100 ==> f(x, y));
    }
}

fn main() {
}

} // verus!
