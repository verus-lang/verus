#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
use vstd::prelude::*;

verus! {

// ANCHOR: spec
spec fn triangle(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
    }
}

// ANCHOR_END: spec
/*
// ANCHOR: bogus
spec fn bogus(i: int) -> int {
    bogus(i) + 1 // FAILS, error due to nontermination
}
// ANCHOR_END: bogus

// ANCHOR: exploit_bogus
proof fn exploit_bogus()
    ensures
        false,
{
    assert(bogus(3) == bogus(3) + 1);
}
// ANCHOR_END: exploit_bogus
*/

/*
// ANCHOR: lacks_fuel
fn test_triangle_fail() {
    assert(triangle(0) == 0); // succeeds
    assert(triangle(10) == 55); // FAILS
}
// ANCHOR_END: lacks_fuel
*/

// ANCHOR: step_by_step
fn test_triangle_step_by_step() {
    assert(triangle(0) == 0);
    assert(triangle(1) == 1);
    assert(triangle(2) == 3);
    assert(triangle(3) == 6);
    assert(triangle(4) == 10);
    assert(triangle(5) == 15);
    assert(triangle(6) == 21);
    assert(triangle(7) == 28);
    assert(triangle(8) == 36);
    assert(triangle(9) == 45);
    assert(triangle(10) == 55);  // succeeds
}
// ANCHOR_END: step_by_step

// ANCHOR: fuel
fn test_triangle_reveal() {
    proof {
        reveal_with_fuel(triangle, 11);
    }
    assert(triangle(10) == 55);
}
// ANCHOR_END: fuel

// ANCHOR: fuel_by
fn test_triangle_assert_by() {
    assert(triangle(10) == 55) by {
        reveal_with_fuel(triangle, 11);
    }
}
// ANCHOR_END: fuel_by

// ANCHOR: min
spec fn min(x: int, y: int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}
// ANCHOR_END: min

/*
// ANCHOR: rec_fail
fn rec_triangle(n: u32) -> (sum: u32)
    ensures
        sum == triangle(n as nat),
{
    if n == 0 {
        0
    } else {
        n + rec_triangle(n - 1) // FAILS: possible overflow
    }
}
// ANCHOR_END: rec_fail
*/

// ANCHOR: rec
fn rec_triangle(n: u32) -> (sum: u32)
    requires
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        sum == triangle(n as nat),
{
    if n == 0 {
        0
    } else {
        n + rec_triangle(n - 1)
    }
}
// ANCHOR_END: rec

// ANCHOR: mut
fn mut_triangle(n: u32, sum: &mut u32)
    requires
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        *sum == triangle(n as nat),
{
    if n == 0 {
        *sum = 0;
    } else {
        mut_triangle(n - 1, sum);
        *sum = *sum + n;
    }
}
// ANCHOR_END: mut

/*
// ANCHOR: tail_fail
fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
    requires
        idx <= n,
        *old(sum) == triangle(idx as nat),
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        *sum == triangle(n as nat),
{
    if idx < n {
        let idx = idx + 1;
        *sum = *sum + idx;
        tail_triangle(n, idx, sum);
    }
}
// ANCHOR_END: tail_fail
*/

// ANCHOR: mono
proof fn triangle_is_monotonic(i: nat, j: nat)
    ensures
        i <= j ==> triangle(i) <= triangle(j),
    decreases j,
{
    // We prove the statement `i <= j ==> triangle(i) <= triangle(j)`
    // by induction on `j`.

    if j == 0 {
        // The base case (`j == 0`) is trivial since it's only
        // necessary to reason about when `i` and `j` are both 0.
        // So no proof lines are needed for this case.
    }
    else {
        // In the induction step, we can assume the statement is true
        // for `j - 1`. In Verus, we can get that fact into scope with
        // a recursive call substituting `j - 1` for `j`.

        triangle_is_monotonic(i, (j - 1) as nat);

        // Once we know it's true for `j - 1`, the rest of the proof
        // is trivial.
    }
}

// ANCHOR_END: mono
/*
// ANCHOR: circular
proof fn circular_reasoning()
    ensures
        false,
{
    circular_reasoning(); // FAILS, does not terminate
}
// ANCHOR_END: circular
*/

// ANCHOR: tail
fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
    requires
        idx <= n,
        *old(sum) == triangle(idx as nat),
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        *sum == triangle(n as nat),
{
    if idx < n {
        let idx = idx + 1;
        assert(*sum + idx < 0x1_0000_0000) by {
            triangle_is_monotonic(idx as nat, n as nat);
        }
        *sum = *sum + idx;
        tail_triangle(n, idx, sum);
    }
}
// ANCHOR_END: tail

// ANCHOR: loop
fn loop_triangle(n: u32) -> (sum: u32)
    requires
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        sum == triangle(n as nat),
{
    let mut sum: u32 = 0;
    let mut idx: u32 = 0;
    while idx < n
        invariant
            idx <= n,
            sum == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
    {
        idx = idx + 1;
        assert(sum + idx < 0x1_0000_0000) by {
            triangle_is_monotonic(idx as nat, n as nat);
        }
        sum = sum + idx;
    }
    sum
}
// ANCHOR_END: loop

// ANCHOR: loop_return
fn loop_triangle_return(n: u32) -> (sum: u32)
    ensures
        sum == triangle(n as nat) || (sum == 0xffff_ffff && triangle(n as nat) >= 0x1_0000_0000),
{
    let mut sum: u32 = 0;
    let mut idx: u32 = 0;
    while idx < n
        invariant
            idx <= n,
            sum == triangle(idx as nat),
    {
        idx = idx + 1;
        if sum as u64 + idx as u64 >= 0x1_0000_0000 {
            proof {
                triangle_is_monotonic(idx as nat, n as nat);
            }
            return 0xffff_ffff;
        }
        sum = sum + idx;
    }
    sum
}
// ANCHOR_END: loop_return

#[verusfmt::skip]
// ANCHOR: loop_break
fn loop_triangle_break(n: u32) -> (sum: u32)
    ensures
        sum == triangle(n as nat) || (sum == 0xffff_ffff && triangle(n as nat) >= 0x1_0000_0000),
{
    let mut sum: u32 = 0;
    let mut idx: u32 = 0;
    while idx < n
        invariant_except_break
            idx <= n,
            sum == triangle(idx as nat),
        ensures
            sum == triangle(n as nat) || (sum == 0xffff_ffff && triangle(n as nat) >= 0x1_0000_0000),
    {
        idx = idx + 1;
        if sum as u64 + idx as u64 >= 0x1_0000_0000 {
            proof {
                triangle_is_monotonic(idx as nat, n as nat);
            }
            sum = 0xffff_ffff;
            break;
        }
        sum = sum + idx;
    }
    sum
}
// ANCHOR_END: loop_break

// ANCHOR: ackermann
spec fn ackermann(m: nat, n: nat) -> nat
    decreases m, n,
{
    if m == 0 {
        n + 1
    } else if n == 0 {
        ackermann((m - 1) as nat, 1)
    } else {
        ackermann((m - 1) as nat, ackermann(m, (n - 1) as nat))
    }
}

proof fn test_ackermann() {
    reveal_with_fuel(ackermann, 12);
    assert(ackermann(3, 2) == 29);
}
// ANCHOR_END: ackermann

// ANCHOR: even
spec fn abs(i: int) -> int {
    if i < 0 {
        -i
    } else {
        i
    }
}

spec fn is_even(i: int) -> bool
    decreases abs(i),
{
    if i == 0 {
        true
    } else if i > 0 {
        is_odd(i - 1)
    } else {
        is_odd(i + 1)
    }
}

spec fn is_odd(i: int) -> bool
    decreases abs(i),
{
    if i == 0 {
        false
    } else if i > 0 {
        is_even(i - 1)
    } else {
        is_even(i + 1)
    }
}

proof fn even_odd_mod2(i: int)
    ensures
        is_even(i) <==> i % 2 == 0,
        is_odd(i) <==> i % 2 == 1,
    decreases abs(i),
{
    if i < 0 {
        even_odd_mod2(i + 1);
    }
    if i > 0 {
        even_odd_mod2(i - 1);
    }
}

fn test_even() {
    proof {
        reveal_with_fuel(is_even, 11);
    }
    assert(is_even(10));
}

fn test_odd() {
    proof {
        reveal_with_fuel(is_odd, 11);
    }
    assert(!is_odd(10));
}
// ANCHOR_END: even

#[verusfmt::skip]
mod M {
use builtin::*;

spec fn abs(i: int) -> int {
    if i < 0 {
        -i
    } else {
        i
    }
}

// ANCHOR: even2
spec fn is_even(i: int) -> bool
    decreases abs(i), 0int,
{
    if i == 0 {
        true
    } else if i > 0 {
        is_odd(i - 1)
    } else {
        is_odd(i + 1)
    }
}

spec fn is_odd(i: int) -> bool
    decreases abs(i), 1int,
{
    !is_even(i)
}

proof fn even_odd_mod2(i: int)
    ensures
        is_even(i) <==> i % 2 == 0,
        is_odd(i) <==> i % 2 == 1,
    decreases abs(i),
{
    reveal_with_fuel(is_odd, 2);
    if i < 0 {
        even_odd_mod2(i + 1);
    }
    if i > 0 {
        even_odd_mod2(i - 1);
    }
}

fn test_even() {
    proof {
        reveal_with_fuel(is_even, 21);
    }
    assert(is_even(10));
}

fn test_odd() {
    proof {
        reveal_with_fuel(is_odd, 22);
    }
    assert(!is_odd(10));
}
// ANCHOR_END: even2
}

// ANCHOR: example_decreases_to
proof fn example_decreases_to(s: Seq<int>)
    requires s.len() == 5
{
    assert(decreases_to!(8int => 4int));

    // fails: can't decrease to negative number
    // assert(decreases_to!(8 => -2));

    // Comma-separated elements are treated lexicographically:
    assert(decreases_to!(12int, 8int, 1int => 12int, 4int, 50000int));

    // Datatypes decrease-to their fields:
    let x = Some(8int);
    assert(decreases_to!(x => x->0));

    let y = (true, false);
    assert(decreases_to!(y => y.0));

    // fails: tuples are not treated lexicographically
    // assert(decreases_to!((20, 9) => (11, 15)));

    // sequence decreases-to an element of the sequence
    assert(decreases_to!(s => s[2]));

    // sequence decreases-to a subrange of the sequence
    assert(decreases_to!(s => s.subrange(1, 3)));
}
// ANCHOR_END: example_decreases_to

fn main() {
}

} // verus!
