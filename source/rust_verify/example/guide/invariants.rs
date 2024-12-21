#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

// ANCHOR: fib_spec
spec fn fib(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fib((n - 2) as nat) + fib((n - 1) as nat)
    }
}
// ANCHOR_END: fib_spec

// ANCHOR: fib_is_mono
proof fn lemma_fib_is_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        fib(i) <= fib(j),
    decreases j - i,
{
    if i < 2 && j < 2 {
    } else if i == j {
    } else if i == j - 1 {
        assert(fib(j) == fib((j - 2) as nat) + fib((j - 1) as nat));
        lemma_fib_is_monotonic(i, (j - 1) as nat);
    } else {
        lemma_fib_is_monotonic(i, (j - 1) as nat);
        lemma_fib_is_monotonic(i, (j - 2) as nat);
    }
}
// ANCHOR_END: fib_is_mono

/*
// ANCHOR: fib_impl_no_proof
fn fib_impl(n: u64) -> (result: u64)
    requires
        fib(n as nat) <= 0xffff_ffff_ffff_ffff
    ensures
        result == fib(n as nat),
{
    if n == 0 {
        return 0;
    }
    let mut prev: u64 = 0;
    let mut cur: u64 = 1;
    let mut i: u64 = 1;
    while i < n
    {
        i = i + 1;
        let new_cur = cur + prev;
        prev = cur;
        cur = new_cur;
    }
    cur
}
// ANCHOR_END: fib_impl_no_proof
*/

// ANCHOR: fib_final
exec fn fib_impl(n: u64) -> (result: u64)
    requires
        fib_fits_u64(n as nat),
    ensures
        result == fib(n as nat),
{
    if n == 0 {
        return 0;
    }
    let mut prev: u64 = 0;
    let mut cur: u64 = 1;
    let mut i: u64 = 1;
    while i < n
        invariant
            0 < i <= n,
            fib_fits_u64(n as nat),
            fib_fits_u64(i as nat),
            cur == fib(i as nat),
            prev == fib((i - 1) as nat),
    {
        i = i + 1;
        proof {
            lemma_fib_is_monotonic(i as nat, n as nat);
        }
        let new_cur = cur + prev;
        prev = cur;
        cur = new_cur;
    }
    cur
}
// ANCHOR_END: fib_final

fn main() {
}

} // verus!

