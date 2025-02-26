#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
use vstd::prelude::*;

verus! {

// ANCHOR: compute_sum_fails
fn compute_sum_fails(x: u64, y: u64) -> (result: u64)
    ensures
        result == x + y,
{
    x + y
}
// ANCHOR_END: compute_sum_fails

// ANCHOR: compute_sum_limited
fn compute_sum_limited(x: u64, y: u64) -> (result: u64)
    requires
        x < 1000000,
        y < 1000000,
    ensures
        result == x + y,
{
    x + y
}
// ANCHOR_END: compute_sum_limited

// ANCHOR: compute_sum_runtime_check
fn compute_sum_runtime_check(x: u64, y: u64) -> (result: Option<u64>)
    ensures
        match result {
            Some(z) => z == x + y,
            None => x + y > u64::MAX,
        },
{
    x.checked_add(y)
}
// ANCHOR_END: compute_sum_runtime_check

// ANCHOR: fib_checked
fn fib_checked(n: u64) -> (result: u64)
    requires
        fib(n as nat) <= u64::MAX
    ensures
        result == fib(n as nat),
{
    if n == 0 {
        return 0;
    }
    let mut prev: CheckedU64 = CheckedU64::new(0);
    let mut cur: CheckedU64 = CheckedU64::new(1);
    let mut i: u64 = 1;
    while i < n
        invariant
            0 < i <= n,
            fib(n as nat) <= u64::MAX,
            cur@ == fib(i as nat),
            prev@ == fib((i - 1) as nat),
    {
        i = i + 1;
        let new_cur = cur.add_checked(&prev);
        prev = cur;
        cur = new_cur;
    }
    cur.unwrap()
}
// ANCHOR_END: fib_checked

// ANCHOR: fib_checked_no_precondition
fn fib_checked_no_precondition(n: u64) -> (result: Option<u64>)
    ensures
        match result {
            Some(x) => x == fib(n as nat),
            None => fib(n as nat) > u64::MAX,
        },
{
    if n == 0 {
        return Some(0);
    }
    let mut prev: CheckedU64 = CheckedU64::new(0);
    let mut cur: CheckedU64 = CheckedU64::new(1);
    let mut i: u64 = 1;
    while i < n
        invariant
            0 < i <= n,
            cur@ == fib(i as nat),
            prev@ == fib((i - 1) as nat),
    {
        i = i + 1;
        let new_cur = cur.add_checked(&prev);
        prev = cur;
        cur = new_cur;
    }
    cur.to_option()
}
// ANCHOR_END: fib_checked_no_precondition

fn main() {
}

} // verus!

