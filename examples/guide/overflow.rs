// rust_verify/tests/example.rs expect-warnings
#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use verus_builtin_macros::*;
use vstd::prelude::*;

verus! {

/*
// ANCHOR: compute_sum_fails
fn compute_sum_fails(x: u64, y: u64) -> (result: u64)
    ensures
        result == x + y,
{
    x + y  // error: possible arithmetic underflow/overflow
}
// ANCHOR_END: compute_sum_fails
*/

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
// ANCHOR: compute_sum_runtime_check

fn main() {
}

} // verus!

