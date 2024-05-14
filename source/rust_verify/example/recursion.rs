use builtin::*;
use builtin_macros::*;
#[allow(unused_imports)]
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {

spec fn arith_sum_int(i: int) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else {
        i + arith_sum_int(i - 1)
    }
}

#[verifier::opaque]
spec fn arith_sum_u64(i: u64) -> u64
    decreases i,
{
    if i == 0 {
        0
    } else {
        (i + arith_sum_u64((i - 1) as u64)) as u64
    }
}

proof fn arith_sum_int_nonneg(i: nat)
    ensures
        arith_sum_int(i as int) >= 0,
    decreases i,
{
    if i > 0 {
        arith_sum_int_nonneg((i - 1) as nat);
    }
}

proof fn arith_sum_test1() {
    assert(arith_sum_int(0) == 0);
    // Recursive functions default to 1 fuel, so without the assert above,
    // the following assert will fail
    assert(arith_sum_int(1) == 1);
    assert(arith_sum_int(2) == 3);
    assert(arith_sum_int(3) == 6);
}

proof fn arith_sum_test2() {
    // Instead of writing out intermediate assertions,
    // we can instead boost the fuel setting
    reveal_with_fuel(arith_sum_int, 4);
    assert(arith_sum_int(3) == 6);
}

proof fn arith_sum_test3() {
    reveal_with_fuel(arith_sum_u64, 4);
    assert(arith_sum_u64(3) == 6);
}

proof fn arith_sum_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        arith_sum_int(i as int) <= arith_sum_int(j as int),
    decreases j,
{
    if i < j {
        arith_sum_monotonic(i, (j - 1) as nat);
    }
}

fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        n < 100,
    ensures
        arith_sum_int(n as int) == sum,
{
    let mut sum: u64 = 0;
    for i in 0..n
        invariant
            n < 100,
            arith_sum_int(i as int) == sum,
            sum <= 100 * i,
    {
        sum = sum + (i + 1);
    }
    sum
}

fn run_arith_sum(n: u64) -> u64 {
    let mut result: u64 = 0;
    if n < 100 {
        result = compute_arith_sum(n);
    }
    result
}

fn exec_with_decreases(n: u64) -> u64
    decreases 100 - n,
{
    if n < 100 {
        exec_with_decreases(n + 1)
    } else {
        n
    }
}

} // verus!
fn main() {
    let args = std::env::args();
    for arg in args {
        if let Ok(n) = arg.parse::<u64>() {
            println!("{}", run_arith_sum(n));
        }
    }
}
