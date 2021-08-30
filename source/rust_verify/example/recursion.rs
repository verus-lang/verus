extern crate builtin;
use builtin::*;
mod pervasive;
use pervasive::*;

#[spec]
fn arith_sum_int(i: int) -> int {
    decreases(i);

    if i <= 0 { 0 } else { i + arith_sum_int(i - 1) }
}

#[spec]
#[opaque]
fn arith_sum_u64(i: u64) -> u64 {
    decreases(i);

    if i == 0 { 0 } else { i + arith_sum_u64(i - 1) }
}

#[proof]
fn arith_sum_int_nonneg(i: nat) {
    ensures(arith_sum_int(i) >= 0);
    decreases(i);

    if i > 0 {
        arith_sum_int_nonneg(i - 1);
    }
}

#[proof]
fn arith_sum_test1() {
    assert(arith_sum_int(0) == 0);
    // Recursive functions default to 1 fuel, so without the assert above,
    // the following assert will fail
    assert(arith_sum_int(1) == 1);  
    assert(arith_sum_int(2) == 3);
    assert(arith_sum_int(3) == 6);
}

#[proof]
fn arith_sum_test2() {
    // Instead of writing out intermediate assertions, 
    // we can instead boost the fuel setting
    reveal_with_fuel(arith_sum_int, 4);
    assert(arith_sum_int(3) == 6);
}

#[proof]
fn arith_sum_test3() {
    reveal_with_fuel(arith_sum_u64, 4);
    assert(arith_sum_u64(3) == 6);
}

#[proof]
fn arith_sum_monotonic(i: nat, j: nat) {
    requires(i <= j);
    ensures(arith_sum_int(i) <= arith_sum_int(j));
    decreases(j);

    if i < j {
        arith_sum_monotonic(i, j - 1);
    }
}

fn compute_arith_sum(n: u64) -> u64 {
    requires(n < 100);
    ensures(|ret: u64| arith_sum_int(n) == ret);

    let mut i: u64 = 0;
    let mut sum: u64 = 0;
    while i < n {
        invariant([
            n < 100,
            i <= n,
            arith_sum_int(i) == sum,
            sum <= 100 * i,
        ]);

        i = i + 1;
        sum = sum + i;
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

#[verifier(external)]
fn main() {
    let args = std::env::args();
    for arg in args {
        if let Ok(n) = arg.parse::<u64>() {
            println!("{}", run_arith_sum(n));
        }
    }
}
