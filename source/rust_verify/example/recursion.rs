extern crate builtin;
use builtin::*;
mod pervasive;
use pervasive::*;

fn main() {}

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

