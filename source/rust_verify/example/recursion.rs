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

/*
#[spec]
fn arith_sum_nat(i: nat) -> nat {
    decreases(i);

    if i == 0 { 0 } else { i + arith_sum_nat(i - 1) }
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
    assert(arith_sum_int(1) == 1);
    assert(arith_sum_int(2) == 3);
    assert(arith_sum_int(3) == 6);
}

#[proof]
fn arith_sum_test2() {
    reveal_with_fuel(arith_sum_int, 4);
    assert(arith_sum_int(3) == 6);
}

#[proof]
fn arith_sum_test3() {
    reveal_with_fuel(arith_sum_u64, 4);
    assert(arith_sum_u64(3) == 6);
}

// Basic test of mutually recursive expressions
#[spec]
fn count_down_a(i:nat) -> nat {
    decreases(i);

    if i == 0 { 0 } else { 1 + count_down_b(i - 1) }
}

#[spec]
fn count_down_b(i:nat) -> nat {
    decreases(i);

    if i == 0 { 0 } else { 1 + count_down_a(i - 1) }
}

#[proof]
fn count_down_properties() {
    assert(count_down_b(0) == 0);
    assert(count_down_a(1) == 1);
}

/*
// Basic test of mutually recursive statements
#[spec]
fn count_down_a_stmt(i:nat) -> nat {
    decreases(i);

    if i == 0 {
        0 
    } else { 
        let r = count_down_b_stmt(i - 1);
        i + r
    }
}

#[spec]
fn count_down_b_stmt(i:nat) -> nat {
    decreases(i);

    if i == 0 { 
        0 
    } else { 
        count_down_a_stmt(i - 1);
        i + count_down_a_stmt(i - 1) 
    }
}
*/
*/
// Test decreases of mutually recursive expressions
#[spec]
fn count_down_a_tricky(i:nat) -> nat {
    decreases(i);

    if i == 0 { 0 } else { 1 + count_down_b_tricky(i - 1) }
}

#[spec]
fn count_down_b_tricky(i:nat) -> nat {
    decreases(5 - i);

    if i >= 5 { 0 } else { 1 + count_down_a_tricky(i + 1) }
}

//#[proof]
//fn count_down_properties() {
//    assert(count_down_b(0) == 0);
//    assert(count_down_a(1) == 1);
//}

