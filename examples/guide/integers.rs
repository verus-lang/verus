#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

// ANCHOR: test_u8
fn test_u8(u: u8) {
    assert(0 <= u < 256);
}
// ANCHOR_END: test_u8

// ANCHOR: test_consts
fn test_consts() {
    let u: u8 = 1u8;
    assert({
        let i: int = 2int;
        let n: nat = 3nat;
        0int <= u < i < n < 4int
    });
}
// ANCHOR_END: test_consts

// ANCHOR: test_consts_infer
fn test_consts_infer() {
    let u: u8 = 1;
    assert({
        let i: int = 2;
        let n: nat = 3;
        0 <= u < i < n < 4
    });
}
// ANCHOR_END: test_consts_infer

// ANCHOR: test_consts_large
fn test_consts_large() {
    assert({
        let i: int = 0x10000000000000000000000000000000000000000000000000000000000000000int;
        let j: int = i + i;
        j == 2 * i
    });
}
// ANCHOR_END: test_consts_large

// ANCHOR: test_coerce
fn test_coerce() {
    let u: u8 = 1;
    assert({
        let i: int = u as int;
        let n: nat = u as nat;
        u == i && u == n
    });
}
// ANCHOR_END: test_coerce

/*
// ANCHOR: test_coerce_fail
fn test_coerce_fail() {
    let v: u16 = 257;
    let u: u8 = v as u8;
    assert(u == v); // FAILS, because u has type u8 and therefore cannot be equal to 257
}
// ANCHOR_END: test_coerce_fail
*/

/*
// ANCHOR: test_sum
fn test_sum(x: u8, y: u8) {
    let sum1: u8 = x + y; // FAILS: possible overflow
}
// ANCHOR_END: test_sum
*/

// ANCHOR: test_sum2
fn test_sum2(x: u8, y: u8) {
    assert({
        let sum2: int = x + y;  // in ghost code, + returns int and does not overflow
        0 <= sum2 < 511
    });
}
// ANCHOR_END: test_sum2

// ANCHOR: test_sum3
fn test_sum3(x: u8, y: u8)
    requires
        x + y < 256,  // make sure "let sum1: u8 = x + y" can't overflow
{
    let sum1: u8 = x + y;  // succeeds
}
// ANCHOR_END: test_sum3

// ANCHOR: test_sum_mixed
fn test_sum_mixed(x: u8, y: u16) {
    assert(x + y >= y);  // x + y has type int, so the assertion succeeds
    assert(x - y <= x);  // x - y has type int, so the assertion succeeds
}
// ANCHOR_END: test_sum_mixed

/*
// ANCHOR: test_sum_add_sub
fn test_sum_add_sub(x: u8, y: u8) {
    assert(add(x, y) >= y); // FAILS: add(x, y) has type u8, so addition might overflow
    assert(sub(x, y) <= x); // FAILS: sub(x, y) has type u8, so subtraction might underflow
}
// ANCHOR_END: test_sum_add_sub
*/

fn main() {
}

} // verus!
