extern crate builtin;
use builtin::*;
mod pervasive;
use pervasive::*;

fn main() {}

/*
fn test_params(i: int, n: nat, u: u8) {
    assert(n >= 5);
}

fn test_mutation(i: int, n: nat, u: u8) {
    let mut x = 5;
    x = x + i;
    x = x + n;
    x = x + u;
    assert(x >= 5);
}
*/

fn test_if_else(b:bool, z:int) {
    let mut x : int = 0;
    let mut y : int = z;
    x = x + y;      // 1_mutation
    if b {
        x = 2*x;    // 2_mutation
        y = x + 1;  // 3_mutation
    } else {
        x = y + 1;  // 4_mutation
        y = 7;      // 5_mutation
    }
    assert(x + y > 5); // 6_join
}

/*
fn test_loop() {
    let mut i: u64 = 10;
    let mut b1: u8 = 20;
    let mut b2: u8 = 200;
    let mut b3: u8 = 30;  // 0_entry
    i = i + 1;           // 1_mutation
    i = i - 1;           // 2_mutation

    while i < 100 {
        invariant([
            10 <= i,
            i <= 100,
            b1 as u64 == i * 2,
        ]);
                      // 3_while_begin
        assert(b1 == 5);
        i = i + 1;    // 4_mutation
        b1 = b1 + 2;  // 5_mutation
        b2 = b2 + 1;  // 6_mutation
    } // 5_while_end

    assert(true);   // 7_while_end
}
*/
