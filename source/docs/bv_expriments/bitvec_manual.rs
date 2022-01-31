use builtin::*;
mod pervasive;
use pervasive::*;


// just a wrapper for assert_bit_vector

#[proof]
fn bit_and_commutes(x: u32, y: u32) {
    ensures(x & y == y & x);
    assert_bit_vector(x & y == y & x);
}

#[proof]
fn bit_and_associative(a: u32, b: u32, c:u32) {
    ensures((a&b)&c == a&(b&c));
    assert_bit_vector((a&b)&c == a&(b&c));
}

#[proof]
fn bit_and_idempotent(a: u32) {
    ensures(a&a == a);
    assert_bit_vector(a&a == a);
}

#[proof]
fn test9(b1: u32, b2:u32, b3:u32) { 
    assert_bit_vector(b1 & 0xff < 0x100);
    bit_and_commutes(b1, 0xff);
    assert(0xff & b1 < 0x100);

    bit_and_idempotent(b2);
    assert(b2&b2 == b2);
}

fn main() { }