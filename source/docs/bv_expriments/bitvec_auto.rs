use builtin::*;
mod pervasive;
use pervasive::*;

#[verifier(bit_vector)]
#[proof]
fn bit_and32_auto(){
    ensures([
        forall(|a: u32, b: u32| #[trigger] (a&b) == b&a),
        forall(|a: u32, b: u32, c:u32| #[trigger] ((a&b)&c) == a&(b&c)),
        forall(|a: u32| #[trigger] (a&a) == a),
        forall(|a: u32| #[trigger] (a&0) == 0),
        forall(|a: u32| #[trigger] (a& 0xffffffffu32) == a),
    ]);
}

#[verifier(bit_vector)]
#[proof]
fn bit_not32_auto(){
    ensures([
        forall(|a: u32| #[trigger] !(!a) == a),
    ]);
}

#[proof]
fn test9(b1: u32, b2:u32, b3:u32) { 
    bit_and32_auto();

    assert_bit_vector(b1 & 0xff < 0x100);
    assert(0xff & b1 < 0x100);

    assert(0 <= (b1 & b1) as int);
    assert((b1 & b1) as int <= 0xffffffffu32);

    assert( (b1&b2)&b3 == b1&(b2&b3) );
    assert(b1&0 == 0);
    assert(0&b2 == 0);

    bit_not32_auto();
    assert(!(!5u32) == 5u32);
}

fn main() {}