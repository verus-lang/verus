use builtin::*;
mod pervasive;
use pervasive::*;

#[proof]
#[verifier(external_body)]
fn bit_and_property(){
    ensures([
        forall(|a: int, b: int| #[trigger] (a&b) == b&a),
        forall(|a: int, b: int, c:int| #[trigger] ((a&b)&c) == a&(b&c)),
        forall(|a: int| #[trigger] (a&a) == a),
        forall(|a: int| #[trigger] (a&0) == 0),
    ]);
}

#[proof]
fn test9(b1: u32, b2:u32, b3:u32) { 
    bit_and_property();
    assert_bit_vector(b1 & 0xff < 0x100);
    assert(0xff & b1 < 0x100);

    assert(0 <= (b1 & b1) as int);
    assert((b1 & b1) as int <= 0xffffffffu32);

    // assert( (b1&b2)&b3 == b1&(b2&b3) );
    // assert(b1&0 == 0);
    // assert(0&b2 == 0);

}

fn main() {}