use builtin::*;
mod pervasive;
use pervasive::*;

// bit_and as trigger 
// use `bit_and` when you want bit-vector properties to be triggered
#[spec]
fn bit_and(x: int, y:int) -> int {
    x & y
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
fn bit_and_property(){
    ensures([
        forall(|a: int, b: int| bit_and(a,b) == bit_and(b,a)),
        forall(|a: int, b: int, c:int| bit_and(bit_and(a,b),c) == bit_and(a,bit_and(b,c))),
        forall(|a: int| bit_and(a,0) == 0),
        forall(|a: int| bit_and(a,a) == a),
        // forall(|a: int| bit_and(a, 0xffffffff) == a), 
    ]);
}

#[proof]
fn test9(b1: u32, b2:u32, b3:u32) { 
    assert_bit_vector(b1 & 0xff < 0x100);
    assert(bit_and(b1, 0xff)  < 0x100); // here bit_and triggers bit_and_property
    assert(0xff & b1 < 0x100);

    assert(bit_and(b1,0) == 0);
    assert(0 & b1 == 0);

    assert(bit_and(b1,b1) == b1);
    assert(b1 & b1 == b1);
}


fn main() {}