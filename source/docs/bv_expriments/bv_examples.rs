use builtin::*;
mod pervasive;
use pervasive::*;

// TODO: concat and bit-select function as builtin (directly translate into z3)
fn concat32(b1: u32, b2: u32) -> u64 {
}

fn extract(high: u32, low: u32, b:u32) -> u32 {    
   // return type u(high-low+1) OR
   // return the same width from input, and move the selected bits to the lowest
   // but second approach will give a type mismatch for "split"
} 

fn split(b:u64) -> (u32, u32){
   (extract(63,32,b), extract(31,0,b))
}

#[proof]
fn concat_and_split32(u1:u32, u2:u32){
   ensures(split(concat(u1,u2)) == (u1,u2));
}

#[proof]
fn concat_and_split64(u1:u64, u2:u64){
   ensures(split(concat(u1,u2)) == (u1,u2));
}
 
#[proof]
fn concat_property(u1:u64, u2:u64){
   ensures(concat(u1,u2) == u1 * 0x10000000000000000 + u2);
}




// TODO: bitvector function mode 
#[verifier(bit_vector)]
#[exec]
fn bitvec_mode_example(b: u32) -> u32 {
   assert(b + 1 == 1 + b);
   b
}


#[verifier(bit_vector)]
#[exec]
fn shift_by_2(b: u32) -> u32 {
   requires(b < 0x1000);
   ensures(|ret: u32| ret == b * 4);
   b << 2
}

// #[exec]
// fn bit_assert_example2(b: u32) -> u32 {
//    assert_bit_vector(b+1 == b);     
//    // assert_bit_vector(0xff & b < 0x100);
//    // assert_bit_vector(0x100 > b & 0xff);
//    // assert_bit_vector(0x90 + 0x10 > 0xff & b);
//    // assert(0x100 > b & 0xff);
   
//    b + 1
// }


// #[exec]
// fn bv128_to_u64(b: bv128) -> (u64, u64){
//    let lower_mask:bv128 = 0x00000000000000001111111111111111;
//    let u1:u64 = ((b >> 64) & lower_mask) as u64 ;
//    let u2:u64 = (b & lower_mask) as u64;
//    (u1, u2)
// }
 
// // gets two u64 and returns one bv128  "concat"
// #[exec]
// fn u64_to_bv128(u1:u64, u2:u64) -> bv128{
//    let b:bv128 = 0;
//    let b1 = u1 as bv128;
//    let b2 = u2 as bv128;
//    b = b | b1 | (b2 << 64);
//    b
// }




fn main() { }
