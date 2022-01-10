use builtin::*;
mod pervasive;
use pervasive::*;

// TODO: concat and bit-select function as builtin (directly translate into z3)
fn concat32(b1: u32, b2: u32) -> u64 {
}

fn extract(high: u32, low: u32, b:u32) -> u(high-low+1) {    
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

fn main() { }
