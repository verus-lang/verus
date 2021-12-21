use builtin::*;
mod pervasive;
use pervasive::*;

pub fn concat64() ->  {
    unimplemented!();
}

#[spec]
fn modulo_8(i: int) -> int {
	i % 8
}

#[exec]
fn and_7(b: u32) -> u32 {
	ensures(|ret: u32| ret == modulo_8(b));
	b & 7
}

#[exec]
fn bv128_to_u64(b: bv128) -> (u64, u64){
   let lower_mask:bv128 = 0x00000000000000001111111111111111;
   let u1:u64 = ((b >> 64) & lower_mask) as u64 ;
   let u2:u64 = (b & lower_mask) as u64;
   (u1, u2)
}
 
// gets two u64 and returns one bv128  "concat"
#[exec]
fn u64_to_bv128(u1:u64, u2:u64) -> bv128{
   let b:bv128 = 0;
   let b1 = u1 as bv128;
   let b2 = u2 as bv128;
   b = b | b1 | (b2 << 64);
   b
}
 
#[proof]
fn concat_and_split(u1:u64, u2:u64){
   ensures(bv128_to_u64(u64_to_bv128(u1,u2)) == (u1,u2));
}
 
#[proof]
fn split_property(u1:u64, u2:u64){
   ensures(bv2int(u64_to_bv128(u1,u2)) == (u1 as int) * 0x10000000000000000 + (u2 as int));
}



fn main() { }
