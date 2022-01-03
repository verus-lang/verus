use builtin::*;
mod pervasive;
use pervasive::*;

// pub fn concat64() ->  {
//     unimplemented!();
// }

// #[spec]
// fn modulo_8(i: int) -> int {
// 	i % 8
// }

#[exec]
// #[verifier(bit_vector)]
fn and_7(b: u32, c: u32) -> u32 {
   requires(b > 0);
	// ensures(|ret: u32| ret == b + 1);
   // assert_bit_vector(b & 7 == b % 8);
   assert_bit_vector(b + c == c + b);
   // assert(b + 1 == 1 + b);
	// let mut c: u32 = b + 1;
   // c = c * 1;
   b + 1
}

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
 
// #[proof]
// fn concat_and_split(u1:u64, u2:u64){
//    ensures(bv128_to_u64(u64_to_bv128(u1,u2)) == (u1,u2));
// }
 
// #[proof]
// fn split_property(u1:u64, u2:u64){
//    ensures(bv2int(u64_to_bv128(u1,u2)) == (u1 as int) * 0x10000000000000000 + (u2 as int));
// }



fn main() { }
