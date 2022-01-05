use builtin::*;
mod pervasive;
use pervasive::*;


#[exec]
fn bit_assert_example(b: u32) -> u32 {
   assert_bit_vector(b & 7 == b % 8);
   assert(b & 7 == b % 8);

   assert_bit_vector(b ^ b == 0);
   assert(b ^ b == 0);

   assert_bit_vector(b & 0xff < 0x100);
   assert(b & 0xff < 0x100);
   //assert(0xff & b < 0x100);  // fails without communtativity

   assert_bit_vector(b<<2 == b*4);
   assert(b<<2 == b*4);

   assert_bit_vector(b>>1 == b/2);
   assert(b>>1 == b/2);

   assert_bit_vector(2*b - b == b);
   assert(2*b - b == b);

   assert_bit_vector(b <= b);
   assert_bit_vector(b >= b);

   assert_bit_vector(b | 0xffff >= b);
   assert(b | 0xffff >= b);

   b + 1
}
fn main() { }
