#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 code! {
        #[proof]
        fn test1(b: u32) {
            assert_bit_vector(b & 7 == b % 8);
            assert(b & 7 == b % 8);

            assert_bit_vector(b ^ b == 0);
            assert(b ^ b == 0);

            assert_bit_vector(b & b == b);
            assert(b & b == b);

            assert_bit_vector(b + (!b) + 1 == 0);
            assert(b + (!b) + 1 == 0);

            assert_bit_vector(b | b == b);
            assert(b | b == b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2 code! {
        #[proof]
        fn test2(b: u32) {
            assert_bit_vector(b & 0xff < 0x100);
            assert(b & 0xff < 0x100);
            //assert(0xff & b < 0x100);  // fails without communtativity

            assert_bit_vector(b<<2 == b*4);
            assert(b<<2 == b*4);
            assert(b < 256 >>= ((b<<2) as int) == (b as int) *4);

            assert_bit_vector(b>>1 == b/2);
            assert(b>>1 == b/2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3 code! {
        #[proof]
        fn test3(b: u32) {
            assert_bit_vector(2*b - b == b);
            assert(2*b - b == b);

            assert_bit_vector(b <= b);
            assert_bit_vector(b >= b);

            assert_bit_vector(b & b & b == b | b | (b ^ b));
            assert(b & b & b == b | b | (b ^ b));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test4 code! {
        #[proof]
        fn test4(u1: u32, u2:u32) {
            assert_bit_vector( (u1 as u64) << (32 as u64) | (u2 as u64)  == (u1 as u64) * 0x100000000 + (u2 as u64));
            assert( (u1 as u64) << (32 as u64) | (u2 as u64)  == (u1 as u64) * 0x100000000 + (u2 as u64));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test5 code! {
        #[proof]
        fn test5(u:u64) {
            assert_bit_vector( (u >> (32 as u64)) as u32  ==  (u / (0x100000000 as u64)) as u32);
            assert( (u >> (32 as u64)) as u32  ==  (u / (0x100000000 as u64)) as u32);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test6 code! {
        #[proof]
        fn test6(a:u64, b:u64, c:u64) {
            assert_bit_vector((a ^ b == a ^ c) >>= (b == c));
            assert((a ^ b == a ^ c) >>= (b == c));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test7 code! {
        #[proof]
        fn test8(b1:u64, b2:u64, b3:u64) {
            assert_bit_vector( !b1 != !b2 >>= !(b1==b2));
            assert_bit_vector(((b1 == (1 as u64)) && (b2 == b3)) >>= (b1 + b2 == b3 + 1));
            assert_bit_vector((b1 == b2)  >>= (!b1 == !b2));
            assert_bit_vector( b1 == (!(!b1)));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails code! {
        #[proof]
        fn test1(b: u32) {
            assert_bit_vector(b | b > b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2_fails code! {
        #[proof]
        fn test2(b: u32) {
            assert_bit_vector(b + 1 == b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3_fails code! {
        #[proof]
        fn test3(b: u32) {
            assert_bit_vector(b & 0 > 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test4_fails code! {
        #[proof]
        fn test4(b: u32) {
            assert_bit_vector( (b << 2) >> 2 == b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test5_fails code! {
        #[proof]
        fn test5(b: u32) {
            assert_bit_vector((b << 1) == b*2);
            assert((b << 1) == b*4); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test6_fails code! {
        #[proof]
        fn test6(b: u32) {
            assert_bit_vector(b<<2 == b*4);
            assert(((b<<2) as int) == (b as int) *4);  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// test_verify_one_file! {
//     #[test] test6_fails code! {
//         #[proof]
//         fn test6(b: i32) {
//             assert_bit_vector(b < b); // FAILS, signed int
//         }
//     } => Err(err) => assert_one_fails(err)
// }
