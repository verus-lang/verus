#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        proof fn test1(b: u32) {
            assert(b & 7 == b % 8) by(bit_vector);
            assert(b & 7 == b % 8);

            assert(b ^ b == 0u32) by(bit_vector);
            assert(b ^ b == 0);

            assert(b & b == b) by(bit_vector);
            assert(b & b == b);

            assert(add(add(b, !b), 1) == 0u32) by(bit_vector);
            assert(add(add(b, !b), 1) == 0);

            assert(b | b == b) by(bit_vector);
            assert(b | b == b);

            assert(b & 0xff < 0x100u32) by(bit_vector);
            assert(b & 0xff < 0x100);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        proof fn test2(b: u32) {
            assert(b << 2 == mul(b, 4)) by(bit_vector);
            assert(b << 2 == mul(b, 4));
            assert(b < 256 ==> ((b << 2) as int) == (b as int) * 4);

            assert(b >> 1 == b / 2) by(bit_vector);
            assert(b >> 1 == b / 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3 verus_code! {
        proof fn test3(b: u32) {
            assert(mul(2, b) - b == b) by(bit_vector);
            assert(mul(2, b) - b == b);

            assert(b <= b) by(bit_vector);
            assert(b >= b) by(bit_vector);

            assert(b & b & b == b | b | (b ^ b)) by(bit_vector);
            assert(b & b & b == b | b | (b ^ b));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test4 verus_code! {
        proof fn test4(u1: u32, u2:u32) {
            assert( (u1 as u64) << 32u64 | (u2 as u64)  == add(mul(u1 as u64, 0x100000000), u2 as u64))
                by(bit_vector);
            assert( (u1 as u64) << (32 as u64) | (u2 as u64)  == add(mul(u1 as u64, 0x100000000), u2 as u64));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test5 verus_code! {
        proof fn test5(u:u64) {
            assert( (u >> 32u64) as u32  ==  (u / 0x100000000u64) as u32)
                by(bit_vector);
            assert( (u >> (32 as u64)) as u32  ==  (u / (0x100000000 as u64)) as u32);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test6 verus_code! {
        proof fn test6(a:u64, b:u64, c:u64) {
            assert((a ^ b == a ^ c) ==> (b == c)) by(bit_vector);
            assert((a ^ b == a ^ c) ==> (b == c));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test7 verus_code! {
        proof fn test7(b1:u64, b2:u64, b3:u64) {
            assert( !b1 != !b2 ==> !(b1 == b2)) by(bit_vector);
            assert(((b1 == 1u64) && (b2 == b3)) ==> (add(b1, b2) == add(b3, 1))) by(bit_vector);
            assert((b1 == b2) ==> (!b1 == !b2)) by(bit_vector);
            assert( b1 == (!(!b1))) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test8 verus_code! {
        proof fn test8(b: u32) {
            assert_bit_vector(forall|a: u32, b: u32| #[trigger] (a & b) == b & a);
            assert_bit_vector(b & 0xff < 0x100u32);
            assert(0xff & b < 0x100);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test9 verus_code! {
        proof fn test9(x: u32, y:u32) {
            let max:u32 = 0xffff_ffff;
            assert(x >> 1 >= 0);
            assert(x & y <= max);
            assert(x | y >= 0);
            assert(x << y <= max);
            assert((!x) <= max);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails verus_code! {
        proof fn test1(b: u32) {
            assert(b | b > b) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2_fails verus_code! {
        proof fn test2(b: u32) {
            assert(add(b, 1) == b) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3_fails verus_code! {
        proof fn test3(b: u32) {
            assert(b & 0 > 0u32) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test4_fails verus_code! {
        proof fn test4(b: u32) {
            assert( (b << 2) >> 2 == b) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test5_fails verus_code! {
        proof fn test5(b: u32) {
            assert((b << 1) == mul(b, 2)) by(bit_vector);
            assert((b << 1) == mul(b, 4)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test6_fails verus_code! {
        proof fn test6(b: u32) {
            assert(b << 2 == mul(b, 4)) by(bit_vector);
            assert(((b << 2) as int) == (b as int) * 4);  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test7_fails verus_code! {
        proof fn test7(b: u32) {
            assert(!0u32 == 0xffffffffu32) by(bit_vector);
            assert(!0u64 == 0xffffffff_ffffffffu64) by(bit_vector);
            assert(false); // FAILS
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
