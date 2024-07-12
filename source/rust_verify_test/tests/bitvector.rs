#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        proof fn test1(b: u32) {
            assert(b & 7 == b % 8) by(bit_vector);
            assert(b & 7 == b % 8);

            assert(b ^ b == 0) by(bit_vector);
            assert(b ^ b == 0);

            assert(b & b == b) by(bit_vector);
            assert(b & b == b);

            assert(add(add(b, !b), 1) == 0) by(bit_vector);
            assert(add(add(b, !b), 1) == 0);

            assert(b | b == b) by(bit_vector);
            assert(b | b == b);

            assert(b & 0xff < 0x100) by(bit_vector);
            assert(b & 0xff < 0x100);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        proof fn test2(b: u32) {
            assert(b << 2 == mul(b, 4)) by(bit_vector);
            assert(b << 2 == mul(b, 4));
            assert(b < 256 ==> b << 2 == b * 4);

            assert(b >> 1 == b / 2) by(bit_vector);
            assert(b >> 1 == b / 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3 verus_code! {
        proof fn test3(b: u32) {
            assert(sub(mul(2, b), b) == b) by(bit_vector);
            assert(sub(mul(2, b), b) == b);

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
            assert( (u >> 32) as u32  ==  (u / 0x100000000) as u32)
                by(bit_vector);
            assert( (u >> 32) as u32  ==  (u / 0x100000000) as u32);
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
            assert(forall|a: u32, b: u32| #[trigger] (a & b) == b & a) by(bit_vector);
            assert(b & 0xff < 0x100) by(bit_vector);
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
            assert(b & 0 > 0) by(bit_vector); // FAILS
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
            assert(b << 2 == b * 4);  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test6_fails2 verus_code! {
        proof fn test6(b: u32) {
            assert(b << 2 == b * 4) by(bit_vector); // FAILS
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

test_verify_one_file! {
    #[test] test8_ok verus_code! {
        proof fn test8(b: i32) {
            assert(b <= b) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    //https://github.com/verus-lang/verus/issues/191 (@matthias-brun)
    #[test] test10_fails verus_code! {
        #[verifier(bit_vector)]
        proof fn f2() { // FAILS
            ensures(forall |i: u64| (1u64 << i) > 0); // Although this line should be reported instead of the above line, since Z3 does not return model which we utilize for error reporting, just use the above line
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] usize_in_by_bit_vector verus_code! {
        proof fn test_usize(x: usize) {
            assert(x & x == x) by (bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] const_usize_in_by_bit_vector verus_code! {
        proof fn test_usize() {
            assert(1usize == 1usize) by (bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] not_supported_int_in_by_bit_vector verus_code! {
        proof fn test_int(x: int) {
            assert(x == x) by (bit_vector);
        }
    } => Err(err) => assert_vir_error_msg(err, "expected finite-width integer")
}

test_verify_one_file! {
    #[test] not_supported_datatype_in_by_bit_vector verus_code! {
        struct X { }
        proof fn test_int(x: X) {
            assert(x == x) by (bit_vector);
        }
    } => Err(err) => assert_vir_error_msg(err, "bit_vector prover cannot handle this type")
}

test_verify_one_file! {
    #[test] const_int_in_by_bit_vector verus_code! {
        proof fn test_int() {
            assert(0int == 0int) by (bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] usize_cast_in_by_bit_vector verus_code! {
        proof fn test_usize(x: u64) {
            assert((x as usize) == (x as usize)) by (bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] bit_vector_with_usize_valid_expr verus_code! {
        spec fn stuff(x: usize, y: usize, z: usize) -> usize {
            (x | y) & !z
        }

        proof fn test_usize(x: usize, y: usize, z: usize) {
            // We can only prove trivial things without by(bit_vector)
            // but these should at least be well-formed expressions.
            assert(((x & y) | !z) == ((x & y) | !z));
        }

        proof fn test_usize2(x: usize, y: usize, z: usize) {
            // This should fail (it is wrong)
            assert(stuff(x, y, z) == stuff(y, z, x)); // FAILS
        }

        proof fn test_usize3(x: usize) {
            // This should fail (if usize is 32-bit, then these expressions are different)
            assert((!x) as u64 == (!(x as u64))); // FAILS
        }

        proof fn test_usize4(x: usize) {
            // This should fail (if usize is 64-bit, this is wrong)
            assert((x >> 32) == 0usize); // FAILS
        }

        proof fn test_usize5(x: usize) {
            // This should fail (if usize is 32-bit, this is wrong)
            assert(((1usize << 35) >> 34) == 2usize); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] bit_vector_usize_as_32bit ["vstd"] => verus_code! {
        global size_of usize == 4;

        proof fn test1(x: usize) {
            assert(x & x == x) by(bit_vector);
        }

        proof fn test2(y: usize) {
            // This should only work for 32-bit usize
            assert((y >> 32) == 0usize) by(bit_vector);
        }

        proof fn test3(x: usize) {
            assert((!x) as u64 == (!(x as u64))); // FAILS
        }

        proof fn test4(x: usize) {
            assert((!x) as u64 == (!(x as u64))) by(bit_vector); // FAILS
        }

        proof fn test5(x: usize) {
            assert((x >> 32) == 0usize) by(bit_vector);
        }

        proof fn test6(x: usize) {
            assert(((1usize << 35) >> 34) == 2usize); // FAILS
        }

        proof fn test7(x: usize) {
            assert(((1usize << 35) >> 34) == 2usize) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] bit_vector_usize_as_64bit ["vstd"] => verus_code! {
        global size_of usize == 8;

        proof fn test1(x: usize) {
            assert(x & x == x) by(bit_vector);
        }

        proof fn test2(y: usize) {
            assert((y >> 32) == 0usize); // FAILS
        }

        proof fn test3(y: usize) {
            assert((y >> 32) == 0usize) by(bit_vector); // FAILS
        }

        proof fn test4(x: usize) {
            assert((!x) as u64 == (!(x as u64))) by(bit_vector);
        }

        proof fn test5(x: usize) {
            assert((x >> 32) == 0usize); // FAILS
        }

        proof fn test6(x: usize) {
            assert((x >> 32) == 0usize) by(bit_vector); // FAILS
        }

        proof fn test7(x: usize) {
            assert(((1usize << 35) >> 34) == 2usize) by(bit_vector);
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] test_casting_to_higher_width_issue386 verus_code! {
        proof fn test() {
            let b: u8 = 20;
            let w: u64 = 20;

            // In order to augment b to a u64, it has to add 64 - 8 = 56 bits.
            // 56 isn't a power of 2
            // Thus, this test makes sure that bitwidths of non-powers-of-2 work.

            assert((b as u64) == w) by (bit_vector)
                requires b == 20 && w == 20 { }
        }

        proof fn test2() {
            let b: u8 = 20;
            let w: u64 = 276;

            assert((b as u64) == w) by (bit_vector) // FAILS
                requires b == 20 && w == 276 { }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_bool_variable_issue369 verus_code! {
        proof fn test() {
            let b: bool = true;
            assert(b ==> (0 | 1u8 == 1) == b) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_issue415 verus_code! {
        #[verifier(bit_vector)]
        proof fn lemma_shift_right_u64_upper_bound(val: u64, amt: u64, upper_bound: u64)
        requires
            amt < 64u64,
            val <= upper_bound,
        ensures
            (val >> amt) <= (upper_bound >> amt)
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] bitvector_in_decreases_by verus_code! {
        spec fn stuff(n: u64) -> int
            decreases n
              via stuff_dec
        {
            if n == 0 {
                0
            } else {
                stuff(n >> 1) + 1
            }
        }

        #[verifier::decreases_by]
        proof fn stuff_dec(n: u64) {
            assert((n > 0) ==> (n >> 1) < n) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] bitvector_ineq_different_bitwidth verus_code! {
        proof fn test() {
            let b: u8 = 5;

            assert(b >= 3u64) by(bit_vector)
                requires b == 5;
        }

        proof fn test2() {
            let b: u8 = 5;

            assert(3u64 <= b) by(bit_vector)
                requires b == 5;
        }

        proof fn test3() {
            let b: u8 = 5;

            assert(b <= 3u64) by(bit_vector) // FAILS
                requires b == 5;
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_extreme_cases_arithmetic1 verus_code! {
        fn test_arith_4_4() {
            assert(((-1i32) ^ (7i32)) + ((-1i32) ^ (7i32)) == -16) by(bit_vector);
            assert(((-1i32) ^ (7i32)) - ((-1i32) ^ (7i32)) == 0) by(bit_vector);
            assert(((-1i32) ^ (7i32)) * ((-1i32) ^ (7i32)) == 64) by(bit_vector);
            assert(((-1i32) ^ (7i32)) + !(-8i32) == -1) by(bit_vector);
            assert(((-1i32) ^ (7i32)) - !(-8i32) == -15) by(bit_vector);
            assert(((-1i32) ^ (7i32)) * !(-8i32) == -56) by(bit_vector);
            assert(!(-8i32) + ((-1i32) ^ (7i32)) == -1) by(bit_vector);
            assert(!(-8i32) - ((-1i32) ^ (7i32)) == 15) by(bit_vector);
            assert(!(-8i32) * ((-1i32) ^ (7i32)) == -56) by(bit_vector);
            assert(!(-8i32) + !(-8i32) == 14) by(bit_vector);
            assert(!(-8i32) - !(-8i32) == 0) by(bit_vector);
            assert(!(-8i32) * !(-8i32) == 49) by(bit_vector);
            assert(((-1i32) ^ (7i32)) + 15 == 7) by(bit_vector);
            assert(((-1i32) ^ (7i32)) - 15 == -23) by(bit_vector);
            assert(((-1i32) ^ (7i32)) * 15 == -120) by(bit_vector);
            assert(!(-8i32) + 15 == 22) by(bit_vector);
            assert(!(-8i32) - 15 == -8) by(bit_vector);
            assert(!(-8i32) * 15 == 105) by(bit_vector);
            assert(15 + ((-1i32) ^ (7i32)) == 7) by(bit_vector);
            assert(15 - ((-1i32) ^ (7i32)) == 23) by(bit_vector);
            assert(15 * ((-1i32) ^ (7i32)) == -120) by(bit_vector);
            assert(15 + !(-8i32) == 22) by(bit_vector);
            assert(15 - !(-8i32) == 8) by(bit_vector);
            assert(15 * !(-8i32) == 105) by(bit_vector);
            assert(0 + 0 == 0) by(bit_vector);
            assert(0 - 0 == 0) by(bit_vector);
            assert(0 * 0 == 0) by(bit_vector);
            assert(15 + 15 == 30) by(bit_vector);
            assert(15 - 15 == 0) by(bit_vector);
            assert(15 * 15 == 225) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_extreme_cases_arithmetic2 verus_code! {
        fn test_arith_8_8() {
            assert(((-1i32) ^ (127i32)) + ((-1i32) ^ (127i32)) == -256) by(bit_vector);
            assert(((-1i32) ^ (127i32)) - ((-1i32) ^ (127i32)) == 0) by(bit_vector);
            assert(((-1i32) ^ (127i32)) * ((-1i32) ^ (127i32)) == 16384) by(bit_vector);
            assert(((-1i32) ^ (127i32)) + !(-128i32) == -1) by(bit_vector);
            assert(((-1i32) ^ (127i32)) - !(-128i32) == -255) by(bit_vector);
            assert(((-1i32) ^ (127i32)) * !(-128i32) == -16256) by(bit_vector);
            assert(!(-128i32) + ((-1i32) ^ (127i32)) == -1) by(bit_vector);
            assert(!(-128i32) - ((-1i32) ^ (127i32)) == 255) by(bit_vector);
            assert(!(-128i32) * ((-1i32) ^ (127i32)) == -16256) by(bit_vector);
            assert(!(-128i32) + !(-128i32) == 254) by(bit_vector);
            assert(!(-128i32) - !(-128i32) == 0) by(bit_vector);
            assert(!(-128i32) * !(-128i32) == 16129) by(bit_vector);
            assert(((-1i32) ^ (127i32)) + 255 == 127) by(bit_vector);
            assert(((-1i32) ^ (127i32)) - 255 == -383) by(bit_vector);
            assert(((-1i32) ^ (127i32)) * 255 == -32640) by(bit_vector);
            assert(!(-128i32) + 255 == 382) by(bit_vector);
            assert(!(-128i32) - 255 == -128) by(bit_vector);
            assert(!(-128i32) * 255 == 32385) by(bit_vector);
            assert(255 + ((-1i32) ^ (127i32)) == 127) by(bit_vector);
            assert(255 - ((-1i32) ^ (127i32)) == 383) by(bit_vector);
            assert(255 * ((-1i32) ^ (127i32)) == -32640) by(bit_vector);
            assert(255 + !(-128i32) == 382) by(bit_vector);
            assert(255 - !(-128i32) == 128) by(bit_vector);
            assert(255 * !(-128i32) == 32385) by(bit_vector);
            assert(255 + 255 == 510) by(bit_vector);
            assert(255 - 255 == 0) by(bit_vector);
            assert(255 * 255 == 65025) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_extreme_cases_arithmetic3 verus_code! {
        fn test_arith_8_16() {
            assert(((-1i32) ^ (127i32)) + ((-1i32) ^ (32767i32)) == -32896) by(bit_vector);
            assert(((-1i32) ^ (127i32)) - ((-1i32) ^ (32767i32)) == 32640) by(bit_vector);
            assert(((-1i32) ^ (127i32)) * ((-1i32) ^ (32767i32)) == 4194304) by(bit_vector);
            assert(((-1i32) ^ (127i32)) + !(-32768i32) == 32639) by(bit_vector);
            assert(((-1i32) ^ (127i32)) - !(-32768i32) == -32895) by(bit_vector);
            assert(((-1i32) ^ (127i32)) * !(-32768i32) == -4194176) by(bit_vector);
            assert(!(-128i32) + ((-1i32) ^ (32767i32)) == -32641) by(bit_vector);
            assert(!(-128i32) - ((-1i32) ^ (32767i32)) == 32895) by(bit_vector);
            assert(!(-128i32) * ((-1i32) ^ (32767i32)) == -4161536) by(bit_vector);
            assert(!(-128i32) + !(-32768i32) == 32894) by(bit_vector);
            assert(!(-128i32) - !(-32768i32) == -32640) by(bit_vector);
            assert(!(-128i32) * !(-32768i32) == 4161409) by(bit_vector);
            assert(((-1i32) ^ (127i32)) + 65535 == 65407) by(bit_vector);
            assert(((-1i32) ^ (127i32)) - 65535 == -65663) by(bit_vector);
            assert(((-1i32) ^ (127i32)) * 65535 == -8388480) by(bit_vector);
            assert(!(-128i32) + 65535 == 65662) by(bit_vector);
            assert(!(-128i32) - 65535 == -65408) by(bit_vector);
            assert(!(-128i32) * 65535 == 8322945) by(bit_vector);
            assert(255 + ((-1i32) ^ (32767i32)) == -32513) by(bit_vector);
            assert(255 - ((-1i32) ^ (32767i32)) == 33023) by(bit_vector);
            assert(255 * ((-1i32) ^ (32767i32)) == -8355840) by(bit_vector);
            assert(255 + !(-32768i32) == 33022) by(bit_vector);
            assert(255 - !(-32768i32) == -32512) by(bit_vector);
            assert(255 * !(-32768i32) == 8355585) by(bit_vector);
            assert(255 + 65535 == 65790) by(bit_vector);
            assert(255 - 65535 == -65280) by(bit_vector);
            assert(255 * 65535 == 16711425) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_extreme_cases_arithmetic4 verus_code! {
        fn test_arith_16_8() {
            assert(((-1i32) ^ (32767i32)) + ((-1i32) ^ (127i32)) == -32896) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) - ((-1i32) ^ (127i32)) == -32640) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) * ((-1i32) ^ (127i32)) == 4194304) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) + !(-128i32) == -32641) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) - !(-128i32) == -32895) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) * !(-128i32) == -4161536) by(bit_vector);
            assert(!(-32768i32) + ((-1i32) ^ (127i32)) == 32639) by(bit_vector);
            assert(!(-32768i32) - ((-1i32) ^ (127i32)) == 32895) by(bit_vector);
            assert(!(-32768i32) * ((-1i32) ^ (127i32)) == -4194176) by(bit_vector);
            assert(!(-32768i32) + !(-128i32) == 32894) by(bit_vector);
            assert(!(-32768i32) - !(-128i32) == 32640) by(bit_vector);
            assert(!(-32768i32) * !(-128i32) == 4161409) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) + 255 == -32513) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) - 255 == -33023) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) * 255 == -8355840) by(bit_vector);
            assert(!(-32768i32) + 255 == 33022) by(bit_vector);
            assert(!(-32768i32) - 255 == 32512) by(bit_vector);
            assert(!(-32768i32) * 255 == 8355585) by(bit_vector);
            assert(65535 + ((-1i32) ^ (127i32)) == 65407) by(bit_vector);
            assert(65535 - ((-1i32) ^ (127i32)) == 65663) by(bit_vector);
            assert(65535 * ((-1i32) ^ (127i32)) == -8388480) by(bit_vector);
            assert(65535 + !(-128i32) == 65662) by(bit_vector);
            assert(65535 - !(-128i32) == 65408) by(bit_vector);
            assert(65535 * !(-128i32) == 8322945) by(bit_vector);
            assert(65535 + 255 == 65790) by(bit_vector);
            assert(65535 - 255 == 65280) by(bit_vector);
            assert(65535 * 255 == 16711425) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_extreme_cases_arithmetic5 verus_code! {
        fn test_arith_15_16() {
            assert(((-1i32) ^ (16383i32)) + ((-1i32) ^ (32767i32)) == -49152) by(bit_vector);
            assert(((-1i32) ^ (16383i32)) - ((-1i32) ^ (32767i32)) == 16384) by(bit_vector);
            assert(((-1i32) ^ (16383i32)) * ((-1i32) ^ (32767i32)) == 536870912) by(bit_vector);
            assert(((-1i32) ^ (16383i32)) + !(-32768i32) == 16383) by(bit_vector);
            assert(((-1i32) ^ (16383i32)) - !(-32768i32) == -49151) by(bit_vector);
            assert(((-1i32) ^ (16383i32)) * !(-32768i32) == -536854528) by(bit_vector);
            assert(!(-16384i32) + ((-1i32) ^ (32767i32)) == -16385) by(bit_vector);
            assert(!(-16384i32) - ((-1i32) ^ (32767i32)) == 49151) by(bit_vector);
            assert(!(-16384i32) * ((-1i32) ^ (32767i32)) == -536838144) by(bit_vector);
            assert(!(-16384i32) + !(-32768i32) == 49150) by(bit_vector);
            assert(!(-16384i32) - !(-32768i32) == -16384) by(bit_vector);
            assert(!(-16384i32) * !(-32768i32) == 536821761) by(bit_vector);
            assert(((-1i32) ^ (16383i32)) + 65535 == 49151) by(bit_vector);
            assert(((-1i32) ^ (16383i32)) - 65535 == -81919) by(bit_vector);
            assert(((-1i32) ^ (16383i32)) * 65535 == -1073725440) by(bit_vector);
            assert(!(-16384i32) + 65535 == 81918) by(bit_vector);
            assert(!(-16384i32) - 65535 == -49152) by(bit_vector);
            assert(!(-16384i32) * 65535 == 1073659905) by(bit_vector);
            assert(32767 + ((-1i32) ^ (32767i32)) == -1) by(bit_vector);
            assert(32767 - ((-1i32) ^ (32767i32)) == 65535) by(bit_vector);
            assert(32767 * ((-1i32) ^ (32767i32)) == -1073709056) by(bit_vector);
            assert(32767 + !(-32768i32) == 65534) by(bit_vector);
            assert(32767 - !(-32768i32) == 0) by(bit_vector);
            assert(32767 * !(-32768i32) == 1073676289) by(bit_vector);
            assert(0 + 65535 == 65535) by(bit_vector);
            assert(0 - 65535 == -65535) by(bit_vector);
            assert(0 * 65535 == 0) by(bit_vector);
            assert(32767 + 65535 == 98302) by(bit_vector);
            assert(32767 - 65535 == -32768) by(bit_vector);
            assert(32767 * 65535 == 2147385345) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_extreme_cases_arithmetic6 verus_code! {
        fn test_arith_16_15() {
            assert(((-1i32) ^ (32767i32)) + ((-1i32) ^ (16383i32)) == -49152) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) - ((-1i32) ^ (16383i32)) == -16384) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) * ((-1i32) ^ (16383i32)) == 536870912) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) + !(-16384i32) == -16385) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) - !(-16384i32) == -49151) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) * !(-16384i32) == -536838144) by(bit_vector);
            assert(!(-32768i32) + ((-1i32) ^ (16383i32)) == 16383) by(bit_vector);
            assert(!(-32768i32) - ((-1i32) ^ (16383i32)) == 49151) by(bit_vector);
            assert(!(-32768i32) * ((-1i32) ^ (16383i32)) == -536854528) by(bit_vector);
            assert(!(-32768i32) + !(-16384i32) == 49150) by(bit_vector);
            assert(!(-32768i32) - !(-16384i32) == 16384) by(bit_vector);
            assert(!(-32768i32) * !(-16384i32) == 536821761) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) + 0 == -32768) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) - 0 == -32768) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) * 0 == 0) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) + 32767 == -1) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) - 32767 == -65535) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) * 32767 == -1073709056) by(bit_vector);
            assert(!(-32768i32) + 32767 == 65534) by(bit_vector);
            assert(!(-32768i32) - 32767 == 0) by(bit_vector);
            assert(!(-32768i32) * 32767 == 1073676289) by(bit_vector);
            assert(65535 + ((-1i32) ^ (16383i32)) == 49151) by(bit_vector);
            assert(65535 - ((-1i32) ^ (16383i32)) == 81919) by(bit_vector);
            assert(65535 * ((-1i32) ^ (16383i32)) == -1073725440) by(bit_vector);
            assert(65535 + !(-16384i32) == 81918) by(bit_vector);
            assert(65535 - !(-16384i32) == 49152) by(bit_vector);
            assert(65535 * !(-16384i32) == 1073659905) by(bit_vector);
            assert(65535 + 32767 == 98302) by(bit_vector);
            assert(65535 - 32767 == 32768) by(bit_vector);
            assert(65535 * 32767 == 2147385345) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_double_arch_ok verus_code! {
        proof fn test_works_both(a: usize, b: usize, c: u32) {
            assert(
                (usize::BITS == 64 ==> (((c as usize) << 32) >> 32 == c))
                && (usize::BITS == 32 ==> (a as u32) == (b as u32) ==> a == b)) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_double_arch_fail32 verus_code! {
        proof fn test(c: u32) {
            assert(((c as usize) << 32) >> 32 == c) by(bit_vector);
        }
    } => Err(err) => assert_fails_bv_32bit(err)
}

test_verify_one_file! {
    #[test] test_double_arch_fail64 verus_code! {
        proof fn test(a: usize, b: usize) {
            assert((a as u32) == (b as u32) ==> a == b) by(bit_vector);
        }
    } => Err(err) => assert_fails_bv_64bit(err)
}

test_verify_one_file! {
    #[test] test_double_arch_fail_both verus_code! {
        proof fn test_works_neither(a: usize, b: usize) {
            assert((a as u32) == (b as u32)) by(bit_vector);
        }
    } => Err(err) => assert_fails_bv_32bit_64bit(err)
}

test_verify_one_file! {
    #[test] test_double_arch_fail64_req_ens verus_code! {
        proof fn test_only_32_2(a: usize) by(bit_vector)
            requires (a as u32) != a
            ensures false
        { }
    } => Err(err) => assert_fails_bv_64bit(err)
}

test_verify_one_file! {
    #[test] test_shl_signed_unsupported verus_code! {
        fn test_shl_neg(x: i32, y: i32) {
            assert(x << y == x) by(bit_vector);
        }
    } => Err(err) => assert_vir_error_msg(err, "not supported: bit-shift with possibly negative shift")
}

test_verify_one_file! {
    #[test] test_shr_signed_unsupported verus_code! {
        fn test_shl_neg(x: i32, y: i32) {
            assert(x >> y == x) by(bit_vector);
        }
    } => Err(err) => assert_vir_error_msg(err, "not supported: bit-shift with possibly negative shift")
}

test_verify_one_file! {
    #[test] test_eq_ineq verus_code! {
        fn test_eq(x: u8, y: i8) {
            assert(x == y as u8 ==> y == x) by(bit_vector); // FAILS
        }

        fn test_ineq(x: u8, y: i8, z: u8) {
            assert(y == -5 ==> x >= y) by(bit_vector);
            assert(x >= (y as u8) ==> x >= y) by(bit_vector);
            assert(x >= (x as i8)) by(bit_vector);

            assert(x >= (z as i8) ==> x >= z) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_eq_ineq2 verus_code! {
        fn test_comparisons(a: u32, b: i32) {
            assert(a < b <==> (b & (-0x8000_0000i32) == 0) && (a < (b as u32))) by(bit_vector);
            assert(a < b ==> a < (b as u32)) by(bit_vector);
            assert(a < b <== a < (b as u32)) by(bit_vector); // FAILS
            assert(a < b <==> (a as i64) < b) by(bit_vector);

            assert(a > b <==> (b & (-0x8000_0000i32) != 0) || (a > (b as u32))) by(bit_vector);
            assert(a > b ==> a > (b as u32)) by(bit_vector); // FAILS
            assert(a > b <== a > (b as u32)) by(bit_vector);
            assert(a > b <==> (a as i64) > b) by(bit_vector);
        }

        fn test_comparisons_2(a: u32, b: i64) {
            assert(a < b <==> (b & (-0x8000_0000_0000_0000i64) == 0) && ((a as u64) < (b as u64))) by(bit_vector);
            assert(a < b ==> a < (b as u64)) by(bit_vector);
            assert(a < b <== a < (b as u64)) by(bit_vector); // FAILS
            assert(a < b <==> (a as i128) < b) by(bit_vector);

            assert(a > b <==> (b & (-0x8000_0000_0000_0000i64) != 0) || ((a as u64) > (b as u64))) by(bit_vector);
            assert(a > b ==> a > (b as u64)) by(bit_vector); // FAILS
            assert(a > b <== a > (b as u64)) by(bit_vector);
            assert(a > b <==> (a as i128) > b) by(bit_vector);
        }

        fn test_comparisons_3(a: u32, b: i16) {
            assert(a < b <==> (b & (-0x8000i16) == 0) && (a < (b as u16))) by(bit_vector);
            assert(a < b ==> a < (b as u16)) by(bit_vector);
            assert(a < b <== a < (b as u16)) by(bit_vector); // FAILS
            assert(a < b <==> (a as i64) < (b as i64)) by(bit_vector);

            assert(a > b <==> (b & (-0x8000i16) != 0) || (a > (b as u16))) by(bit_vector);
            assert(a > b ==> a > (b as u16)) by(bit_vector); // FAILS
            assert(a > b <== a > (b as u16)) by(bit_vector);
            assert(a > b <==> (a as i64) > b) by(bit_vector);
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file! {
    #[test] test_clipping_and_casting verus_code! {
        fn test_clipping(a: u32, b: i32) {
            assert(a as u64 == a) by(bit_vector);
            assert(a as u16 == a) by(bit_vector); // FAILS
            assert(a as u16 == (a as i32) as u16) by(bit_vector);

            assert(b as i64 == b) by(bit_vector);
            assert(b as u64 == b) by(bit_vector); // FAILS
            assert(b as i16 == b) by(bit_vector); // FAILS
            assert(b as i16 == (b as u64) as i16) by(bit_vector);
        }


        fn test_casting(x: u16, y: i16) {
            assert(x as u32 == x) by(bit_vector);
            assert(y as i32 == y) by(bit_vector);
            assert(x as i64 == x) by(bit_vector);

            assert(x as i8 as u8 == x as u8) by(bit_vector);
            assert(y as u8 as i8 == y as i8) by(bit_vector);

            assert(y as u64 == y) by(bit_vector); // FAILS
            assert(x as u8 == x) by(bit_vector); // FAILS
            assert(y as i8 == y) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file! {
    #[test] test_or verus_code! {
        fn test_or(x: u16, y: u16, z: i16) {
            assert((x | y) == (x as i16 | y as i16) as u16) by(bit_vector);
            assert((x | y) == (x as i16 | y as i16)) by(bit_vector); // FAILS
            assert((x | 0x7777) & 0x8000 == x & 0x8000) by(bit_vector);
            assert((z | 0x7777) & (0x8000u16 as i16) == z & (0x8000u16 as i16)) by(bit_vector);

            assert((x as i32 | z as i32) == (x | z as u16)) by(bit_vector); // FAILS
            assert((x as i32 | z as i32) == (x as i16 | z)) by(bit_vector); // FAILS
            assert((x as i32 | z as i32) ==
                ((x | z as u16) as u32 | (if z < 0 { 0xffff0000u32 } else { 0 })) as i32) by(bit_vector);
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_and verus_code! {
        fn test_and(x: u16, y: u16, z: i16) {
            assert((x & y) == (x as i16 & y as i16) as u16) by(bit_vector);
            assert((x & y) == (x as i16 & y as i16)) by(bit_vector); // FAILS
            assert((x & 0x7777) & 0x8000 == 0) by(bit_vector);
            assert((z & 0x7777) & (0x8000u16 as i16) == 0) by(bit_vector);

            assert((x as i32 & z as i32) == (x & z as u16)) by(bit_vector);
            assert((x as i32 & z as i32) == (x as i16 & z)) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_xor verus_code! {
        fn test_xor(x: u16, y: u16, z: i16) {
            assert((x ^ y) == (x as i16 ^ y as i16) as u16) by(bit_vector);
            assert((x ^ y) == (x as i16 ^ y as i16)) by(bit_vector); // FAILS
            assert((x ^ 0x7777) & 0x8000 == x & 0x8000) by(bit_vector);
            assert((z ^ 0x7777) & (0x8000u16 as i16) == z & (0x8000u16 as i16)) by(bit_vector);

            assert((x as i32 ^ z as i32) == (x ^ z as u16)) by(bit_vector); // FAILS
            assert((x as i32 ^ z as i32) == (x as i16 ^ z)) by(bit_vector); // FAILS
            assert((x as i32 ^ z as i32) ==
                ((x ^ z as u16) as u32 | (if z < 0 { 0xffff0000u32 } else { 0 })) as i32) by(bit_vector);
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_shl verus_code! {
        fn test_shl(x: u32, y: u16) {
            assert(x == y ==> (x << 2) == (y << 2)) by(bit_vector); // FAILS
            assert((x << 32) == (y << 32)) by(bit_vector);

            assert((x << 2) as i32 == (x as i32) << 2) by(bit_vector);
            assert((x << 2) == (x as i32) << 2) by(bit_vector); // FAILS

            assert((x << 2) == x * 4) by(bit_vector); // FAILS
            assert(((x as u64) << 2) == x * 4) by(bit_vector);

            assert((y << 2) == y * 4) by(bit_vector); // FAILS
            assert(((y as u64) << 2) == y * 4) by(bit_vector);

            assert((y << 2) == ((y as u32) << 2) as u16) by(bit_vector);
            assert((y << 2) == ((y as i32) << 2) as u16) by(bit_vector);
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] test_shl_signed verus_code! {
        fn test_shl_signed(x: i32, y: i16, z: i32) {
            assert(x & (0xff000000u32 as i32) == 0 ==> (x << 2) == x * 4) by(bit_vector);
            assert((x << 2) == (x * 4) as i32) by(bit_vector);

            assert(x == y ==> (x << 2) == (y << 2)) by(bit_vector); // FAILS
            assert((x << 32) == (y << 32)) by(bit_vector);

            assert((x << 2) as u32 == (x as u32) << 2) by(bit_vector);

            assert((x << 2) == (y << 2)) by(bit_vector); // FAILS
            assert((x << 2) == (x as u32) << 2) by(bit_vector); // FAILS
            assert((x << 2) == x * 4) by(bit_vector); // FAILS
            assert(((x as i64) << 2) == x * 4) by(bit_vector);

            assert((y << 2) == ((y as u32) << 2) as i16) by(bit_vector);
            assert((y << 2) == ((y as i32) << 2) as i16) by(bit_vector);
        }

        fn test_shl_shift_is_signed_but_still_nonnegative(x: i32, z: i32) {
            assert(z == 2 ==> x << (z as u32) == (x * 4) as i32) by(bit_vector);
            assert(z == 2 ==> x << z == (x * 4) as i32); // normal solver, not bit-vector
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] test_shr verus_code! {
        fn test_shr(x: u32, y: u16) {
            assert(x == y ==> (x >> 2) == (y >> 2)) by(bit_vector);
            assert(x >> 32 == y >> 16) by(bit_vector);
            assert(x >> 16 == y >> 16) by(bit_vector); // FAILS

            assert((x >> 2) as i32 == (x as i32) >> 2) by(bit_vector); // FAILS
            assert((x >> 2) == (x as i32) >> 2) by(bit_vector); // FAILS

            assert((x >> 2) == x / 4) by(bit_vector);

            assert((y >> 2) == (y as u32) >> 2) by(bit_vector);
            assert((y >> 2) == (y as i32) >> 2) by(bit_vector);
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_shr_signed verus_code! {
        fn test_shr_signed(x: i32, y: i16, z: i32) {
            assert(x & 0x3 == 0 ==> (x >> 2) * 4 == x) by(bit_vector);
            assert(x >> 2 == (if x > 0 { ((x as u64) / 4) as i64 } else { -(((-x) as u64 + 3) / 4) as i64 })) by(bit_vector);

            assert(x == y ==> (x >> 2) == (y >> 2)) by(bit_vector);
            assert(x >> 32 == y >> 16) by(bit_vector); // FAILS
            assert(y >> 16 == 0 || y >> 16 == -1) by(bit_vector);
            assert(x >> 16 == y >> 16) by(bit_vector); // FAILS

            assert((x >> 2) as u32 == (x as u32) >> 2) by(bit_vector); // FAILS
            assert((x >> 2) == (x as u32) >> 2) by(bit_vector); // FAILS

            assert((y >> 2) == (y as u32) >> 2) by(bit_vector); // FAILS
            assert((y >> 2) == (y as i32) >> 2) by(bit_vector);
        }

        fn test_shr_shift_is_signed_but_still_nonnegative(x: i32, z: i32) {
            assert(z == 2 ==> x & 0x3 == 0 ==> (x >> (z as u32)) * 4 == x) by(bit_vector);
            assert(z == 2 ==> x & 0x3 == 0 ==> (x >> z) * 4 == x);  // normal solver, not bit-vector
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file! {
    #[test] div0_underspecified verus_code! {
        fn div_0_underspecified(x: u32, y: u32) {
            assert(0u32 / y == 0) by(bit_vector); // FAILS
            assert(y != 0 ==> 0u32 / y == 0) by(bit_vector);

            assert(y / y == 1) by(bit_vector); // FAILS
            assert(y != 0 ==> y / y == 1) by(bit_vector);

            assert(x == 0 && y == 0 ==> x/y == 0xffffffff) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] mod0_underspecified verus_code! {
        fn mod_0_underspecified(x: u32, y: u32) {
            assert(0u32 % y == 0) by(bit_vector); // FAILS
            assert(y != 0 ==> 0u32 % y == 0) by(bit_vector);

            assert(y % y == 0) by(bit_vector); // FAILS
            assert(y != 0 ==> y % y == 0) by(bit_vector);

            assert(x == 0 && y == 0 ==> x%y == 0) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] mod0_div0_consistency verus_code! {
        fn mod_0_div_0_consistency(x: u32, y: u32) {
            assert(x % y == x % y) by(bit_vector); // FAILS
            assert(x / y == x / y) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] bitnot verus_code! {
        fn test_bitnot_unsigned(x: u32, y: u64) {
            assert(x == y ==> (!x) == (!y)) by(bit_vector); // FAILS
            assert(x == y ==> ((!x) as u64 ^ 0xffff_ffff_0000_0000) == (!y)) by(bit_vector);
            assert((!y) == 0xffff_ffff_ffff_ffff - y) by(bit_vector);
        }

        fn test_bitnot_signed(x: i32, y: i64) {
            assert(x == y ==> (!x) == (!y)) by(bit_vector);
            assert((!y) == (-1) - y) by(bit_vector);
            assert(!0xffffi32 == -0x10000) by(bit_vector);
        }

        fn test_bitnot_signed_unsigned(a: u32, b: i32) {
            assert(a == (b as u32) ==> !a == (!b) as u32) by(bit_vector);
            assert(a == (b as u32) ==> !a == (!b)) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

// test_by_equating:
// test `x op y` for all combinations of
//    - (x, y) are (8 bits, 8 bits); (8 bits, 9 bits); (9 bits, 8 bits)
//    - all combinations signed/unsigned
//    - for a bunch of different ops
// by comparing the results to the same operation done on a higher number of bits
// to get a '9 bit' thing, we add two 8 bits things together (e.g., ai + ai2)

test_verify_one_file! {
    #[test] test_by_equating_add verus_code! {
        fn test_add(au: u8, au2: u8, bu: u8, bu2: u8, ai: i8, ai2: i8, bi: i8, bi2: i8, x: i32, y: i32) {
            assert(ai == x && bi == y ==> (ai + bi) == (x + y)) by(bit_vector);
            assert(ai == x && bu == y ==> (ai + bu) == (x + y)) by(bit_vector);
            assert(au == x && bi == y ==> (au + bi) == (x + y)) by(bit_vector);
            assert(au == x && bu == y ==> (au + bu) == (x + y)) by(bit_vector);
            assert(ai == x && (bi + bi2) == y ==> (ai + (bi + bi2)) == (x + y)) by(bit_vector);
            assert(ai == x && (bu + bu2) == y ==> (ai + (bu + bu2)) == (x + y)) by(bit_vector);
            assert(au == x && (bi + bi2) == y ==> (au + (bi + bi2)) == (x + y)) by(bit_vector);
            assert(au == x && (bu + bu2) == y ==> (au + (bu + bu2)) == (x + y)) by(bit_vector);
            assert((ai + ai2) == x && bi == y ==> ((ai + ai2) + bi) == (x + y)) by(bit_vector);
            assert((ai + ai2) == x && bu == y ==> ((ai + ai2) + bu) == (x + y)) by(bit_vector);
            assert((au + au2) == x && bi == y ==> ((au + au2) + bi) == (x + y)) by(bit_vector);
            assert((au + au2) == x && bu == y ==> ((au + au2) + bu) == (x + y)) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_by_equating_sub verus_code! {
        fn test_sub(au: u8, au2: u8, bu: u8, bu2: u8, ai: i8, ai2: i8, bi: i8, bi2: i8, x: i32, y: i32) {
            assert(ai == x && bi == y ==> (ai - bi) == (x - y)) by(bit_vector);
            assert(ai == x && bu == y ==> (ai - bu) == (x - y)) by(bit_vector);
            assert(au == x && bi == y ==> (au - bi) == (x - y)) by(bit_vector);
            assert(au == x && bu == y ==> (au - bu) == (x - y)) by(bit_vector);
            assert(ai == x && (bi + bi2) == y ==> (ai - (bi + bi2)) == (x - y)) by(bit_vector);
            assert(ai == x && (bu + bu2) == y ==> (ai - (bu + bu2)) == (x - y)) by(bit_vector);
            assert(au == x && (bi + bi2) == y ==> (au - (bi + bi2)) == (x - y)) by(bit_vector);
            assert(au == x && (bu + bu2) == y ==> (au - (bu + bu2)) == (x - y)) by(bit_vector);
            assert((ai + ai2) == x && bi == y ==> ((ai + ai2) - bi) == (x - y)) by(bit_vector);
            assert((ai + ai2) == x && bu == y ==> ((ai + ai2) - bu) == (x - y)) by(bit_vector);
            assert((au + au2) == x && bi == y ==> ((au + au2) - bi) == (x - y)) by(bit_vector);
            assert((au + au2) == x && bu == y ==> ((au + au2) - bu) == (x - y)) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_by_equating_mul verus_code! {
        fn test_mul(au: u8, au2: u8, bu: u8, bu2: u8, ai: i8, ai2: i8, bi: i8, bi2: i8, x: i32, y: i32) {
            assert(ai == x && bi == y ==> (ai * bi) == (x * y)) by(bit_vector);
            assert(ai == x && bu == y ==> (ai * bu) == (x * y)) by(bit_vector);
            assert(au == x && bi == y ==> (au * bi) == (x * y)) by(bit_vector);
            assert(au == x && bu == y ==> (au * bu) == (x * y)) by(bit_vector);
            assert(ai == x && (bi + bi2) == y ==> (ai * (bi + bi2)) == (x * y)) by(bit_vector);
            assert(ai == x && (bu + bu2) == y ==> (ai * (bu + bu2)) == (x * y)) by(bit_vector);
            assert(au == x && (bi + bi2) == y ==> (au * (bi + bi2)) == (x * y)) by(bit_vector);
            assert(au == x && (bu + bu2) == y ==> (au * (bu + bu2)) == (x * y)) by(bit_vector);
            assert((ai + ai2) == x && bi == y ==> ((ai + ai2) * bi) == (x * y)) by(bit_vector);
            assert((ai + ai2) == x && bu == y ==> ((ai + ai2) * bu) == (x * y)) by(bit_vector);
            assert((au + au2) == x && bi == y ==> ((au + au2) * bi) == (x * y)) by(bit_vector);
            assert((au + au2) == x && bu == y ==> ((au + au2) * bu) == (x * y)) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_by_equating_le verus_code! {
        fn test_le(au: u8, au2: u8, bu: u8, bu2: u8, ai: i8, ai2: i8, bi: i8, bi2: i8, x: i32, y: i32) {
            assert(ai == x && bi == y ==> (ai <= bi) == (x <= y)) by(bit_vector);
            assert(ai == x && bu == y ==> (ai <= bu) == (x <= y)) by(bit_vector);
            assert(au == x && bi == y ==> (au <= bi) == (x <= y)) by(bit_vector);
            assert(au == x && bu == y ==> (au <= bu) == (x <= y)) by(bit_vector);
            assert(ai == x && (bi + bi2) == y ==> (ai <= (bi + bi2)) == (x <= y)) by(bit_vector);
            assert(ai == x && (bu + bu2) == y ==> (ai <= (bu + bu2)) == (x <= y)) by(bit_vector);
            assert(au == x && (bi + bi2) == y ==> (au <= (bi + bi2)) == (x <= y)) by(bit_vector);
            assert(au == x && (bu + bu2) == y ==> (au <= (bu + bu2)) == (x <= y)) by(bit_vector);
            assert((ai + ai2) == x && bi == y ==> ((ai + ai2) <= bi) == (x <= y)) by(bit_vector);
            assert((ai + ai2) == x && bu == y ==> ((ai + ai2) <= bu) == (x <= y)) by(bit_vector);
            assert((au + au2) == x && bi == y ==> ((au + au2) <= bi) == (x <= y)) by(bit_vector);
            assert((au + au2) == x && bu == y ==> ((au + au2) <= bu) == (x <= y)) by(bit_vector);
        }
    } => Ok(())
}

// TODO once signed division/mod are supported,
// we can remove these 2 tests and un-ignore the more complete ones below
test_verify_one_file! {
    #[test] test_by_equating_div_unsigned_only verus_code! {
        fn test_div(au: u8, au2: u8, bu: u8, bu2: u8, x: u32, y: u32) {
            assert(y != 0 ==> au == x && bu == y ==> (au as int) / (bu as int) == x / y) by(bit_vector);
            assert(y != 0 ==> au == x && (bu + bu2) == y ==> (au as int) / ((bu + bu2) as int) == x / y) by(bit_vector);
            assert(y != 0 ==> (au + au2) == x && bu == y ==> ((au + au2) as int) / (bu as int) == x / y) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_by_equating_mod_unsigned_only verus_code! {
        fn test_mod(au: u8, au2: u8, bu: u8, bu2: u8, x: u32, y: u32) {
            assert(y != 0 ==> au == x && bu == y ==> (au as int) % (bu as int) == x % y) by(bit_vector);
            assert(y != 0 ==> au == x && (bu + bu2) == y ==> (au as int) % ((bu + bu2) as int) == x % y) by(bit_vector);
            assert(y != 0 ==> (au + au2) == x && bu == y ==> ((au + au2) as int) % (bu as int) == x % y) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] test_by_equating_div verus_code! {
        fn test_div(au: u8, au2: u8, bu: u8, bu2: u8, x: u32, y: u32) {
            assert(y != 0 ==> ai == x && bi == y ==> (ai as int) / (bi as int) == x / y) by(bit_vector);
            assert(y != 0 ==> ai == x && bu == y ==> (ai as int) / (bu as int) == x / y) by(bit_vector);
            assert(y != 0 ==> au == x && bi == y ==> (au as int) / (bi as int) == x / y) by(bit_vector);
            assert(y != 0 ==> au == x && bu == y ==> (au as int) / (bu as int) == x / y) by(bit_vector);
            assert(y != 0 ==> ai == x && (bi + bi2) == y ==> (ai as int) / ((bi + bi2) as int) == x / y) by(bit_vector);
            assert(y != 0 ==> ai == x && (bu + bu2) == y ==> (ai as int) / ((bu + bu2) as int) == x / y) by(bit_vector);
            assert(y != 0 ==> au == x && (bi + bi2) == y ==> (au as int) / ((bi + bi2) as int) == x / y) by(bit_vector);
            assert(y != 0 ==> au == x && (bu + bu2) == y ==> (au as int) / ((bu + bu2) as int) == x / y) by(bit_vector);
            assert(y != 0 ==> (ai + ai2) == x && bi == y ==> ((ai + ai2) as int) / (bi as int) == x / y) by(bit_vector);
            assert(y != 0 ==> (ai + ai2) == x && bu == y ==> ((ai + ai2) as int) / (bu as int) == x / y) by(bit_vector);
            assert(y != 0 ==> (au + au2) == x && bi == y ==> ((au + au2) as int) / (bi as int) == x / y) by(bit_vector);
            assert(y != 0 ==> (au + au2) == x && bu == y ==> ((au + au2) as int) / (bu as int) == x / y) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] test_by_equating_mod verus_code! {
        fn test_mod(au: u8, au2: u8, bu: u8, bu2: u8, x: u32, y: u32) {
            assert(y != 0 ==> ai == x && bi == y ==> (ai as int) % (bi as int) == x % y) by(bit_vector);
            assert(y != 0 ==> ai == x && bu == y ==> (ai as int) % (bu as int) == x % y) by(bit_vector);
            assert(y != 0 ==> au == x && bi == y ==> (au as int) % (bi as int) == x % y) by(bit_vector);
            assert(y != 0 ==> au == x && bu == y ==> (au as int) % (bu as int) == x % y) by(bit_vector);
            assert(y != 0 ==> ai == x && (bi + bi2) == y ==> (ai as int) % ((bi + bi2) as int) == x % y) by(bit_vector);
            assert(y != 0 ==> ai == x && (bu + bu2) == y ==> (ai as int) % ((bu + bu2) as int) == x % y) by(bit_vector);
            assert(y != 0 ==> au == x && (bi + bi2) == y ==> (au as int) % ((bi + bi2) as int) == x % y) by(bit_vector);
            assert(y != 0 ==> au == x && (bu + bu2) == y ==> (au as int) % ((bu + bu2) as int) == x % y) by(bit_vector);
            assert(y != 0 ==> (ai + ai2) == x && bi == y ==> ((ai + ai2) as int) % (bi as int) == x % y) by(bit_vector);
            assert(y != 0 ==> (ai + ai2) == x && bu == y ==> ((ai + ai2) as int) % (bu as int) == x % y) by(bit_vector);
            assert(y != 0 ==> (au + au2) == x && bi == y ==> ((au + au2) as int) % (bi as int) == x % y) by(bit_vector);
            assert(y != 0 ==> (au + au2) == x && bu == y ==> ((au + au2) as int) % (bu as int) == x % y) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_by_equating_shr verus_code! {
        fn test_shr(au8: u8, au16: u16, bu8: u8, bu16: u16, ai8: i8, ai16: i16, x: i32, y: u32) {
            assert(ai8 == x && bu8 == y ==> (ai8 >> bu8) == (x >> y)) by(bit_vector);
            assert(au8 == x && bu8 == y ==> (au8 >> bu8) == (x >> y)) by(bit_vector);
            assert(ai8 == x && bu16 == y ==> (ai8 >> bu16) == (x >> y)) by(bit_vector);
            assert(au8 == x && bu16 == y ==> (au8 >> bu16) == (x >> y)) by(bit_vector);
            assert(ai16 == x && bu8 == y ==> (ai16 >> bu8) == (x >> y)) by(bit_vector);
            assert(au16 == x && bu8 == y ==> (au16 >> bu8) == (x >> y)) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_by_equating_shl verus_code! {
        fn test_shl(au8: u8, au16: u16, bu8: u8, bu16: u16, ai8: i8, ai16: i16, x: i32, y: u32) {
            assert(ai8 == x && bu8 == y ==> (ai8 << bu8) == (x << y) as i8) by(bit_vector);
            assert(au8 == x && bu8 == y ==> (au8 << bu8) == (x << y) as u8) by(bit_vector);
            assert(ai8 == x && bu16 == y ==> (ai8 << bu16) == (x << y) as i8) by(bit_vector);
            assert(au8 == x && bu16 == y ==> (au8 << bu16) == (x << y) as u8) by(bit_vector);
            assert(ai16 == x && bu8 == y ==> (ai16 << bu8) == (x << y) as i16) by(bit_vector);
            assert(au16 == x && bu8 == y ==> (au16 << bu8) == (x << y) as u16) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_forall verus_code! {
        proof fn test() {
            assert(forall |x: i32, y: i16| x == y ==> (x >> 2) == (y >> 2)) by(bit_vector);
            assert(forall |x: i32, y: i16| x >> 32 == y >> 16) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_let_binder verus_code! {
        proof fn test(x: i32, y: i16) {
            assert({let z = y; x == y ==> (x >> 2) == (z >> 2)}) by(bit_vector);
            assert({let z = y; x == y ==> (x >> 2) == (z >> 3)}) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_normal_solver verus_code! {
        fn test_unsigned(x: u16, y: u16) {
            assert((x | y) == (x as u32) | (y as u32));
            assert((x & y) == (x as u32) & (y as u32));
            assert((x ^ y) == (x as u32) ^ (y as u32));

            assert((x | y) == (x as i64) | (y as i64));
            assert((x & y) == (x as i64) & (y as i64));
            assert((x ^ y) == (x as i64) ^ (y as i64));
        }

        fn test_signed(x: i16, y: i16) {
            assert((x | y) == (x as i32) | (y as i32));
            assert((x & y) == (x as i32) & (y as i32));
            assert((x ^ y) == (x as i32) ^ (y as i32));
        }

        fn test_signed_fail(x: i16, y: i16) {
            assert((x | y) == (x as u32) | (y as u32)); // FAILS
        }

        fn test_signed_fail2(x: i16, y: i16) {
            assert((x & y) == (x as u32) & (y as u32)); // FAILS
        }

        fn test_signed_not(x: i16) {
            assert(!x == !(x as i32));
        }

        fn test_unsigned_not(x: u16) {
            assert(!x == !(x as u32)); // FAILS
        }

        fn test_shr(x: u16, y: u16) {
            assert(x >> 2 == (x as u32) >> 2);
            assert(x >> y == x >> (y as u32));
        }

        fn test_shl(x: u16) {
            assert(x << 2 == (x as u32) << 2); // FAILS
        }

        fn test_shl2(x: u16, y: u16) {
            assert(x >> y == x >> (y as u32));
        }

        fn test_shr_signed(x: i16, y: u16) {
            assert(x >> 2 == (x as i32) >> 2);
            assert(x >> y == x >> (y as u32));
        }

        fn test_shl_signed(x: i16) {
            assert(x << 2 == (x as i32) << 2); // FAILS
        }

        fn test_shl2_signed(x: i16, y: u16) {
            assert(x >> y == x >> (y as u32));
        }

        fn test_bounds(x: u16, y: u16, z: u32, w: int) {
            assert(0 <= (x | y) < 0x1_0000);
            assert(0 <= (x & y) < 0x1_0000);
            assert(0 <= (x ^ y) < 0x1_0000);
            assert(0 <= (x >> y) < 0x1_0000);
            assert(0 <= (x << y) < 0x1_0000);

            assert(0 <= (x >> z) < 0x1_0000);
            assert(0 <= (x << z) < 0x1_0000);

            assert(0 <= (x >> w) < 0x1_0000);
            assert(0 <= (x << w) < 0x1_0000);
        }
    } => Err(err) => assert_fails(err, 5)
}
