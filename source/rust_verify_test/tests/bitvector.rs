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
            assert(((-1i32) ^ (7i32)) + 0 == -8) by(bit_vector);
            assert(((-1i32) ^ (7i32)) - 0 == -8) by(bit_vector);
            assert(((-1i32) ^ (7i32)) * 0 == 0) by(bit_vector);
            assert(((-1i32) ^ (7i32)) + 15 == 7) by(bit_vector);
            assert(((-1i32) ^ (7i32)) - 15 == -23) by(bit_vector);
            assert(((-1i32) ^ (7i32)) * 15 == -120) by(bit_vector);
            assert(!(-8i32) + 0 == 7) by(bit_vector);
            assert(!(-8i32) - 0 == 7) by(bit_vector);
            assert(!(-8i32) * 0 == 0) by(bit_vector);
            assert(!(-8i32) + 15 == 22) by(bit_vector);
            assert(!(-8i32) - 15 == -8) by(bit_vector);
            assert(!(-8i32) * 15 == 105) by(bit_vector);
            assert(0 + ((-1i32) ^ (7i32)) == -8) by(bit_vector);
            assert(0 - ((-1i32) ^ (7i32)) == 8) by(bit_vector);
            assert(0 * ((-1i32) ^ (7i32)) == 0) by(bit_vector);
            assert(0 + !(-8i32) == 7) by(bit_vector);
            assert(0 - !(-8i32) == -7) by(bit_vector);
            assert(0 * !(-8i32) == 0) by(bit_vector);
            assert(15 + ((-1i32) ^ (7i32)) == 7) by(bit_vector);
            assert(15 - ((-1i32) ^ (7i32)) == 23) by(bit_vector);
            assert(15 * ((-1i32) ^ (7i32)) == -120) by(bit_vector);
            assert(15 + !(-8i32) == 22) by(bit_vector);
            assert(15 - !(-8i32) == 8) by(bit_vector);
            assert(15 * !(-8i32) == 105) by(bit_vector);
            assert(0 + 0 == 0) by(bit_vector);
            assert(0 - 0 == 0) by(bit_vector);
            assert(0 * 0 == 0) by(bit_vector);
            assert(0 + 15 == 15) by(bit_vector);
            assert(0 - 15 == -15) by(bit_vector);
            assert(0 * 15 == 0) by(bit_vector);
            assert(15 + 0 == 15) by(bit_vector);
            assert(15 - 0 == 15) by(bit_vector);
            assert(15 * 0 == 0) by(bit_vector);
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
            assert(((-1i32) ^ (127i32)) + 0 == -128) by(bit_vector);
            assert(((-1i32) ^ (127i32)) - 0 == -128) by(bit_vector);
            assert(((-1i32) ^ (127i32)) * 0 == 0) by(bit_vector);
            assert(((-1i32) ^ (127i32)) + 255 == 127) by(bit_vector);
            assert(((-1i32) ^ (127i32)) - 255 == -383) by(bit_vector);
            assert(((-1i32) ^ (127i32)) * 255 == -32640) by(bit_vector);
            assert(!(-128i32) + 0 == 127) by(bit_vector);
            assert(!(-128i32) - 0 == 127) by(bit_vector);
            assert(!(-128i32) * 0 == 0) by(bit_vector);
            assert(!(-128i32) + 255 == 382) by(bit_vector);
            assert(!(-128i32) - 255 == -128) by(bit_vector);
            assert(!(-128i32) * 255 == 32385) by(bit_vector);
            assert(0 + ((-1i32) ^ (127i32)) == -128) by(bit_vector);
            assert(0 - ((-1i32) ^ (127i32)) == 128) by(bit_vector);
            assert(0 * ((-1i32) ^ (127i32)) == 0) by(bit_vector);
            assert(0 + !(-128i32) == 127) by(bit_vector);
            assert(0 - !(-128i32) == -127) by(bit_vector);
            assert(0 * !(-128i32) == 0) by(bit_vector);
            assert(255 + ((-1i32) ^ (127i32)) == 127) by(bit_vector);
            assert(255 - ((-1i32) ^ (127i32)) == 383) by(bit_vector);
            assert(255 * ((-1i32) ^ (127i32)) == -32640) by(bit_vector);
            assert(255 + !(-128i32) == 382) by(bit_vector);
            assert(255 - !(-128i32) == 128) by(bit_vector);
            assert(255 * !(-128i32) == 32385) by(bit_vector);
            assert(0 + 0 == 0) by(bit_vector);
            assert(0 - 0 == 0) by(bit_vector);
            assert(0 * 0 == 0) by(bit_vector);
            assert(0 + 255 == 255) by(bit_vector);
            assert(0 - 255 == -255) by(bit_vector);
            assert(0 * 255 == 0) by(bit_vector);
            assert(255 + 0 == 255) by(bit_vector);
            assert(255 - 0 == 255) by(bit_vector);
            assert(255 * 0 == 0) by(bit_vector);
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
            assert(((-1i32) ^ (127i32)) + 0 == -128) by(bit_vector);
            assert(((-1i32) ^ (127i32)) - 0 == -128) by(bit_vector);
            assert(((-1i32) ^ (127i32)) * 0 == 0) by(bit_vector);
            assert(((-1i32) ^ (127i32)) + 65535 == 65407) by(bit_vector);
            assert(((-1i32) ^ (127i32)) - 65535 == -65663) by(bit_vector);
            assert(((-1i32) ^ (127i32)) * 65535 == -8388480) by(bit_vector);
            assert(!(-128i32) + 0 == 127) by(bit_vector);
            assert(!(-128i32) - 0 == 127) by(bit_vector);
            assert(!(-128i32) * 0 == 0) by(bit_vector);
            assert(!(-128i32) + 65535 == 65662) by(bit_vector);
            assert(!(-128i32) - 65535 == -65408) by(bit_vector);
            assert(!(-128i32) * 65535 == 8322945) by(bit_vector);
            assert(0 + ((-1i32) ^ (32767i32)) == -32768) by(bit_vector);
            assert(0 - ((-1i32) ^ (32767i32)) == 32768) by(bit_vector);
            assert(0 * ((-1i32) ^ (32767i32)) == 0) by(bit_vector);
            assert(0 + !(-32768i32) == 32767) by(bit_vector);
            assert(0 - !(-32768i32) == -32767) by(bit_vector);
            assert(0 * !(-32768i32) == 0) by(bit_vector);
            assert(255 + ((-1i32) ^ (32767i32)) == -32513) by(bit_vector);
            assert(255 - ((-1i32) ^ (32767i32)) == 33023) by(bit_vector);
            assert(255 * ((-1i32) ^ (32767i32)) == -8355840) by(bit_vector);
            assert(255 + !(-32768i32) == 33022) by(bit_vector);
            assert(255 - !(-32768i32) == -32512) by(bit_vector);
            assert(255 * !(-32768i32) == 8355585) by(bit_vector);
            assert(0 + 0 == 0) by(bit_vector);
            assert(0 - 0 == 0) by(bit_vector);
            assert(0 * 0 == 0) by(bit_vector);
            assert(0 + 65535 == 65535) by(bit_vector);
            assert(0 - 65535 == -65535) by(bit_vector);
            assert(0 * 65535 == 0) by(bit_vector);
            assert(255 + 0 == 255) by(bit_vector);
            assert(255 - 0 == 255) by(bit_vector);
            assert(255 * 0 == 0) by(bit_vector);
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
            assert(((-1i32) ^ (32767i32)) + 0 == -32768) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) - 0 == -32768) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) * 0 == 0) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) + 255 == -32513) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) - 255 == -33023) by(bit_vector);
            assert(((-1i32) ^ (32767i32)) * 255 == -8355840) by(bit_vector);
            assert(!(-32768i32) + 0 == 32767) by(bit_vector);
            assert(!(-32768i32) - 0 == 32767) by(bit_vector);
            assert(!(-32768i32) * 0 == 0) by(bit_vector);
            assert(!(-32768i32) + 255 == 33022) by(bit_vector);
            assert(!(-32768i32) - 255 == 32512) by(bit_vector);
            assert(!(-32768i32) * 255 == 8355585) by(bit_vector);
            assert(0 + ((-1i32) ^ (127i32)) == -128) by(bit_vector);
            assert(0 - ((-1i32) ^ (127i32)) == 128) by(bit_vector);
            assert(0 * ((-1i32) ^ (127i32)) == 0) by(bit_vector);
            assert(0 + !(-128i32) == 127) by(bit_vector);
            assert(0 - !(-128i32) == -127) by(bit_vector);
            assert(0 * !(-128i32) == 0) by(bit_vector);
            assert(65535 + ((-1i32) ^ (127i32)) == 65407) by(bit_vector);
            assert(65535 - ((-1i32) ^ (127i32)) == 65663) by(bit_vector);
            assert(65535 * ((-1i32) ^ (127i32)) == -8388480) by(bit_vector);
            assert(65535 + !(-128i32) == 65662) by(bit_vector);
            assert(65535 - !(-128i32) == 65408) by(bit_vector);
            assert(65535 * !(-128i32) == 8322945) by(bit_vector);
            assert(0 + 0 == 0) by(bit_vector);
            assert(0 - 0 == 0) by(bit_vector);
            assert(0 * 0 == 0) by(bit_vector);
            assert(0 + 255 == 255) by(bit_vector);
            assert(0 - 255 == -255) by(bit_vector);
            assert(0 * 255 == 0) by(bit_vector);
            assert(65535 + 0 == 65535) by(bit_vector);
            assert(65535 - 0 == 65535) by(bit_vector);
            assert(65535 * 0 == 0) by(bit_vector);
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
            assert(((-1i32) ^ (16383i32)) + 0 == -16384) by(bit_vector);
            assert(((-1i32) ^ (16383i32)) - 0 == -16384) by(bit_vector);
            assert(((-1i32) ^ (16383i32)) * 0 == 0) by(bit_vector);
            assert(((-1i32) ^ (16383i32)) + 65535 == 49151) by(bit_vector);
            assert(((-1i32) ^ (16383i32)) - 65535 == -81919) by(bit_vector);
            assert(((-1i32) ^ (16383i32)) * 65535 == -1073725440) by(bit_vector);
            assert(!(-16384i32) + 0 == 16383) by(bit_vector);
            assert(!(-16384i32) - 0 == 16383) by(bit_vector);
            assert(!(-16384i32) * 0 == 0) by(bit_vector);
            assert(!(-16384i32) + 65535 == 81918) by(bit_vector);
            assert(!(-16384i32) - 65535 == -49152) by(bit_vector);
            assert(!(-16384i32) * 65535 == 1073659905) by(bit_vector);
            assert(0 + ((-1i32) ^ (32767i32)) == -32768) by(bit_vector);
            assert(0 - ((-1i32) ^ (32767i32)) == 32768) by(bit_vector);
            assert(0 * ((-1i32) ^ (32767i32)) == 0) by(bit_vector);
            assert(0 + !(-32768i32) == 32767) by(bit_vector);
            assert(0 - !(-32768i32) == -32767) by(bit_vector);
            assert(0 * !(-32768i32) == 0) by(bit_vector);
            assert(32767 + ((-1i32) ^ (32767i32)) == -1) by(bit_vector);
            assert(32767 - ((-1i32) ^ (32767i32)) == 65535) by(bit_vector);
            assert(32767 * ((-1i32) ^ (32767i32)) == -1073709056) by(bit_vector);
            assert(32767 + !(-32768i32) == 65534) by(bit_vector);
            assert(32767 - !(-32768i32) == 0) by(bit_vector);
            assert(32767 * !(-32768i32) == 1073676289) by(bit_vector);
            assert(0 + 0 == 0) by(bit_vector);
            assert(0 - 0 == 0) by(bit_vector);
            assert(0 * 0 == 0) by(bit_vector);
            assert(0 + 65535 == 65535) by(bit_vector);
            assert(0 - 65535 == -65535) by(bit_vector);
            assert(0 * 65535 == 0) by(bit_vector);
            assert(32767 + 0 == 32767) by(bit_vector);
            assert(32767 - 0 == 32767) by(bit_vector);
            assert(32767 * 0 == 0) by(bit_vector);
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
            assert(!(-32768i32) + 0 == 32767) by(bit_vector);
            assert(!(-32768i32) - 0 == 32767) by(bit_vector);
            assert(!(-32768i32) * 0 == 0) by(bit_vector);
            assert(!(-32768i32) + 32767 == 65534) by(bit_vector);
            assert(!(-32768i32) - 32767 == 0) by(bit_vector);
            assert(!(-32768i32) * 32767 == 1073676289) by(bit_vector);
            assert(0 + ((-1i32) ^ (16383i32)) == -16384) by(bit_vector);
            assert(0 - ((-1i32) ^ (16383i32)) == 16384) by(bit_vector);
            assert(0 * ((-1i32) ^ (16383i32)) == 0) by(bit_vector);
            assert(0 + !(-16384i32) == 16383) by(bit_vector);
            assert(0 - !(-16384i32) == -16383) by(bit_vector);
            assert(0 * !(-16384i32) == 0) by(bit_vector);
            assert(65535 + ((-1i32) ^ (16383i32)) == 49151) by(bit_vector);
            assert(65535 - ((-1i32) ^ (16383i32)) == 81919) by(bit_vector);
            assert(65535 * ((-1i32) ^ (16383i32)) == -1073725440) by(bit_vector);
            assert(65535 + !(-16384i32) == 81918) by(bit_vector);
            assert(65535 - !(-16384i32) == 49152) by(bit_vector);
            assert(65535 * !(-16384i32) == 1073659905) by(bit_vector);
            assert(0 + 0 == 0) by(bit_vector);
            assert(0 - 0 == 0) by(bit_vector);
            assert(0 * 0 == 0) by(bit_vector);
            assert(0 + 32767 == 32767) by(bit_vector);
            assert(0 - 32767 == -32767) by(bit_vector);
            assert(0 * 32767 == 0) by(bit_vector);
            assert(65535 + 0 == 65535) by(bit_vector);
            assert(65535 - 0 == 65535) by(bit_vector);
            assert(65535 * 0 == 0) by(bit_vector);
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
