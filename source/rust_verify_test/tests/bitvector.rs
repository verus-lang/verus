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
            assert(b << 2 == b * 4) by(bit_vector);
            assert(b << 2 == b * 4);  // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "Inside bit-vector assertion, use `add` `sub` `mul` for fixed-bit operators")
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
    #[test] test8_fails verus_code! {
        proof fn test8(b: i32) {
            assert(b <= b) by(bit_vector); // VIR Error: signed int
        }
    } => Err(err) => assert_vir_error_msg(err, "signed integer is not supported for bit-vector reasoning")
}

test_verify_one_file! {
    //https://github.com/verus-lang/verus/issues/191 (@matthias-brun)
    #[test] test10_fails verus_code! {
        #[verifier(bit_vector)]
        proof fn f2() {
            ensures(forall |i: u64| (1 << i) > 0); // FAILS: should not panic
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] not_supported_usize_in_by_bit_vector verus_code! {
        proof fn test_usize(x: usize) {
            // Ideally this would work, but by(bit_vector) currently doesn't
            // support arch-dependent sizes.
            assert(x & x == x) by (bit_vector);
        }
    } => Err(err) => assert_vir_error_msg(err, "architecture-dependent")
}

test_verify_one_file! {
    #[test] not_supported_const_usize_in_by_bit_vector verus_code! {
        proof fn test_usize() {
            // Ideally this would work, but by(bit_vector) currently doesn't
            // support arch-dependent sizes.
            assert(1usize == 1usize) by (bit_vector);
        }
    } => Err(err) => assert_vir_error_msg(err, "architecture-dependent")
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
    #[test] not_supported_const_int_in_by_bit_vector verus_code! {
        proof fn test_int() {
            assert(0int == 0int) by (bit_vector);
        }
    } => Err(err) => assert_vir_error_msg(err, "expected finite-width integer")
}

test_verify_one_file! {
    #[test] not_supported_usize_cast_in_by_bit_vector verus_code! {
        proof fn test_usize(x: u64) {
            // Ideally this would work, but by(bit_vector) currently doesn't
            // support arch-dependent sizes.
            assert((x as usize) == (x as usize)) by (bit_vector);
        }
    } => Err(err) => assert_vir_error_msg(err, "architecture-dependent")
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
    #[test] bit_vector_usize_as_32bit ["--arch-word-bits 32"] => verus_code! {
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
    #[test] bit_vector_usize_as_64bit ["--arch-word-bits 64"] => verus_code! {
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
