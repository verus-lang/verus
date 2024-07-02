#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_overflow_spec_pass verus_code! {
        use vstd::*;
        fn test(a: u64) {
            let ghost mut j: u64 = a;
            proof { j = add(j, 2); }
            assert(j == add(a, 2));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_overflow_spec_fails_1 verus_code! {
        proof fn test(a: u64) {
            let mut j = a;
            j = add(j, 2);
            assert(j == a as nat + 2); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_overflow_fails_1 verus_code! {
        fn test(a: u64) {
            let mut j = a;
            j = j + 2; // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_overflow_spec_fails_2 verus_code! {
        use vstd::*;
        fn test(a: u64) {
            let ghost mut j: u64 = a;
            proof {
                j = add(j, 2);
                j = add(j, 2);
            }
            assert(j == a + 4); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_overflow_fails_2 verus_code! {
        fn test(a: u64) {
            let mut j = a;
            j = j + 2; // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_divide_by_zero verus_code! {
        fn ok(a: u8, b: u8)
            requires b != 0
        {
            let x = a / b;
            let y = a % b;
        }
        fn fail1(a: u8, b: u8) {
            let x = a / b; // FAILS
        }
        fn fail2(a: u8, b: u8) {
            let y = a % b; // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] test_const_ok verus_code! {
        const C: u8 = 254 + 1;
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_const_fail verus_code! {
        const C: u8 = 255 + 1 /* FAILS */;
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_static_fail verus_code! {
        exec static C: u8 = 255 + 1 /* FAILS */;
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_literal_out_of_range verus_code! {
        const C: u8 = 256 - 1;
    } => Err(err) => assert_vir_error_msg(err, "integer literal out of range")
}

test_verify_one_file! {
    #[test] test_overflow_fails_usize verus_code! {
        fn test(a: usize) -> usize {
            let b = a + 1; // FAILS
            b
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_overflow_ensures_pass verus_code! {
        fn test(a: usize) -> (r: usize)
            requires a < 30
            ensures r == a + 1
        {
            let b = a + 1;
            b
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] underflow verus_code! {
        fn underflow() {
            let mut a: u64 = 0;
            a = a - 1; // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] bit_shift_overflow verus_code! {
        fn test_overflow_right_shift() {
            let x: u16 = 0;
            let y: u16 = 16;

            let z = x >> y; // FAILS
        }

        fn test_overflow_right_shift2() {
            let x: u16 = 0;
            let y: u16 = 17;

            let z = x >> y; // FAILS
        }

        fn test_overflow_right_shift3() {
            let x: u16 = 0;
            let y: u16 = 15;

            // this one is ok
            let z = x >> y;
        }

        fn test_overflow_left_arg_doesnt_matter() {
            let x: u16 = 16;
            let y: u16 = 5;

            // this one is ok
            let z = x >> y;
        }

        fn test_overflow_left_shift() {
            let x: u16 = 0;
            let y: u16 = 16;

            let z = x << y; // FAILS
        }

        fn test_usize_overflow() {
            let x: usize = 0;
            let y: usize = 32;

            let z = x << y; // FAILS
        }

        fn test_usize_overflow2() {
            let x: usize = 0;
            let y: usize = usize::BITS as usize;

            let z = x << y; // FAILS
        }

        fn test_usize_overflow3() {
            let x: usize = 0;
            let y: usize = (usize::BITS - 1) as usize;

            // this is ok
            let z = x << y;
        }
    } => Err(e) => assert_fails(e, 5)
}

test_verify_one_file! {
    #[test] bit_shift_width_mismatch verus_code! {
        fn test_underflow() {
            // This type mismatch is unsupported; however, if it is ever supported,
            // it should be an overflow error.
            let x: u16 = 0;
            let y: u32 = 40;

            let z = x << y; // FAILS
        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_one_file! {
    #[test] bit_shift_width_mismatch_signed verus_code! {
        fn test_underflow() {
            // This type mismatch is unsupported; however, if it is ever supported,
            // it should be an underflow error.
            let x: u16 = 0;
            let y: i32 = -1;

            let z = x << y; // FAILS
        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_one_file! {
    #[test] bit_shift_unsigned_shift_signed verus_code! {
        fn test_underflow() {
            let x: u16 = 0;
            let y: i16 = -1;

            let z = x << y; // FAILS
        }
    } => Err(e) => assert_vir_error_msg(e, "possible bit shift underflow/overflow")
}

test_verify_one_file! {
    #[test] bit_shift_underflow verus_code! {
        fn test_underflow() {
            let x: i16 = 0;
            let y: i16 = -1;

            let z = x << y; // FAILS
        }
    } => Err(e) => assert_vir_error_msg(e, "possible bit shift underflow/overflow")
}

test_verify_one_file_with_options! {
    #[test] bit_shift_overflow_arch32 ["vstd"] => verus_code! {
        global size_of usize == 4;

        fn test_usize_overflow() {
            let x: usize = 0;
            let y: usize = 32;

            let z = x << y; // FAILS
        }

        fn test_usize_overflow2() {
            let x: usize = 0;
            let y: usize = 31;

            let z = x << y;
        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_one_file_with_options! {
    #[test] bit_shift_overflow_arch64 ["vstd"] => verus_code! {
        global size_of usize == 8;

        fn test_usize_overflow() {
            let x: usize = 0;
            let y: usize = 64;

            let z = x << y; // FAILS
        }

        fn test_usize_overflow2() {
            let x: usize = 0;
            let y: usize = 63;

            let z = x << y;
        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_one_file! {
    #[test] spec_bitshift_defined_for_larger_ints verus_code! {
        fn test() {
            // Unlike Rust, Z3's bitvector reasoning allows the right-hand side to
            // be out-of-range
            assert(1u8 >> 20u8 == 0u8) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] spec_bitshift_negative verus_code! {
        // TODO bit_vector solver currently doesn't support bit-shifts by signed types.
        // However, if it ever does, then this test case should test that Verus
        // checks for underflow (maybe as a recommends check?)

        // If our solver interprets (-1i8) as 255 then the following assert would pass,
        // but it may be preferable to leave shifts-by-negatives underspecified?
        // That can be decided later, though.
        fn test() {
            assert(1i8 >> (-1i8) == 0i8) by(bit_vector); // FAILS
        }
    } => Err(e) => assert_vir_error_msg(e, "bit-shift with possibly negative shift")
}

test_verify_one_file! {
    #[test] nonlinear_ops_dont_overflow_unsigned verus_code!{
        fn test_mul(x: u16, y: u16) {
            assert(((x as nat) * (y as nat)) as int == (x as int) * (y as int));
        }

        fn test_div(a: u32, b: u32)
            requires b != 0
        {
            let x = a / b;
            assert(x as int == a as int / b as int);
        }

        fn test_mod(a: u32, b: u32)
            requires b != 0
        {
            let x = a % b;
            assert(x as int == a as int % b as int);
        }

        // Make sure axiom about % properly accounts for 0:

        proof fn test_mod_by_0(a: u32, b: u32) {
            assert((a as int % 0 as int) < 0); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}
