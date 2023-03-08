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
    #[test] bit_shift_underflow verus_code! {
        // TODO Verus currently doesn't support bit-shifts by signed types.
        // However, if it ever does, then this test case should test that Verus
        // checks for underflow.
        fn test_underflow() {
            let x: u16 = 0;
            let y: i16 = -1;

            let z = 0 << y; // FAILS
        }
    } => Err(e) => assert_vir_error_msg(e, "argument bit-width does not match")
}

test_verify_one_file_with_options! {
    #[test] bit_shift_overflow_arch32 ["--arch-word-bits 32"] => verus_code! {
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
    #[test] bit_shift_overflow_arch64 ["--arch-word-bits 64"] => verus_code! {
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
