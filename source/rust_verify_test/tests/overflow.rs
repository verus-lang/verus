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
