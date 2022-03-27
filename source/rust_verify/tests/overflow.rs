#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_overflow_spec_pass code! {
        fn test(a: u64) {
            #[spec] let mut j = a;
            j = j + 2;
            assert(j == a + 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_overflow_fails_0 code! {
        fn test(a: u64) {
            let mut j = a;
            j = j + 2; // FAILS
            assert(j == a + 2);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_overflow_spec_fails_1 code! {
        fn test(a: u64) {
            #[spec] let mut j = a;
            j = j + 2;
            assert(j == a as nat + 2); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_overflow_fails_1 code! {
        fn test(a: u64) {
            let mut j = a;
            j = j + 2; // FAILS
            assert(j == a as nat + 2);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_overflow_spec_fails_2 code! {
        fn test(a: u64) {
            #[spec] let mut j = a;
            j = j + 2;
            j = j + 2;
            assert(j == a + 4); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_overflow_fails_2 code! {
        fn test(a: u64) {
            let mut j = a;
            j = j + 2; // FAILS
            j = j + 2;
            assert(j == a + 4);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_divide_by_zero code! {
        fn ok(a: u8, b: u8) {
            requires(b != 0);
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
    #[test] test_literal_out_of_range code! {
        const C: u8 = 256 - 1;
    } => Err(e) => assert_vir_error(e)
}
