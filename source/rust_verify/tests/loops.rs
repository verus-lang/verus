#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] basic_while code! {
        fn test1() {
            let mut i = 0;
            while i < 10 {
                invariant([
                    i <= 10
                ]);
                i = i + 1;
            }
            assert(i == 10);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_while_fail1 code! {
        fn test1() {
            let mut i = 0;
            while i < 10 {
                i = i + 1;
            }
            assert(i == 10); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] basic_while_fail2 code! {
        fn test1() {
            let mut i = 0;
            let mut j = 0;
            while i < 10 {
                i = i + 1;
                while j < 5 {
                    j = j + 1;
                }
            }
            assert(j == 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] complex_while code! {
        fn test1() {
            let mut i = 0;
            let mut x = 0;
            while {x = x + 1; i < 10} {
                invariant([
                    i <= 10,
                    x == i,
                ]);
                i = i + 1;
            }
            assert(i == 10);
            assert(x == 11);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] complex_while_fail1 code! {
        fn test1() {
            let mut i = 0;
            let mut x = 0;
            while {x = x + 1; i < 10} {
                invariant([
                    i <= 10,
                    x == i,
                ]);
                i = i + 1;
            }
            assert(i == 10);
            assert(x != 11); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] complex_while2 code! {
        #[proof]
        fn check(a: u64) {
            requires(1 <= a);
        }

        fn test1() {
            let mut i = 0;
            let mut x = 0;
            while {x = x + 1; check(x); i < 10} {
                invariant([
                    i <= 10,
                    x == i,
                ]);
                i = i + 1;
            }
            assert(i == 10);
            assert(x == 11);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] complex_while2_fail code! {
        #[proof]
        fn check(a: u64) {
            requires(2 <= a); // FAILS
        }

        fn test1() {
            let mut i = 0;
            let mut x = 0;
            while {
                x = x + 1;
                check(x); // FAILS
                i < 10
            } {
                invariant([
                    i <= 10,
                    x == i,
                ]);
                i = i + 1;
            }
            assert(i == 10);
            assert(x == 11);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    // TODO: support break in loops?
    #[test] #[ignore] break_test code! {
        fn test1(a: int, b: int) {
            let mut i = a;
            while i >= 1 {
                if a % i == 0 && b % i == 0 {
                    break;
                }
            }
            assert(a % i == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_variables_havoc_basic code! {
        fn test(a: u64) {
            requires(a < 10);
            let mut i = a;
            while i < 20 {
                i = i + 1;
            }
            assert(i == a); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_variables_not_havoc_basic code! {
        fn test(a: u64) {
            requires(a < 10);
            let mut i = a;
            let mut j = a;
            j = j + 2;
            while i < 20 {
                i = i + 1;
            }
            j = j + 2;
            assert(j == a + 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_variables_no_effect_basic code! {
        fn test(a: u64) {
            requires(a < 10);
            let mut i = a;
            let mut k = 12;
            while i < 20 {
                let mut k = i;
                i = i + 1;
                k = k + 1;
                assert(k == i);
            }
            k = k + 1;
            assert(k == 13);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_variables_havoc_nested code! {
        fn test(a: u64) {
            requires(a < 10);
            let mut i = a;
            while i < 20 {
                i = i + 1;
                let mut j = a;
                while j < 10 {
                    j = j + 1;
                }
                assert(j == a); // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_variables_not_havoc_nested code! {
        fn test(a: u64) {
            requires(a < 10);
            let mut i = a;
            let mut j = a;
            j = j + 2;
            while i < 20 {
                i = i + 1;
                let mut j = a;
                while j < 20 {
                    j = j + 1;
                }
            }
            j = j + 2;
            assert(j == a + 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_variables_no_effect_nested code! {
        fn test(a: u64) {
            requires(a < 10);
            let mut i = a;
            let mut k = 12;
            while i < 20 {
                let mut k = i;
                i = i + 1;
                while k < 20 {
                    k = k + 1;
                }
            }
            k = k + 1;
            assert(k == 13);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_loop code! {
        fn test() {
            #[spec] let mut a: int = 5;
            loop {
                invariant(a > 0);
                a = a + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_loop_fail code! {
        fn test() {
            #[spec] let mut a: int = 5;
            loop {
                invariant(a > 0); // FAILS
                a = a - 1;
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] basic_loop_new_vars code! {
        fn test() {
            #[spec] let mut a: int = 5;
            loop {
                invariant([
                    {#[spec] let b = 0; a > b},
                    {#[spec] let b = 0; a > b},
                ]);
                a = a + 1;
            }
        }
    } => Ok(())
}
