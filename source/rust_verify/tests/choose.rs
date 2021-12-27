#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 code! {
        #[spec]
        fn f(i: int) -> bool {
            5 <= i
        }

        #[proof]
        fn test_choose() {
            let i = choose(|i: int| f(i));
            assert(f(7));
            assert(5 <= i);
        }

        #[proof]
        fn test_choose_eq() {
            let i1 = choose(|i: int| f(i) && (1 + 1 == 2));
            let i2 = choose(|i: int| f(i) && (2 + 2 == 4));
            assert(i1 == i2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 code! {
        #[spec]
        fn f(i: int) -> bool {
            5 <= i
        }

        #[proof]
        fn test_choose() {
            let i = choose(|i: int| f(i));
            assert(5 <= i); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2 code! {
        #[spec]
        fn f(i: int) -> bool {
            5 <= i
        }

        #[proof]
        fn test_choose() {
            let i = choose(|i: int| f(i));
            assert(f(7));
            assert(i == 7); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails3 code! {
        #[spec]
        fn f(i: int) -> bool {
            5 <= i
        }

        #[proof]
        fn test_choose_eq() {
            let i1 = choose(|i: int| f(i) && (2 + 2 == 4));
            let i2 = choose(|i: int| (2 + 2 == 4) && f(i));
            // requires extensional equality
            assert(i1 == i2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_refine code! {
        #[spec]
        fn cnatf(n: nat) -> bool {
            true
        }

        #[spec]
        fn cintf(n: int) -> bool {
            true
        }

        #[proof]
        fn cnat() {
            assert(choose(|n: nat| cnatf(n)) >= 0);
            assert(choose(|n: nat| cintf(n) && n < 0) >= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_refine_fail1 code! {
        #[spec]
        fn cintf(n: int) -> bool {
            true
        }

        #[proof]
        fn cnat() {
            assert(cintf(-10));
            assert(choose(|n: nat| cintf(n) && n < 0) < 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_refine2 code! {
        #[spec]
        fn cnatf(n: nat) -> bool {
            true
        }

        #[proof]
        fn cnat() {
            assert(cnatf(10));
            assert(choose(|n: nat| cnatf(n) && n >= 10) >= 10);
        }
    } => Ok(())
}
