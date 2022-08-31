#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 code! {
        fn test_ret(b: bool) -> u64 {
            ensures(|i: u64| [
                10 <= i,
                20 <= i,
            ]);

            if b {
                return 20;
            }
            30
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 code! {
        fn test_ret(b: bool) -> u64 {
            ensures(|i: u64| [
                10 <= i,
                20 <= i,
            ]);

            if b {
                return 10; // FAILS
            }
            30
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2 code! {
        fn test_ret(b: bool) -> u64 {
            ensures(|i: u64| [
                10 <= i,
                20 <= i, // FAILS
            ]);

            if b {
                return 20;
            }
            10
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2 code! {
        fn test_ret(b: bool) {
            ensures(true);

            if b {
                return;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2_fails code! {
        fn test_ret(b: bool) {
            ensures(false);
            requires(b);

            if b {
                return; // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3 code! {
        fn test_ret(b: bool) {
            requires(b);
            ensures(b);

            while b || !b {
                invariant(b);
                return;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3_fails code! {
        fn test_ret(b: bool) {
            requires(b);
            ensures(b);

            while b || !b {
                return; // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] regression_215 verus_code! {
        // NOTE: we may want to allow this, but fixing the panic in #215 was the priority
        fn f() {
            return ();
        }
    } => Err(e) => assert_vir_error(e)
}
