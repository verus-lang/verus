#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        fn test_ret(b: bool) -> (i: u64)
            ensures
                10 <= i,
                20 <= i,
        {
            if b {
                return 20;
            }
            30
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 verus_code! {
        fn test_ret(b: bool) -> (i: u64)
            ensures
                10 <= i,
                20 <= i,
        {
            if b {
                return 10; // FAILS
            }
            30
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2 verus_code! {
        fn test_ret(b: bool) -> (i: u64)
            ensures
                10 <= i,
                20 <= i, // FAILS
        {
            if b {
                return 20;
            }
            10
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        fn test_ret(b: bool)
            ensures true
        {
            if b {
                return;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2_fails verus_code! {
        fn test_ret(b: bool)
            requires b
            ensures false
        {
            if b {
                return; // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3 verus_code! {
        fn test_ret(b: bool)
            requires b
            ensures b
        {
            while b || !b
                invariant b
            {
                return;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3_fails verus_code! {
        fn test_ret(b: bool)
            requires b
            ensures b
        {
            while b || !b {
                return; // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] regression_215 verus_code! {
        fn f() {
            return ();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] returning_named_unit verus_code! {
        // TODO All of these panic right now

        // This should probably pass:

        proof fn f() -> (n: ())
            ensures n === ()
        {
            return ();
        }

        // This should either pass or fail with a sensible error message:

        proof fn g() -> (n: ())
            ensures n === ()
        {
            return;
        }

        proof fn f_fail() -> (n: ())
            ensures n === ()
        {
            return (); // FAILS
        }

        proof fn g_fail() -> (n: ())
            ensures n === ()
        {
            return; // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}
