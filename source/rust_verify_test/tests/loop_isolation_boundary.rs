#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] basic verus_code! {
        #[verifier::exec_allows_no_decreases_clause]
        fn test() {
            let i = 0;
            let y = 5;

            #[verifier::loop_isolation_boundary]
            {
                let x = 5;
                while i < 10 {
                    assert(x == 5);
                    assert(y == 5); // FAILS
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test2(x: &mut u64) {
            let i = 0;
            let y = 5;

            #[verifier::loop_isolation_boundary]
            {
                assert(y == 5);
                while i < 10 {
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_stuff_havoced(x: &mut u64) {
            let mut i = 0;
            let j = 0;

            #[verifier::loop_isolation_boundary]
            {
                assert(i == j);
                while i < 10 {
                    assert(i == j); // FAILS
                    i = i + 1;
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_assert_fail_in_block(x: &mut u64) {
            let mut i = 0;

            #[verifier::loop_isolation_boundary]
            {
                assert(false); // FAILS
                while i < 10 {
                    i = i + 1;
                }
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] param_not_equal_to_old verus_code! {
        #[verifier::exec_allows_no_decreases_clause]
        fn test_param_havoced(x: &mut u64) {
            let mut i = 0;
            *x = 2;

            #[verifier::loop_isolation_boundary]
            {
                while i < 10 {
                    assert(*x == *old(x)); // FAILS
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_param_havoced2(x: &mut u64) {
            let mut i = 0;

            #[verifier::loop_isolation_boundary]
            {
                *x = 2;
                while i < 10 {
                    assert(*x == *old(x)); // FAILS
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_param_havoced3(x: &mut u64) {
            let mut i = 0;

            #[verifier::loop_isolation_boundary]
            {
                while i < 10 {
                    assert(*x == *old(x)); // FAILS
                    *x = 2;
                }
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] closure_param_not_equal_to_old verus_code! {
        #[verifier::exec_allows_no_decreases_clause]
        fn test_param_havoced() {
            let clos = |x: &mut u64| {
                let mut i = 0;
                *x = 2;

                #[verifier::loop_isolation_boundary]
                {
                    while i < 10 {
                        assert(*x == *old(x)); // FAILS
                    }
                }
            };
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_param_havoced2() {
            let clos = |x: &mut u64| {
                let mut i = 0;

                #[verifier::loop_isolation_boundary]
                {
                    *x = 2;
                    while i < 10 {
                        assert(*x == *old(x)); // FAILS
                    }
                }
            };
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_param_havoced3() {
            let clos = |x: &mut u64| {
                let mut i = 0;

                #[verifier::loop_isolation_boundary]
                {
                    while i < 10 {
                        assert(*x == *old(x)); // FAILS
                        *x = 2;
                    }
                }
            };
        }
    } => Err(err) => assert_fails(err, 3)
}
