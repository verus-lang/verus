#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] basic verus_code! {
        fn test_labelled_block(cond: bool) {
            let mut x = 0;
            'a: {
                assert(x == 0);
                x = 7;
                if cond {
                    break 'a;
                }
                x = 5;
            }

            assert(x == if cond { 7u64 } else { 5u64 });
        }

        fn fail1(cond: bool) {
            let mut x = 0;
            'a: {
                assert(x == 0);
                x = 7;
                if cond {
                    break 'a;
                }
                x = 5;
            }

            assert(cond); // FAILS
        }

        fn fail2(cond: bool) {
            let mut x = 0;
            'a: {
                assert(x == 0);
                x = 7;
                if cond {
                    break 'a;
                }
                x = 5;
            }

            assert(!cond); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] with_value verus_code! {
        fn test_labelled_block_value(cond: bool) {
            let x = 'a: {
                if cond {
                    break 'a 27;
                }
                33
            };

            assert(x == if cond { 27u64 } else { 33u64 });
        }

        fn fails1(cond: bool) {
            let x = 'a: {
                if cond {
                    break 'a 27;
                }
                33
            };

            assert(cond); // FAILS
        }

        fn fails2(cond: bool) {
            let x = 'a: {
                if cond {
                    break 'a 27;
                }
                33
            };

            assert(!cond); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] in_proof_block verus_code! {
        fn test() {
            proof {
                'a: {
                    break 'a;
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use breakable block in proof or spec mode")
}

test_verify_one_file! {
    #[test] in_proof_block_break verus_code! {
        #[allow(unreachable_code)]
        fn test() {
            'a: {
                proof {
                    break 'a;
                    ()
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "break/continue is not allowed outside executable context")
}

test_verify_one_file! {
    #[test] with_loop verus_code! {
        fn rand() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test(cond: bool) {
            let mut x = 0;
            let y = 'a: {
                if cond {
                    #[verifier::loop_isolation(false)]
                    loop {
                        if rand() {
                            break 'a 20;
                        }
                    }
                } else {
                    30
                }
            };
            assert(y == if cond { 20u32 } else { 30u32 });
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn fails1(cond: bool) {
            let mut x = 0;
            let y = 'a: {
                if cond {
                    #[verifier::loop_isolation(false)]
                    loop {
                        if rand() {
                            break 'a 20;
                        }
                    }
                } else {
                    30
                }
            };
            assert(cond); // FAILS
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn fails2(cond: bool) {
            let mut x = 0;
            let y = 'a: {
                if cond {
                    #[verifier::loop_isolation(false)]
                    loop {
                        if rand() {
                            break 'a 20;
                        }
                    }
                } else {
                    30
                }
            };
            assert(!cond); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] with_loop_iso_true verus_code! {
        fn rand() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test(cond: bool) {
            let mut x = 0;
            let y = 'a: {
                if cond {
                    #[verifier::loop_isolation(true)]
                    loop {
                        if rand() {
                            break 'a 20;
                        }
                    }
                } else {
                    30
                }
            };
            assert(y == if cond { 20u32 } else { 30u32 });
        }
    } => Err(err) => assert_vir_error_msg(err, "breakable block contains 'break' statement inside a nested loop with loop_isolation=true")
}
