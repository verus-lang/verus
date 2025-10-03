#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_let_else_returns verus_code! {
        enum X {
            A(usize),
            B(bool),
        }
        spec fn is_a(x: X) -> bool {
            match x {
                X::A(..) => {
                    true
                }
                _ => {
                    false
                }
            }
        }
        fn f(x: X) -> (ret: bool)
        ensures is_a(x) == ret
        {
            let X::A(a) = x else {
                let x: bool = false;
                return x;
            };
            return true;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_let_else_ensures_failed_no_unwind_condition2 verus_code! {
        enum X {
            A(usize),
            B(bool),
        }
        #[verifier(external_body)]
        fn call_panic() -> ! {
            panic!();
        }
        spec fn is_a(x: X) -> bool {
            if let X::A(..) = x {
                true
            } else {
                false
            }
        }
        fn f(x: X) -> (ret: bool)
        ensures is_a(x) == ret
        {
            let X::A(a) = x else {
                return true; // FAILS
            };
            return true;
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_let_else_dots verus_code! {
        struct A {
            x: usize,
            y: bool,
            z: i32,
        }
        enum X {
            U(usize),
            B(bool),
            A(A, usize, bool),
        }
        #[verifier(external_body)]
        fn call_panic() -> ! {
            panic!();
        }
        spec fn is_a(x: X) -> bool {
            if let X::A(..) = x {
                true
            } else {
                false
            }
        }
        spec fn check_x_b(x: X, val1: usize, val2: bool) -> bool {
            match x {
                X::A(A{x, ..}, ..,b) => {
                    x == val1 && b == val2
                }
                _ => {
                    false
                }
            }
        }
        fn f(x: X) -> (ret: (usize, bool))
        ensures check_x_b(x, ret.0, ret.1)
        no_unwind when is_a(x)
        {
            let X::A(A {x, ..}, .., b) = x else {
                call_panic();
            };
            (x, b)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] let_else_not_supported_in_proof verus_code! {
        enum X {
            A(usize),
            B(bool),
        }
        proof fn stuff(x: X) -> usize {
            let X::A(y) = x else {
                return 0;
            };
            y
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: let-else in spec/proof")
}

test_verify_one_file! {
    #[test] let_else_not_supported_in_spec verus_code! {
        enum X {
            A(usize),
            B(bool),
        }
        spec fn stuff(x: X) -> usize {
            let X::A(y) = x else {
                return 0;
            };
            y
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: let-else in spec/proof")
}

test_verify_one_file! {
    #[test] let_else_verus_parse_else verus_code! {
        enum X {
            A(usize),
            B(bool),
        }
        fn stuff(x: X) -> usize {
            let X::A(y) = x else {
                assert(false); // FAILS
                return 0;
            };
            y
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] let_else_just_a_normal_var verus_code! {
        #[verifier::exec_allows_no_decreases_clause]
        #[allow(irrefutable_let_patterns)]
        fn test(x: u64) {
            let y = x else {
                assert(false);
                loop { }
            };

            assert(y == x);
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(irrefutable_let_patterns)]
        fn test_fails(x: u64) {
            let y = x else {
                loop { }
            };

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
