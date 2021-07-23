#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_with_pervasive! {
    #[test] basic_correctness_expr code! {
        #[spec]
        fn arith_sum_nat(i: nat) -> nat {
            decreases(i);

            if i == 0 { 0 } else { i + arith_sum_nat(i - 1) }
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] basic_correctness_stmt code! {
        #[proof]
        fn count_down_stmt(i:nat) {
            decreases(i);

            if i != 0 {
                count_down_stmt(i - 1);
            }
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    // Basic test of mutually recursive expressions
    #[test] mutually_recursive_expressions code! {
        #[spec]
        fn count_down_a(i:nat) -> nat {
            decreases(i);

            if i == 0 { 0 } else { 1 + count_down_b(i - 1) }
        }

        #[spec]
        fn count_down_b(i:nat) -> nat {
            decreases(i);

            if i == 0 { 0 } else { 1 + count_down_a(i - 1) }
        }

        #[proof]
        fn count_down_properties() {
            assert(count_down_b(0) == 0);
            assert(count_down_a(1) == 1);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    // Test that fuel only provides one definition unfolding
    #[test] mutually_recursive_expressions_insufficient_fuel code! {
        #[spec]
        fn count_down_a(i:nat) -> nat {
            decreases(i);

            if i == 0 { 0 } else { 1 + count_down_b(i - 1) }
        }

        #[spec]
        fn count_down_b(i:nat) -> nat {
            decreases(i);

            if i == 0 { 0 } else { 1 + count_down_a(i - 1) }
        }

        #[proof]
        fn count_down_properties() {
            assert(count_down_a(1) == 1);   // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    // Basic test of mutually recursive statements
    #[test] mutually_recursive_statements code! {
        #[proof]
        fn count_down_a_stmt(i:nat) {
            decreases(i);

            if i != 0 {
                count_down_b_stmt(i - 1);
            }
        }

        #[proof]
        fn count_down_b_stmt(i:nat) {
            decreases(i);

            if i != 0 {
                count_down_a_stmt(i - 1);
            }
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    // Expression that fails to decrease
    #[test] expr_decrease_fail_1 code! {
        #[spec]
        fn arith_sum_int(i: int) -> int {
            decreases(i);

            if i <= 0 { 0 } else { i + arith_sum_int(i + 1) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    // Statement that fails to decrease
    #[test] stmt_decrease_fail code! {
        #[proof]
        fn count_down_stmt(i:nat) {
            decreases(i);

            if i != 0 {
                count_down_stmt(i + 1); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    // Expression that decreases, but not based on the decreases clause provided
    #[test] expr_wrong_decreases code! {
        #[spec]
        fn arith_sum_int(i: int) -> int {
            decreases(100 - i);

            if i <= 0 { 0 } else { i + arith_sum_int(i - 1) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    // Expression that decreases, but not based on the decreases clause provided
    #[test] expr_wrong_decreases_2 code! {
        #[spec]
        fn arith_sum_int(x:nat, i: int) -> int {
            decreases(x);

            if i <= 0 { 0 } else { i + arith_sum_int(x, i - 1) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    // Expression that decreases, but not based on the decreases clause provided
    #[test] expr_wrong_decreases_3 code! {
        #[spec]
        fn arith_sum_int(i: int) -> int {
            decreases(5);

            if i <= 0 { 0 } else { i + arith_sum_int(4) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    // Expression that doesn't decrease due to extra clause
    #[test] expr_decrease_fail_2 code! {
        #[spec]
        fn arith_sum_int(x:nat, y:nat, i: int) -> int {
            decreases(i);

            if i <= 0 && x < y { 0 } else { i + arith_sum_int(x, y, i - 1) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    // Expression that fails to decrease
    #[test] expr_decrease_fail_3 code! {
        #[spec]
        fn arith_sum_int(i: int) -> int {
            decreases(i);

            if i <= 0 { 0 } else { i + arith_sum_int(i) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    // Mutually recursive expressions fail to decrease
    #[test] mutual_expr_decrease_fail code! {
        #[spec]
        fn count_down_a(i:nat) -> nat {
            decreases(i);

            if i == 0 { 0 } else { 1 + count_down_b(i - 1) }  // FAILS
        }

        #[spec]
        fn count_down_b(i:nat) -> nat {
            decreases(5 - i);

            if i >= 5 { 0 } else { 1 + count_down_a(i + 1) }  // FAILS
        }
    } => Err(err) => assert_two_fails(err)
}

test_verify_with_pervasive! {
    // Mutually recursive statements fail to decrease
    #[test] mutual_stmt_decrease_fail code! {
        #[proof]
        fn count_down_a_stmt(i:nat) {
            decreases(i);

            if i != 0 {
                count_down_b_stmt(i + 1);   // FAILS
            }
        }

        #[proof]
        fn count_down_b_stmt(i:nat) {
            decreases(i);

            if i != 0 {
                count_down_a_stmt(i + 1);   // FAILS
            }
        }
    } => Err(err) => assert_two_fails(err)
}

// TODO: Expression that fails to decrease in a function returning unit
/*
test_verify_with_pervasive! {
    #[test] unit_expr_decrease_fail code! {
        #[spec]
        fn count_down_tricky(i:nat) {
            decreases(i);

            if i != 0 {
                count_down_tricky(i + 1)
            }
        }
    } => Err(err) => assert_one_fails(err)
}
*/
