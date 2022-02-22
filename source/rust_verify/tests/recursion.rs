#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] basic_correctness_expr code! {
        #[spec]
        fn arith_sum_nat(i: nat) -> nat {
            decreases(i);

            if i == 0 { 0 } else { i + arith_sum_nat(i - 1) }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_correctness_expr_fail code! {
        #[spec]
        fn arith_sum_nat(i: nat) -> nat {
            if i == 0 { 0 } else { i + arith_sum_nat(i - 1) }
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] basic_correctness_stmt code! {
        #[proof]
        fn count_down_stmt(i: nat) {
            decreases(i);

            if i != 0 {
                count_down_stmt(i - 1);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_correctness_stmt_fail code! {
        #[proof]
        fn count_down_stmt(i: nat) {
            if i != 0 {
                count_down_stmt(i - 1);
            }
        }
    } => Err(_)
}

test_verify_one_file! {
    // Basic test of mutually recursive expressions
    #[test] mutually_recursive_expressions code! {
        #[spec]
        fn count_down_a(i: nat) -> nat {
            decreases(i);

            if i == 0 { 0 } else { 1 + count_down_b(i - 1) }
        }

        #[spec]
        fn count_down_b(i: nat) -> nat {
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

test_verify_one_file! {
    // Basic test of mutually recursive expressions
    #[test] mutually_recursive_expressions_j code! {
        #[spec]
        fn count_down_a(i: nat) -> nat {
            decreases(i);

            if i == 0 { 0 } else { 1 + count_down_b(i - 1) }
        }

        #[spec]
        fn count_down_b(j: nat) -> nat {
            decreases(j);

            if j == 0 { 0 } else { 1 + count_down_a(j - 1) }
        }

        #[proof]
        fn count_down_properties() {
            assert(count_down_b(0) == 0);
            assert(count_down_a(1) == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    // Test that fuel only provides one definition unfolding
    #[test] mutually_recursive_expressions_insufficient_fuel code! {
        #[spec]
        fn count_down_a(i: nat) -> nat {
            decreases(i);

            if i == 0 { 0 } else { 1 + count_down_b(i - 1) }
        }

        #[spec]
        fn count_down_b(i: nat) -> nat {
            decreases(i);

            if i == 0 { 0 } else { 1 + count_down_a(i - 1) }
        }

        #[proof]
        fn count_down_properties() {
            assert(count_down_a(1) == 1);   // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Test that fuel only provides one definition unfolding
    #[test] mutually_recursive_expressions_insufficient_fuel_j code! {
        #[spec]
        fn count_down_a(i: nat) -> nat {
            decreases(i);

            if i == 0 { 0 } else { 1 + count_down_b(i - 1) }
        }

        #[spec]
        fn count_down_b(j: nat) -> nat {
            decreases(j);

            if j == 0 { 0 } else { 1 + count_down_a(j - 1) }
        }

        #[proof]
        fn count_down_properties() {
            assert(count_down_a(1) == 1);   // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Basic test of mutually recursive statements
    #[test] mutually_recursive_statements code! {
        #[proof]
        fn count_down_a_stmt(i: nat) {
            decreases(i);

            if i != 0 {
                count_down_b_stmt(i - 1);
            }
        }

        #[proof]
        fn count_down_b_stmt(i: nat) {
            decreases(i);

            if i != 0 {
                count_down_a_stmt(i - 1);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Basic test of mutually recursive statements
    #[test] mutually_recursive_statements_j code! {
        #[proof]
        fn count_down_a_stmt(i: nat) {
            decreases(i);

            if i != 0 {
                count_down_b_stmt(i - 1);
            }
        }

        #[proof]
        fn count_down_b_stmt(j: nat) {
            decreases(j);

            if j != 0 {
                count_down_a_stmt(j - 1);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Expression that fails to decrease
    #[test] expr_decrease_fail_1 code! {
        #[spec]
        fn arith_sum_int(i: int) -> int {
            decreases(i);

            if i <= 0 { 0 } else { i + arith_sum_int(i + 1) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Statement that fails to decrease
    #[test] stmt_decrease_fail code! {
        #[proof]
        fn count_down_stmt(i: nat) {
            decreases(i);

            if i != 0 {
                count_down_stmt(i + 1); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Expression that decreases, but not based on the decreases clause provided
    #[test] expr_wrong_decreases code! {
        #[spec]
        fn arith_sum_int(i: int) -> int {
            decreases(100 - i);

            if i <= 0 { 0 } else { i + arith_sum_int(i - 1) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Expression that decreases, but not based on the decreases clause provided
    #[test] expr_wrong_decreases_2 code! {
        #[spec]
        fn arith_sum_int(x: nat, i: int) -> int {
            decreases(x);

            if i <= 0 { 0 } else { i + arith_sum_int(x, i - 1) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Expression that decreases, but not based on the decreases clause provided
    #[test] expr_wrong_decreases_3 code! {
        #[spec]
        fn arith_sum_int(i: int) -> int {
            decreases(5);

            if i <= 0 { 0 } else { i + arith_sum_int(4) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Expression that doesn't decrease due to extra clause
    #[test] expr_decrease_fail_2 code! {
        #[spec]
        fn arith_sum_int(x: nat, y: nat, i: int) -> int {
            decreases(i);

            if i <= 0 && x < y { 0 } else { i + arith_sum_int(x, y, i - 1) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Expression that fails to decrease
    #[test] expr_decrease_fail_3 code! {
        #[spec]
        fn arith_sum_int(i: int) -> int {
            decreases(i);

            if i <= 0 { 0 } else { i + arith_sum_int(i) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Mutually recursive expressions fail to decrease
    #[test] mutual_expr_decrease_fail code! {
        #[spec]
        fn count_down_a(i: nat) -> nat {
            decreases(i);

            if i == 0 { 0 } else { 1 + count_down_b(i - 1) }  // FAILS
        }

        #[spec]
        fn count_down_b(i: nat) -> nat {
            decreases(5 - i);

            if i >= 5 { 0 } else { 1 + count_down_a(i + 1) }  // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    // Mutually recursive statements fail to decrease
    #[test] mutual_stmt_decrease_fail code! {
        #[proof]
        fn count_down_a_stmt(i: nat) {
            decreases(i);

            if i != 0 {
                count_down_b_stmt(i + 1);   // FAILS
            }
        }

        #[proof]
        fn count_down_b_stmt(i: nat) {
            decreases(i);

            if i != 0 {
                count_down_a_stmt(i + 1);   // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] mutual_stmt_decrease2 code! {
        #[proof]
        fn f(x: nat) {
            decreases(2 * x);
            if x > 0 {
                g(x - 1, x - 1);
            }
        }

        #[proof]
        fn g(y: nat, z: nat) {
            decreases(y + z);
            if y > 0 && z > 0 {
                f((y + z) / 2 - 1);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Mutually recursive statements fail to decrease
    #[test] mutual_stmt_decrease_fail2 code! {
        #[proof]
        fn f(x: nat) {
            decreases(2 * x);
            g(x + 1, x + 2); // FAILS
        }

        #[proof]
        fn g(y: nat, z: nat) {
            decreases(y * z);
            f(y + z); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] unit_expr_decrease_fail code! {
        #[spec]
        fn count_down_tricky(i: nat) {
            decreases(i);

            if i != 0 {
                count_down_tricky(i + 1) // FAILS
            } else {
                ()
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] multidecrease1 code! {
        #[proof]
        fn dec1(i: nat) {
            decreases(i);
            if 0 < i {
                dec1(i - 1);
                dec2(i, 100 * i);
            }
        }

        #[proof]
        fn dec2(j: nat, k: nat) {
            decreases((j, k));
            if 0 < k {
                dec2(j, k - 1);
            }
            if 0 < j {
                dec2(j - 1, 100 * j + k);
                dec1(j - 1);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] multidecrease1_fail1 code! {
        #[proof]
        fn dec1(i: nat) {
            decreases(i);
            if 0 < i {
                dec1(i); // FAILS
                dec2(i, 100 * i);
            }
        }

        #[proof]
        fn dec2(j: nat, k: nat) {
            decreases((j, k));
            if 0 < k {
                dec2(j, k); // FAILS
            }
            if 0 < j {
                dec2(j - 1, 100 * j + k);
                dec1(j - 1);
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] multidecrease1_fail2 code! {
        #[proof]
        fn dec1(i: nat) {
            decreases(i);
            if 0 < i {
                dec1(i - 1);
                dec2(i + 1, 100 * i); // FAILS
            }
        }

        #[proof]
        fn dec2(j: nat, k: nat) {
            decreases((j, k));
            if 0 < k {
                dec2(j, k - 1);
            }
            if 0 < j {
                dec2(j, 100 * j + k); // FAILS
                dec1(j - 1);
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] multidecrease1_fail3 code! {
        #[proof]
        fn dec1(i: nat) {
            decreases(i);
            if 0 < i {
                dec1(i - 1);
                dec2(i, 100 * i);
            }
        }

        #[proof]
        fn dec2(j: nat, k: nat) {
            decreases((j, k));
            if 0 < k {
                dec2(j, k - 1);
            }
            if 0 < j {
                dec2(j - 1, 100 * j + k);
                dec1(j); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] multidecrease1_fail4 code! {
        #[proof]
        fn dec1(i: nat) {
            if 0 < i {
                dec2(i, 100 * i); // FAILS
            }
        }

        #[proof]
        fn dec2(j: nat, k: nat) {
            decreases((j, k));
            if 0 < k {
                dec2(j, k - 1);
            }
            if 0 < j {
                dec2(j - 1, 100 * j + k);
                dec1(j - 1);
            }
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] multidecrease1_fail5 code! {
        #[proof]
        fn dec1(i: nat) {
            decreases(i);
            if 0 < i {
                dec1(i - 1);
                dec2(i, 100 * i); // FAILS
            }
        }

        #[proof]
        fn dec2(j: nat, k: nat) {
            if 0 < j {
                dec1(j - 1);
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] extra_dep_fail code! {
        // We expect this to complain about the lack of 'decreases' clause

        #[proof]
        fn dec1(i: nat) {
            dec2(i);
        }

        #[proof]
        #[verifier(external_body)]
        fn dec2(i: nat) {
            extra_dependency(dec1);
            unimplemented!();
        }
    } => Err(err) => assert_vir_error(err)
}
