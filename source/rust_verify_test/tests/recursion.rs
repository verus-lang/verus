#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] basic_correctness_expr verus_code! {
        spec fn arith_sum_nat(i: nat) -> nat
            decreases i
        {
            if i == 0 { 0 } else { i + arith_sum_nat((i - 1) as nat) }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_correctness_expr_fail verus_code! {
        spec fn arith_sum_nat(i: nat) -> nat {
            if i == 0 { 0 } else { i + arith_sum_nat((i - 1) as nat) }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] basic_correctness_stmt verus_code! {
        proof fn count_down_stmt(i: nat)
            decreases i
        {
            if i != 0 {
                count_down_stmt((i - 1) as nat);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_correctness_stmt_fail verus_code! {
        proof fn count_down_stmt(i: nat) {
            if i != 0 {
                count_down_stmt((i - 1) as nat);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    // Basic test of mutually recursive expressions
    #[test] mutually_recursive_expressions verus_code! {
        spec fn count_down_a(i: nat) -> nat
            decreases i
        {
            if i == 0 { 0 } else { 1 + count_down_b((i - 1) as nat) }
        }

        spec fn count_down_b(i: nat) -> nat
            decreases i
        {
            if i == 0 { 0 } else { 1 + count_down_a((i - 1) as nat) }
        }

        proof fn count_down_properties() {
            assert(count_down_b(0) == 0);
            assert(count_down_a(1) == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    // Basic test of mutually recursive expressions
    #[test] mutually_recursive_expressions_j verus_code! {
        spec fn count_down_a(i: nat) -> nat
            decreases i
        {
            if i == 0 { 0 } else { 1 + count_down_b((i - 1) as nat) }
        }

        spec fn count_down_b(j: nat) -> nat
            decreases j
        {
            if j == 0 { 0 } else { 1 + count_down_a((j - 1) as nat) }
        }

        proof fn count_down_properties() {
            assert(count_down_b(0) == 0);
            assert(count_down_a(1) == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    // Test that default fuel only provides one cycle of unfolding
    #[test] mutually_recursive_expressions_insufficient_fuel verus_code! {
        spec fn count_down_a(i: nat) -> nat
            decreases i
        {
            if i == 0 { 0 } else { 1 + count_down_b((i - 1) as nat) }
        }

        spec fn count_down_b(i: nat) -> nat
            decreases i
        {
            if i == 0 { 0 } else { 1 + count_down_a((i - 1) as nat) }
        }

        proof fn count_down_properties() {
            assert(count_down_a(1) == 1);
        }

        proof fn count_down_properties_fail() {
            assert(count_down_a(2) == 2);   // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Test that default fuel only provides one cycle of unfolding
    #[test] mutually_recursive_expressions_insufficient_fuel_short_cycle verus_code! {
        spec fn count_down_a(i: nat) -> nat
            decreases i
        {
            if i == 0 { 0 } else if i == 100 { 1 + count_down_a((i - 1) as nat) } else { 1 + count_down_b((i - 1) as nat) }
        }

        spec fn count_down_b(i: nat) -> nat
            decreases i
        {
            if i == 0 { 0 } else { 1 + count_down_a((i - 1) as nat) }
        }

        proof fn count_down_properties() {
            reveal_with_fuel(count_down_a, 2);
            assert(count_down_a(1) == 1);
        }

        // Since count_down_a calls itself directly, there is a cycle of length 1
        // from count_down_a to itself, so the default fuel for count_down_a is 1,
        // which is not enough for count_down_a(1) == 1 to succeed.
        proof fn count_down_properties_fail() {
            assert(count_down_a(1) == 1);   // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Test that default fuel only provides one cycle of unfolding
    #[test] mutually_recursive_expressions_insufficient_fuel_j verus_code! {
        spec fn count_down_a(i: nat) -> nat
            decreases i
        {
            if i == 0 { 0 } else { 1 + count_down_b((i - 1) as nat) }
        }

        spec fn count_down_b(j: nat) -> nat
            decreases j
        {
            if j == 0 { 0 } else { 1 + count_down_a((j - 1) as nat) }
        }

        proof fn count_down_properties() {
            assert(count_down_a(1) == 1);
        }

        proof fn count_down_properties_fail() {
            assert(count_down_a(2) == 2);   // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Basic test of mutually recursive statements
    #[test] mutually_recursive_statements verus_code! {
        proof fn count_down_a_stmt(i: nat)
            decreases i
        {
            if i != 0 {
                count_down_b_stmt((i - 1) as nat);
            }
        }

        proof fn count_down_b_stmt(i: nat)
            decreases i
        {
            if i != 0 {
                count_down_a_stmt((i - 1) as nat);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Basic test of mutually recursive statements
    #[test] mutually_recursive_statements_j verus_code! {
        proof fn count_down_a_stmt(i: nat)
            decreases i
        {
            if i != 0 {
                count_down_b_stmt((i - 1) as nat);
            }
        }

        proof fn count_down_b_stmt(j: nat)
            decreases j
        {
            if j != 0 {
                count_down_a_stmt((j - 1) as nat);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Expression that fails to decrease
    #[test] expr_decrease_fail_1 verus_code! {
        spec fn arith_sum_int(i: int) -> int
            decreases i
        {
            if i <= 0 { 0 } else { i + arith_sum_int(i + 1) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Statement that fails to decrease
    #[test] stmt_decrease_fail verus_code! {
        proof fn count_down_stmt(i: nat)
            decreases i
        {
            if i != 0 {
                count_down_stmt(i + 1); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Expression that decreases, but not based on the decreases clause provided
    #[test] expr_wrong_decreases verus_code! {
        spec fn arith_sum_int(i: int) -> int
            decreases 100 - i
        {
            if i <= 0 { 0 } else { i + arith_sum_int(i - 1) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Expression that decreases, but not based on the decreases clause provided
    #[test] expr_wrong_decreases_2 verus_code! {
        spec fn arith_sum_int(x: nat, i: int) -> int
            decreases x
        {
            if i <= 0 { 0 } else { i + arith_sum_int(x, i - 1) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Expression that decreases, but not based on the decreases clause provided
    #[test] expr_wrong_decreases_3 verus_code! {
        spec fn arith_sum_int(i: int) -> int
            decreases 5int
        {
            if i <= 0 { 0 } else { i + arith_sum_int(4) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Expression that doesn't decrease due to extra clause
    #[test] expr_decrease_fail_2 verus_code! {
        spec fn arith_sum_int(x: nat, y: nat, i: int) -> int
            decreases i
        {
            if i <= 0 && x < y { 0 } else { i + arith_sum_int(x, y, i - 1) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Expression that fails to decrease
    #[test] expr_decrease_fail_3 verus_code! {
        spec fn arith_sum_int(i: int) -> int
            decreases i
        {
            if i <= 0 { 0 } else { i + arith_sum_int(i) }  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Mutually recursive expressions fail to decrease
    #[test] mutual_expr_decrease_fail verus_code! {
        spec fn count_down_a(i: nat) -> nat
            decreases i
        {
            if i == 0 { 0 } else { 1 + count_down_b((i - 1) as nat) }  // FAILS
        }

        spec fn count_down_b(i: nat) -> nat
            decreases 5 - i
        {
            if i >= 5 { 0 } else { 1 + count_down_a(i + 1) }  // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    // Mutually recursive statements fail to decrease
    #[test] mutual_stmt_decrease_fail verus_code! {
        proof fn count_down_a_stmt(i: nat)
            decreases i
        {
            if i != 0 {
                count_down_b_stmt(i + 1);   // FAILS
            }
        }

        proof fn count_down_b_stmt(i: nat)
            decreases i
        {
            if i != 0 {
                count_down_a_stmt(i + 1);   // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] mutual_stmt_decrease2 verus_code! {
        proof fn f(x: nat)
            decreases 2 * x
        {
            if x > 0 {
                g((x - 1) as nat, (x - 1) as nat);
            }
        }

        proof fn g(y: nat, z: nat)
            decreases y + z
        {
            if y > 0 && z > 0 {
                f(((y + z) / 2 - 1) as nat);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Mutually recursive statements fail to decrease
    #[test] mutual_stmt_decrease_fail2 verus_code! {
        proof fn f(x: nat)
            decreases 2 * x
        {
            g(x + 1, x + 2); // FAILS
        }

        proof fn g(y: nat, z: nat)
            decreases y * z
        {
            f(y + z); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] unit_expr_decrease_fail verus_code! {
        spec fn count_down_tricky(i: nat)
            decreases i
        {
            if i != 0 {
                count_down_tricky(i + 1) // FAILS
            } else {
                ()
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] multidecrease1 verus_code! {
        proof fn dec1(i: nat)
            decreases i
        {
            if 0 < i {
                assert(decreases_to!(i => i - 1));
                dec1((i - 1) as nat);
                assert(decreases_to!(i => i, 100 * i));
                dec2(i, 100 * i);
            }
        }

        proof fn dec2(j: nat, k: nat)
            decreases j, k
        {
            if 0 < k {
                assert(decreases_to!(j, k => j, k - 1));
                dec2(j, (k - 1) as nat);
            }
            if 0 < j {
                assert(decreases_to!(j, k => j - 1, 100 * j + k));
                dec2((j - 1) as nat, 100 * j + k);
                assert(decreases_to!(j, k => j - 1));
                dec1((j - 1) as nat);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] multidecrease1_fail1 verus_code! {
        proof fn dec1(i: nat)
            decreases i
        {
            if 0 < i {
                dec1(i); // FAILS
                dec2(i, 100 * i);
            }
        }

        proof fn dec2(j: nat, k: nat)
            decreases j, k
        {
            if 0 < k {
                dec2(j, k); // FAILS
            }
            if 0 < j {
                dec2((j - 1) as nat, 100 * j + k);
                dec1((j - 1) as nat);
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] multidecrease1_fail1_assert verus_code! {
        proof fn dec1(i: nat)
            decreases i
        {
            if 0 < i {
                let tmp = decreases_to!(i => i);
                assert(tmp); // FAILS
                dec2(i, 100 * i);
            }
        }

        proof fn dec2(j: nat, k: nat)
            decreases j, k
        {
            if 0 < k {
                let tmp = decreases_to!(j, k => j, k);
                assert(tmp); // FAILS
            }
            if 0 < j {
                dec2((j - 1) as nat, 100 * j + k);
                dec1((j - 1) as nat);
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] multidecrease1_fail2 verus_code! {
        proof fn dec1(i: nat)
            decreases i
        {
            if 0 < i {
                dec1((i - 1) as nat);
                dec2(i + 1, 100 * i); // FAILS
            }
        }

        proof fn dec2(j: nat, k: nat)
            decreases j, k
        {
            if 0 < k {
                dec2(j, (k - 1) as nat);
            }
            if 0 < j {
                dec2(j, 100 * j + k); // FAILS
                dec1((j - 1) as nat);
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] multidecrease1_fail2_assert verus_code! {
        proof fn dec1(i: nat)
            decreases i
        {
            if 0 < i {
                dec1((i - 1) as nat);
                let tmp = decreases_to!(i => i + 1, 100 * i);
                assert(tmp); // FAILS
            }
        }

        proof fn dec2(j: nat, k: nat)
            decreases j, k
        {
            if 0 < k {
                dec2(j, (k - 1) as nat);
            }
            if 0 < j {
                let tmp = decreases_to!(j, k => j, 100 * j + k);
                assert(tmp); // FAILS
                dec1((j - 1) as nat);
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] multidecrease1_fail3 verus_code! {
        proof fn dec1(i: nat)
            decreases i
        {
            if 0 < i {
                dec1((i - 1) as nat);
                dec2(i, 100 * i);
            }
        }

        proof fn dec2(j: nat, k: nat)
            decreases j, k
        {
            if 0 < k {
                dec2(j, (k - 1) as nat);
            }
            if 0 < j {
                dec2((j - 1) as nat, 100 * j + k);
                dec1(j); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] multidecrease1_fail3_assert verus_code! {
        proof fn dec1(i: nat)
            decreases i
        {
            if 0 < i {
                dec1((i - 1) as nat);
                dec2(i, 100 * i);
            }
        }

        proof fn dec2(j: nat, k: nat)
            decreases j, k
        {
            if 0 < k {
                dec2(j, (k - 1) as nat);
            }
            if 0 < j {
                dec2((j - 1) as nat, 100 * j + k);
                let tmp = decreases_to!(j, k => j);
                assert(tmp); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] multidecrease1_fail4 verus_code! {
        proof fn dec1(i: nat) {
            if 0 < i {
                dec2(i, 100 * i); // FAILS
            }
        }

        proof fn dec2(j: nat, k: nat)
            decreases j, k
        {
            if 0 < k {
                dec2(j, (k - 1) as nat);
            }
            if 0 < j {
                dec2((j - 1) as nat, 100 * j + k);
                dec1((j - 1) as nat);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] multidecrease1_fail5 verus_code! {
        proof fn dec1(i: nat)
            decreases i
        {
            if 0 < i {
                dec1((i - 1) as nat);
                dec2(i, 100 * i); // FAILS
            }
        }

        proof fn dec2(j: nat, k: nat) {
            if 0 < j {
                dec1((j - 1) as nat);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] extra_dep_fail verus_code! {
        // We expect this to complain about the lack of 'decreases' clause

        proof fn dec1(i: nat) {
            dec2(i);
        }

        #[verifier(external_body)]
        proof fn dec2(i: nat) {
            extra_dependency(dec1);
            unimplemented!();
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] termination_checked_before_definition1 verus_code! {
        spec fn f(i: int) -> int
            decreases f(0) + i
        {
            f(i) + 1 // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] termination_checked_before_definition2 verus_code! {
        spec fn f(i: int) -> int
            decreases g(0) + i
        {
            g(i) + 1 // FAILS
        }

        spec fn g(i: int) -> int
            decreases f(0) + i
        {
            f(i) + 1 // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] termination_checked_before_definition3 verus_code! {
        spec fn f(i: int) -> int
            decreases g(0) + h(0) + i
        {
            g(i) + 1 // FAILS
        }

        spec fn g(i: int) -> int
            decreases f(0) + h(0) + i
        {
            f(i) + 1 // FAILS
        }

        spec fn h(i: int) -> int
            decreases f(0) + i
        {
            h(i) + 1 // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] termination_checked_before_definition4 verus_code! {
        spec fn f(i: int) -> int
            decreases i
        {
            if i > 0 { 2 + f(g(i - 1)) } else { 0 }
        }

        spec fn g(i: int) -> int {
            i
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] termination_checked_across_modules verus_code! {
        // We expect this to complain about the lack of 'decreases' clause
        mod M1 {
            use builtin::*;
            pub(crate) closed spec fn f1(i: int) -> int { crate::M2::f2(i - 1) }
        }
        mod M2 {
            use builtin::*;
            pub(crate) closed spec fn f2(i: int) -> int { crate::M1::f1(i - 1) }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] termination_checked_across_modules2 verus_code! {
        mod M1 {
            use builtin::*;
            pub(crate) closed spec fn f1(i: int) -> int
                decreases i
            {
                crate::M2::f2(i - 1) // FAILS
            }
        }
        mod M2 {
            use builtin::*;
            pub(crate) closed spec fn f2(i: int) -> int
                decreases i
            {
                crate::M1::f1(i - 1) // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] basic_decreases_by verus_code! {
        spec fn arith_sum_nat(i: nat) -> nat
            decreases i
        {
            decreases_by(check_arith_sum_nat);

            if i == 0 { 0 } else { i + arith_sum_nat((i - 1) as nat) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum_nat(i: nat) {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_decreases_by_int verus_code! {
        spec fn arith_sum(i: int) -> int
            decreases i
        {
            decreases_when(i >= 0);
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(i: int) {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail1 verus_code! {
        spec fn arith_sum(i: int) -> int
            decreases i
        {
            if i == 0 { 0 } else { i + arith_sum(i - 1) } // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail2 verus_code! {
        spec fn arith_sum(i: int) -> int
            decreases i
        {
            decreases_when(i >= 0);
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(i: int) {
        }

        proof fn ignore_require(i: int) {
            assert(arith_sum(i) == (if i == 0 { 0 } else { i + arith_sum(i - 1) })); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail3 verus_code! {
        spec fn arith_sum(i: int) -> int
            decreases i
        {
            decreases_when(i >= 0);
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        //#[verifier(decreases_by)]
        proof fn check_arith_sum(i: int) {
        }
    } => Err(err) => assert_vir_error_msg(err, "proof function must be marked #[verifier::decreases_by] or #[verifier::recommends_by] to be used as decreases_by/recommends_by")
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail4 verus_code! {
        spec fn arith_sum(i: int) -> int
            decreases i
        {
            decreases_when(i >= 0);
            //decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(i: int) {
        }
    } => Err(err) => assert_vir_error_msg(err, "unless it is used in some decreases_by/recommends_by")
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail5 verus_code! {
        spec fn arith_sum(i: int) -> int
            decreases i
        {
            decreases_when(i >= 0);
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(i: int)
            decreases i
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function cannot have its own decreases clause")
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail6_requires verus_code! {
        spec fn arith_sum(i: int) -> int
            decreases i
        {
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(i: int)
            requires i >= 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function cannot have requires clauses")
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail6_ensures verus_code! {
        spec fn arith_sum(i: int) -> int
            decreases i
        {
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(i: int)
            ensures i >= 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function cannot have ensures clauses")
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail7 verus_code! {
        spec fn arith_sum(i: int) -> int
            decreases i
        {
            decreases_when(i >= 0);
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(i: nat) {
        }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same parameters")
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail8 verus_code! {
        spec fn arith_sum(i: int) -> int
            decreases i
        {
            decreases_when(i >= 0);
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(j: int) {
        }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same parameters")
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail9 verus_code! {
        spec fn arith_sum<A, B>(a: A, b: B, i: int) -> int
            decreases i
        {
            decreases_when(i >= 0);
            decreases_by(check_arith_sum::<int, int>);

            if i == 0 { 0 } else { i + arith_sum(a, b, i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum<B, A>(a: A, b: B, i: int) {
        }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same type bounds")
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail10 verus_code! {
        spec fn arith_sum(i: int) -> int
            decreases i
        {
            decreases_when(i >= 0);
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(i: int) {
            if false {
                check_arith_sum(i);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call a decreases_by/recommends_by function directly")
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail11 verus_code! {
        spec fn arith_sum(i: int) -> int
            decreases i
        {
            decreases_when(i >= 0);
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(i: int) {
        }

        proof fn test() {
            check_arith_sum(0);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call a decreases_by/recommends_by function directly")
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail12 verus_code! {
        spec fn f(x: int) -> int
            decreases x
        {
            decreases_by(check_f);
            f(x + 1) + 1
        }

        proof fn test()
            ensures f(3) == f(4) + 1
        {
        }

        #[verifier(decreases_by)]
        proof fn check_f(x: int) {
            test();
        }
    } => Err(err) => assert_vir_error_msg(err, "found cyclic dependency in decreases_by function")
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail13 verus_code! {
        spec fn f(x: int) -> int
            decreases x
        {
            decreases_by(check_f);
            3
        }

        #[verifier(decreases_by)]
        proof fn check_f(x: int) {
            let foo = f(x); // cyclic dependency on f
        }
    } => Err(err) => assert_vir_error_msg(err, "found cyclic dependency in decreases_by function")
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail14 verus_code! {
        proof fn arith_sum(i: int) -> int
            decreases i
        {
            decreases_when(i >= 0);
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(i: int) {
        }
    } => Err(err) => assert_vir_error_msg(err, "only spec functions can use decreases_by/recommends_by")
}

test_verify_one_file! {
    #[test] basic_decreases_by_int_fail15 verus_code! {
        spec fn arith_sum(i: int) -> int
            decreases i
        {
            decreases_by(check_arith_sum);

            3
        }

        #[verifier(decreases_by)]
        spec fn check_arith_sum(i: int) {
        }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function must have mode proof")
}

test_verify_one_file! {
    #[test] proof_decreases_by_int verus_code! {
        #[verifier(opaque)]
        spec fn id(i: int) -> int {
            i
        }

        spec fn arith_sum(i: int) -> int
            decreases id(i)
        {
            decreases_when(i >= 0);
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(i: int) {
            reveal(id);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] proof_decreases_by_int2 verus_code! {
        #[verifier(opaque)]
        spec fn id(i: int) -> int {
            i
        }

        spec fn arith_sum(i: int) -> int
            decreases id(i)
        {
            decreases_when(i >= 0);
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) }
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(i: int) {
            reveal_id(i);
            reveal_id(i - 1);
        }

        proof fn reveal_id(i: int)
            ensures id(i) == i
        {
            reveal(id);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] proof_decreases_by_int_fail verus_code! {
        #[verifier(opaque)]
        spec fn id(i: int) -> int {
            i
        }

        spec fn arith_sum(i: int) -> int
            decreases id(i)
        {
            decreases_when(i >= 0);
            decreases_by(check_arith_sum);

            if i == 0 { 0 } else { i + arith_sum(i - 1) } // FAILS
        }

        #[verifier(decreases_by)]
        proof fn check_arith_sum(i: int) {
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] proof_decreases_by_self_1_pass verus_code! {
        tracked struct A { i: int }

        impl A {
            spec fn count(self) -> int
                decreases self.i
            {
                decreases_when(self.i >= 0);
                decreases_by(Self::check_count);

                if self.i == 0 { 0 } else { 1 + A { i: self.i - 1}.count() } // FAILS
            }

            #[verifier(decreases_by)]
            proof fn check_count(self) {
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] proof_decreases_when_ok verus_code! {
        spec fn f(i: int) -> int
            decreases i
        {
            decreases_when(i >= 0);

            if i == 0 {
                0
            } else {
                i + f(i - 1)
            }
        }

        proof fn test() {
            assert(f(0) == 0);
            assert(f(1) == 1);
            assert(f(2) == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] proof_decreases_when_fail verus_code! {
        spec fn f(i: int) -> int
            decreases i
        {
            decreases_when(i >= 0);

            if i == 0 {
                0
            } else {
                i + f(i - 1)
            }
        }

        proof fn test() {
            assert(f(0) == 0);
            assert(f(1) == 1);
            assert(f(2) == 3);
            assert(f(-1) == (-1) + f(-2)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] proof_decreases_when_fail2_ok ["-V allow-inline-air"] => verus_code! {
        spec fn f(x: u8, y: int) -> int decreases y {
            if x == 300 {
                f(x, y) + 1
            } else {
                7
            }
        }

        proof fn good() {
            inline_air_stmt("(assert (= (f.? (I 200) (I 3)) (Add (f.? (I 200) (I 3)) 0)))");
            inline_air_stmt("(assume (= (f.? (I 200) (I 3)) (Add (f.? (I 200) (I 3)) 0)))");
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] proof_decreases_when_fail2 ["-V allow-inline-air"] => verus_code! {
        spec fn f(x: u8, y: int) -> int decreases y {
            if x == 300 {
                f(x, y) + 1
            } else {
                7
            }
        }

        proof fn bad()
            ensures false
        {
            inline_air_stmt("(assert (= (f.? (I 300) (I 3)) (Add (f.? (I 300) (I 3)) 1)))");
            inline_air_stmt("(assume (= (f.? (I 300) (I 3)) (Add (f.? (I 300) (I 3)) 1)))");
        }
    } => Err(err) => { assert!(err.errors.len() == 1); }
}

test_verify_one_file_with_options! {
    #[test] const_generics_decreases ["-V allow-inline-air"] => verus_code! {
        spec fn some_spec_fn<const X: u8>() -> bool
            decreases 0int via dec::<X>
        {
            if X <= 255 {
                true
            } else {
                !some_spec_fn::<X>()
            }
        }

        #[verifier::decreases_by]
        proof fn dec<const X: u8>() {
            // TODO this should work without an 'assume'
            assume(X <= 255);
        }

        fn test1() {
            inline_air_stmt("(assert (= (some_spec_fn.? $ (CONST_INT 256)) true))");
        }

        fn test2() {
            inline_air_stmt("(assert (= (some_spec_fn.? $ (CONST_INT 255)) true))"); // ok
        }
    } => Err(err) => { assert!(err.errors.len() == 1); }
}

test_verify_one_file! {
    #[test] proof_decreases_recommends_fail verus_code! {
        spec fn f(i: int) -> int
            decreases i
        {
            recommends(false);

            if i == 0 {
                0
            } else {
                i + f(i) // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] mutable_reference_no_decreases verus_code! {
        fn e(s: &mut u64, i: usize) -> usize {
            if i < 10 {
                e(s, i + 1)
            } else {
                i
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mutable_reference_decreases_1 verus_code! {
        fn e(s: &mut u64, i: usize) -> usize
            decreases i
        {
            if i > 0 {
                e(s, i - 1)
            } else {
                i
            }
        }
    } => Ok(err) => {
        assert!(err.warnings.iter().find(|x| x.message.contains("decreases checks in exec functions do not guarantee termination of functions with loops or of their callers")).is_some());
    }
}

test_verify_one_file! {
    #[test] mutable_reference_decreases_2_pass verus_code! {
        fn e(s: &mut u64) -> u64
            decreases *old(s)
        {
            if *s > 0 {
                *s = *s - 1;
                e(s)
            } else {
                *s
            }
        }
    } => Ok(err) => {
        assert!(err.warnings.iter().find(|x| x.message.contains("decreases checks in exec functions do not guarantee termination of functions with loops or of their callers")).is_some());
    }
}

test_verify_one_file! {
    #[test] mutable_reference_decreases_2_fail verus_code! {
        fn e(s: &mut u64) -> u64
            decreases *old(s)
        {
            *s = *s - 1; // FAILS
            e(s) // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] exec_no_decreases verus_code! {
        fn e(s: &mut u64, i: usize) -> usize
        {
            decreases_by(check_e);
            if i < 10 {
                e(s, i + 1)
            } else {
                i
            }
        }

        #[verifier(decreases_by)]
        proof fn check_e(s: &mut u64, i: usize) {
        }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same parameters")
}

test_verify_one_file! {
    #[test] decreases_by_other_module_1_regression_249 verus_code! {
        mod A {
            #[allow(unused_imports)] use builtin::*;
            pub open spec fn f(a: nat) -> nat
                decreases a
            {
                decreases_by(termination_f);
                if a > 0 {
                    f((a - 1) as nat)
                } else {
                    0
                }
            }

            #[verifier(decreases_by)]
            pub proof fn termination_f(a: nat) {
                assert(true);
            }
        }

        mod B {
            #[allow(unused_imports)] use builtin::*;
            #[allow(unused_imports)] use crate::A::f;

            spec fn g() -> nat {
                f(10)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] decreases_by_other_module_2 verus_code! {
        mod A {
            #[allow(unused_imports)] use builtin::*;
            pub open spec fn f(a: nat) -> nat
                decreases a
            {
                decreases_by(crate::B::termination_f);
                if a > 10 {
                    f(a)
                } else {
                    0
                }
            }

        }

        mod B {
            #[allow(unused_imports)] use builtin::*;
            #[verifier(decreases_by)]
            pub proof fn termination_f(a: nat) {
                assert(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a decreases_by function must be in the same module as the function definition")
}

test_verify_one_file! {
    #[test] decreases_by_lemma_with_return_stmt_fails verus_code! {
        spec fn some_fun(i: nat) -> nat
            decreases i
        {
            decreases_by(decby_lemma);

            some_fun((i - 1) as nat)
        }

        #[verifier(decreases_by)]
        proof fn decby_lemma(i: nat)
        {
            if i > 0 {
            } else {
                return; // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] decreases_by_lemma_with_loop_fails verus_code! {
        spec fn some_fun(i: nat) -> nat
            decreases i
        {
            decreases_by(decby_lemma);

            some_fun((i - 1) as nat)
        }

        #[verifier(decreases_by)]
        proof fn decby_lemma(i: nat)
        {
            while true { }
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot use while in proof or spec mode")
}

test_verify_one_file! {
    #[test] decreases_by_lemma_with_assert_false_fails verus_code! {
        spec fn some_fun(i: nat) -> nat
            decreases i
        {
            decreases_by(decby_lemma);

            some_fun((i - 1) as nat)
        }

        #[verifier(decreases_by)]
        proof fn decby_lemma(i: nat)
        {
            assert(false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] decreases_on_non_recursive_generic_datatype_regression_315 verus_code! {
        // https://github.com/verus-lang/verus/issues/315
        use vstd::prelude::*;
        spec fn max(a: nat, b: nat) -> nat {
            if a >= b { a } else { b }
        }

        struct Node<V> {
            left: Box<Option<Node<V>>>,
            right: Box<Option<Node<V>>>,
            value: V,
        }

        impl<V: SpecOrd> Node<V> {
            spec fn height(&self) -> nat {
                decreases(self);
                max(
                    if let Option::Some(l) = *self.left { l.height() } else { 0 },
                    if let Option::Some(r) = *self.right { r.height() } else { 0 },
                )
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] decrease_through_seq verus_code! {
        use vstd::prelude::*;

        struct S {
            x: Seq<Box<S>>,
        }

        spec fn f(s: S) -> int
            decreases s
        {
            if s.x.len() > 0 {
                f(*s.x[0])
            } else {
                0
            }
        }

        proof fn p(s: S)
            decreases s
        {
            if s.x.len() > 0 {
                p(*s.x[0]);
                assert(false); // FAILS
            }
        }

        proof fn q(s: S)
            decreases s
        {
            q(*s.x[0]); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] decrease_through_map verus_code! {
        use vstd::prelude::*;

        struct S {
            x: Map<int, Box<S>>,
        }

        spec fn f(s: S) -> int
            decreases s
        {
            if s.x.dom().contains(3) {
                f(*s.x[3])
            } else {
                0
            }
        }

        proof fn p(s: S)
            decreases s
        {
            if s.x.dom().contains(3) {
                p(*s.x[3]);
                assert(false); // FAILS
            }
        }

        proof fn q(s: S)
            decreases s
        {
            q(*s.x[3]); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] decrease_through_my_map verus_code! {
        // Err on the side of caution; see https://github.com/FStarLang/FStar/pull/2954
        use vstd::prelude::*;

        #[verifier::reject_recursive_types(A)]
        #[verifier::accept_recursive_types(B)]
        struct MyMap<A, B>(Map<A, B>);
        struct S {
            x: MyMap<int, Box<S>>,
        }

        spec fn f(s: S) -> int
            decreases s
        {
            if s.x.0.dom().contains(3) { f(*s.x.0[3]) } else { 0 } // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] decrease_through_function verus_code! {
        enum E {
            Nil,
            F(spec_fn(int) -> E),
        }

        proof fn p(e: E)
            decreases e
        {
            if let E::F(f) = e {
                p(f(0));
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] decrease_through_function_fails verus_code! {
        enum E {
            Nil,
            F(spec_fn(int) -> E),
        }

        proof fn p(e: E)
            decreases e
        {
            if let E::F(f) = e {
                p(f(0));
                assert(false); // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] decrease_through_function_bad verus_code! {
        struct S {
            x: spec_fn(int) -> S,
        }

        proof fn p(s: S)
            ensures false
            decreases s
        {
            p((s.x)(0));
        }
    } => Err(e) => assert_vir_error_msg(e, "datatype must have at least one non-recursive variant")
}

test_verify_one_file! {
    #[test] decrease_through_my_fun verus_code! {
        // Err on the side of caution; see https://github.com/FStarLang/FStar/pull/2954
        use vstd::prelude::*;

        #[verifier::reject_recursive_types(A)]
        struct MyFun<A, B>(spec_fn(A) -> B);
        enum E {
            Nil,
            F(MyFun<int, E>),
        }

        proof fn p(e: E)
            decreases e
        {
            if let E::F(f) = e {
                p(f.0(0)); // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] decrease_through_abstract_type verus_code! {
        mod m1 {
            use builtin::*;
            pub struct S<A, B>(A, B);
            impl<A, B> S<A, B> {
                pub closed spec fn get0(self) -> A { self.0 }
                pub closed spec fn get1(self) -> B { self.1 }
            }
            // TODO: broadcast_forall
            pub proof fn lemma_height_s<A, B>(s: S<A, B>)
                ensures
                    decreases_to!(s => s.get0()),
                    decreases_to!(s => s.get1()),
            {
            }
        }

        mod m2 {
            use builtin::*;
            use crate::m1::*;
            enum Q {
                Nil,
                Cons(S<u8, Box<Q>>),
            }
            proof fn test(q: Q)
                decreases q,
            {
                if let Q::Cons(s) = q {
                    lemma_height_s(s);
                    test(*s.get1());
                }
            }
        }

        mod m3 {
            use builtin::*;
            use crate::m1::*;
            enum Q {
                Nil,
                Cons(S<u8, Box<Q>>),
            }
            proof fn test(q: Q)
                decreases q,
            {
                if let Q::Cons(s) = q {
                    test(*s.get1()); // FAILS
                }
            }
        }

        mod m4 {
            use builtin::*;
            use crate::m1::*;
            enum Q {
                Nil,
                Cons(S<u8, Box<Q>>),
            }
            proof fn test(q: Q)
                decreases q,
            {
                if let Q::Cons(s) = q {
                    lemma_height_s(s);
                    test(*s.get1());
                    assert(false); // FAILS
                }
            }
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] height_intrinsic verus_code! {
        #[is_variant]
        enum Tree {
            Node(Box<Tree>, Box<Tree>),
            Leaf,
        }

        proof fn testing(l: Tree, r: Tree) {
            let x = Tree::Node(Box::new(l), Box::new(r));

            assert(l == *x.get_Node_0());
            assert(r == *x.get_Node_1());

            assert(decreases_to!(x => l));
            assert(decreases_to!(x => r));
            assert(decreases_to!(x => x.get_Node_0()));
        }

        proof fn testing_fail(l: Tree, r: Tree) {
            let tmp = decreases_to!(l => r);
            assert(tmp); // FAILS
        }

        proof fn testing_fail2(x: Tree) {
            let tmp = decreases_to!(x => x.get_Node_0());
            assert(tmp); // FAILS
        }

        proof fn testing3(x: Tree)
            requires x.is_Node(),
        {
            assert(decreases_to!(x => x.get_Node_0()));
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] height_intrinsic_mode verus_code! {
        #[is_variant]
        enum Tree {
            Node(Box<Tree>, Box<Tree>),
            Leaf,
        }

        fn test(tree: Tree) {
            let x = decreases_to!(tree => tree);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] datatype_height_axiom_checks_the_variant verus_code! {
        #[is_variant]
        enum List {
            Cons(Box<List>),
            Nil,
        }

        spec fn list_length(l: List) -> int
            decreases l,
        {
            list_length(*l.get_Cons_0()) + 1 // FAILS
        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_one_file! {
    #[test] mutual_recursion_result_incompleteness_regression_564_1 verus_code! {
        use vstd::prelude::*;

        pub spec const NUM_LAYERS: nat = 4;
        pub spec const NUM_ENTRIES: nat = 32;

        pub enum Entry {
            Directory(Directory),
            Page(nat),
        }

        pub struct Directory {
            pub entries: Seq<Entry>,
        }

        #[verifier(external_body)]
        pub struct Data { }

        impl Data {

            pub open spec fn fn_one(self, layer: nat) -> Directory
                decreases NUM_LAYERS - layer, NUM_ENTRIES, 2nat
            {
                Directory { entries: self.fn_three(layer, seq![]) }
            }

            pub open spec fn fn_two(self, layer: nat, idx: nat) -> Entry
                decreases NUM_LAYERS - layer, NUM_ENTRIES - idx, 0nat
            {
                if layer + 1 <= NUM_LAYERS {
                    Entry::Directory(self.fn_one(layer + 1))
                } else {
                    arbitrary()
                }
            }

            pub open spec fn fn_three(self, layer: nat, init: Seq<Entry>) -> Seq<Entry>
                decreases NUM_LAYERS - layer, NUM_ENTRIES - init.len(), 1nat
                via Self::termination_fn_three
            {
                if init.len() >= NUM_ENTRIES {
                    init
                } else {
                    let entry = self.fn_two(layer, init.len());
                    self.fn_three(layer, init.add(seq![entry]))
                }
            }

            #[verifier(decreases_by)]
            proof fn termination_fn_three(self, layer: nat, init: Seq<Entry>) {
                let num_entries: nat = NUM_ENTRIES as nat;
                if init.len() >= num_entries {
                    assume(false);
                } else {
                    // let entry = self.fn_two(layer, init.len());
                    // self.fn_three(layer, init.add(seq![entry]))
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mutual_recursion_result_incompleteness_regression_564_2 verus_code! {
        use vstd::prelude::*;

        pub spec const NUM_LAYERS: nat = 4;
        pub spec const NUM_ENTRIES: nat = 32;

        pub open spec fn fn_two(layer: nat, idx: nat) -> nat
            decreases NUM_LAYERS - layer, NUM_ENTRIES - idx, 0nat
        {
            if layer + 1 <= NUM_LAYERS {
                fn_three(layer + 1, seq![]).len()
            } else {
                arbitrary()
            }
        }

        pub open spec fn fn_three(layer: nat, init: Seq<nat>) -> Seq<nat>
            decreases NUM_LAYERS - layer, NUM_ENTRIES - init.len(), 1nat
        {
            if init.len() >= NUM_ENTRIES {
                init
            } else {
                let entry = fn_two(layer, init.len());
                fn_three(layer, init.push(entry))
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] decreases_inside_closure verus_code! {
        spec fn f1(n: int) -> spec_fn(int) -> int
            decreases n
        {
            if n > 0 {
                |i: int| f1(n - 1)(i)
            } else {
                |i: int| i
            }
        }

        spec fn f2(n: int) -> spec_fn(int) -> int
            decreases n
        {
            if n > 0 {
                |i: int| f2(n + 1)(i) // FAILS
            } else {
                |i: int| i
            }
        }
    } => Err(e) => assert_one_fails(e)
}

// We now also allow decreases inside choose|x| body,
// on the grounds that you could rewrite this as let f = |x| body; choose|x| f(x)
// and decreases is already allowed in |x| body.
test_verify_one_file! {
    #[test] decreases_inside_choose verus_code! {
        spec fn f(n: int) -> bool
            decreases n
        {
            if n > 0 {
                0 == choose|i: int| f(i) // FAILS
            } else {
                false
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] lemma_not_proved_by_impossible_fun verus_code! {
        spec fn impossible_fun() -> bool
            decreases 0int
              via f_decreases
        {
            !impossible_fun()
        }

        #[verifier::decreases_by]
        proof fn f_decreases() {
            bad_lemma();
        }

        proof fn bad_lemma()
            ensures false,
        {
            assert(false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] lemma_not_proved_by_impossible_fun2 verus_code! {
        spec fn impossible_fun() -> bool
            decreases 0int
              via f_decreases
        {
            !impossible_fun()
        }

        #[verifier::decreases_by]
        proof fn f_decreases() {
            bad_lemma();
        }

        proof fn bad_lemma()
            ensures false,
        {
            assert(impossible_fun() == !impossible_fun());
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "found cyclic dependency in decreases_by function")
}

test_verify_one_file! {
    #[test] lemma_decreases_vec_seq_len verus_code! {
        use vstd::prelude::*;
        struct S {
            s: Seq<Box<S>>,
        }

        struct V {
            v: Vec<Box<V>>,
        }

        spec fn f(s: Seq<Box<S>>) -> int
            decreases s
        {
            if s.len() == 0 {
                0
            } else if s.len() == 1 {
                f(s[0].s)
            } else {
                f(s.drop_last())
            }
        }

        spec fn vs(v: V) -> S
            decreases v
        {
            let s = Seq::new(v.v.len() as nat, |i: int| {
                if 0 <= i < v.v.len() {
                    Box::new(vs(*v.v[i]))
                } else {
                    arbitrary()
                }
            });
            S { s }
        }

        spec fn sbad(s: Seq<bool>) -> Seq<bool>
            decreases s
        {
            sbad(s) // FAILS
        }

        spec fn vbad(v: Vec<bool>) -> Vec<bool>
            decreases v
        {
            vbad(v) // FAILS
        }

        struct X {
            y: Seq<X>,
        }

        proof fn bad() {
            let x0 = X { y: seq![] };
            let t = seq![X { y: seq![ x0, x0 ] }];
            assert(decreases_to!(t => t[0]));
            assert(decreases_to!(t[0] => t[0].y));

            vstd::seq::axiom_seq_len_decreases(t[0].y, t); // FAILS
            assert(decreases_to!(t[0].y => t));
        }
    } => Err(e) => assert_fails(e, 3)
}

test_verify_one_file! {
    #[test] commas_in_spec_sigs_github_issue947 verus_code! {
        spec fn add0(a: nat, b: nat) -> nat
            recommends
                a > 0,
            via add0_recommends
        {
            a
        }

        #[via_fn]
        proof fn add0_recommends(a: nat, b: nat) {
            // proof
        }

        spec fn rids_match(bools_start: nat) -> bool
            decreases bools_start,
            when 0 <= bools_start <= 5
        {
            true
        }

    } => Ok(())
}
