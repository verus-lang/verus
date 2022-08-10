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
    } => Err(_)
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
    } => Err(_)
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
    // Test that fuel only provides one definition unfolding
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
            assert(count_down_a(1) == 1);   // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // Test that fuel only provides one definition unfolding
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
            assert(count_down_a(1) == 1);   // FAILS
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
    } => Err(_)
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
    } => Err(err) => assert_one_fails(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Err(err) => assert_vir_error(err)
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
    } => Ok(())
}

test_verify_one_file! {
    #[test] mutable_reference_decreases_2_pass verus_code! {
        fn e(s: &mut u64) -> u64
            decreases *s
        {
            if *s > 0 {
                *s = *s - 1;
                e(s)
            } else {
                *s
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mutable_reference_decreases_2_fail verus_code! {
        fn e(s: &mut u64) -> u64
            decreases *s
        {
            *s = *s - 1;
            e(s) // FAILS
        }
    } => Err(e) => assert_one_fails(e)
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
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] decreases_by_other_module_1_regression_249 verus_code! {
        mod A {
            #[allow(unused_imports)] use builtin::*;
            pub open spec fn f() -> nat {
                decreases_by(termination_f);
                0
            }

            #[verifier(decreases_by)]
            pub proof fn termination_f() {
            }
        }

        mod B {
            #[allow(unused_imports)] use builtin::*;
            #[allow(unused_imports)] use crate::A::f;

            spec fn g() -> nat {
                f()
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] decreases_by_other_module_2 verus_code! {
        mod A {
            #[allow(unused_imports)] use builtin::*;
            pub open spec fn f() -> nat {
                decreases_by(crate::B::termination_f);
                0
            }

        }

        mod B {
            #[allow(unused_imports)] use builtin::*;
            #[verifier(decreases_by)]
            pub proof fn termination_f() {
                assert(false);
            }
        }
    } => Err(e) => assert_vir_error(e) // the decreases_by function must be in the same module
}
