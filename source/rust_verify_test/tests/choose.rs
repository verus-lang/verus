#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// choose

test_verify_one_file! {
    #[test] test1 verus_code! {
        spec fn f(i: int) -> bool {
            5 <= i
        }

        proof fn test_choose() {
            let i = choose|i: int| f(i);
            assert(f(7));
            assert(5 <= i);
        }

        proof fn test_choose_inference() {
            let i = choose|i| f(i);
            assert(f(7));
            assert(5 <= i);
        }


        proof fn test_choose_eq() {
            let i1 = choose|i: int| f(i) && (1 + 1 == 2);
            let i2 = choose|i: int| f(i) && (2 + 2 == 4);
            assert(i1 == i2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 verus_code! {
        spec fn f(i: int) -> bool {
            5 <= i
        }

        proof fn test_choose() {
            let i = choose|i: int| f(i);
            assert(5 <= i); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2 verus_code! {
        spec fn f(i: int) -> bool {
            5 <= i
        }

        proof fn test_choose() {
            let i = choose|i: int| f(i);
            assert(f(7));
            assert(i == 7); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails3 verus_code! {
        spec fn f(i: int) -> bool {
            5 <= i
        }

        proof fn test_choose_eq() {
            let i1 = choose|i: int| f(i) && (2 + 2 == 4);
            let i2 = choose|i: int| (2 + 2 == 4) && f(i);
            // requires extensional equality
            assert(i1 == i2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_refine verus_code! {
        spec fn cnatf(n: nat) -> bool {
            true
        }

        spec fn cintf(n: int) -> bool {
            true
        }

        proof fn cnat() {
            assert((choose|n: nat| cnatf(n)) >= 0);
            assert((choose|n: nat| cintf(n as int) && n < 0) >= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_refine_fail1 verus_code! {
        spec fn cintf(n: int) -> bool {
            true
        }

        proof fn cnat() {
            assert(cintf(-10));
            assert((choose|n: nat| cintf(n as int) && n < 0) < 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_refine2 verus_code! {
        spec fn cnatf(n: nat) -> bool {
            true
        }

        proof fn cnat() {
            assert(cnatf(10));
            assert((choose|n: nat| cnatf(n) && n >= 10) >= 10);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_choose_with_closure_illegal verus_code! {
        spec fn f(i: int, j: int) -> bool {
            i <= j
        }

        proof fn test_choose() {
            let (i, j): (int, int) = choose(|i: int, j: int| f(i, j));
            assert(f(7, 8));
            assert(i <= j);
        }
    } => Err(e) => assert_vir_error_msg(e, "forall, choose, and exists do not allow parentheses")
}

// choose_tuple

test_verify_one_file! {
    #[test] test1_tuple verus_code! {
        spec fn f(i: int, j: int) -> bool {
            i <= j
        }

        proof fn test_choose() {
            let (i, j): (int, int) = choose|i: int, j: int| f(i, j);
            assert(f(7, 8));
            assert(i <= j);
        }

        proof fn test_choose_eq() {
            let (i1, j1): (int, int) = choose|i: int, j: int| f(i, j) && (1 + 1 == 2);
            let (i2, j2): (int, int) = choose|i: int, j: int| f(i, j) && (2 + 2 == 4);
            assert(i1 == i2);
            assert(j1 == j2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1_tuple verus_code! {
        spec fn f(i: int, j: int) -> bool {
            i <= j
        }

        proof fn test_choose() {
            let (i, j): (int, int) = choose|i: int, j: int| f(i, j);
            assert(i <= j); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2_tuple verus_code! {
        spec fn f(i: int, j: int) -> bool {
            i <= j
        }

        proof fn test_choose() {
            let (i, j): (int, int) = choose|i: int, j: int| f(i, j);
            assert(f(7, 8));
            assert(i == 7); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails3_tuple verus_code! {
        spec fn f(i: int, j: int) -> bool {
            i <= j
        }

        proof fn test_choose_eq() {
            let (i1, j1): (int, int) = choose|i: int, j: int| f(i, j) && (2 + 2 == 4);
            let (i2, j2): (int, int) = choose|i: int, j: int| (2 + 2 == 4) && f(i, j);
            // requires extensional equality
            assert(i1 == i2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_refine_tuple verus_code! {
        spec fn cnatf(m: nat, n: nat) -> bool {
            true
        }

        spec fn cintf(m: int, n: int) -> bool {
            true
        }

        proof fn cnat() {
            assert(choose_tuple::<(nat, nat), _>(|m: nat, n: nat| cnatf(m, n)).0 >= 0);
            assert(choose_tuple::<(nat, nat), _>(|m: nat, n: nat| cintf(m as int, n as int) && m < 0 && n < 0).0 >= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_refine_fail1_tuple verus_code! {
        spec fn cintf(m: int, n: int) -> bool {
            true
        }

        proof fn cnat() {
            assert(cintf(-10, -10));
            assert(choose_tuple::<(nat, nat), _>(|m: nat, n: nat| cintf(m as int, n as int) && m < 0 && n < 0).0 < 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_refine2_tuple verus_code! {
        spec fn cnatf(m: nat, n: nat) -> bool {
            true
        }

        proof fn cnat() {
            assert(cnatf(10, 10));
            assert(choose_tuple::<(nat, nat), _>(|m: nat, n: nat| cnatf(m, n) && m >= 10 && n >= 10).0 >= 10);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_choose_tuple_wrong_type verus_code! {
        spec fn f(i: int, j: int) -> bool {
            i <= j
        }

        proof fn test_choose() {
            let (i, j): (int, nat) = choose_tuple(|i: int, j: int| f(i, j));
        }
    } => Err(err) => assert_vir_error_msg(err, "expected choose_tuple to have type")
}

test_verify_one_file! {
    #[test] test1_choose_tuple_no_ascription_regression_1183 verus_code! {
        spec fn less_than(x: int, y: int) -> bool {
            x < y
        }

        proof fn test_choose_succeeds2() {
            assert(less_than(3, 7));  // promote i = 3, i = 7 as a witness
            let (x, y) = choose|i: int, j: int| less_than(i, j);
            assert(x < y);
        }
    } => Ok(())
}
