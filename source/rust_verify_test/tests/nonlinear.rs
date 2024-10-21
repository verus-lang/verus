// Some testcases are ported from https://github.com/secure-foundations/libraries/tree/master/src/NonlinearArithmetic

#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Test #[verifier(nonlinear)]

test_verify_one_file! {
    #[test] test1 verus_code! {
        #[verifier(nonlinear)]
        proof fn lemma_mul_upper_bound(x: int, x_bound: int, y: int, y_bound: int)
            requires
                x <= x_bound,
                y <= y_bound,
                0 <= x,
                0 <= y,
            ensures
                x * y <= x_bound * y_bound,
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        #[verifier(nonlinear)]
        proof fn lemma_mul_stay_positive(x: int, y: int)
            requires
                0 <= x,
                0 <= y,
            ensures
                0 <= x * y,
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3 verus_code! {
        #[verifier(nonlinear)]
        proof fn lemma_inequality_after_mul(x: int, y: int, z: int)
            requires
                x <= y,
                0 <= z,
            ensures
                x * z <= y * z,
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test4 verus_code! {
        #[verifier(nonlinear)]
        proof fn lemma_div_pos_is_pos(x: int, d: int)
            requires
                0 <= x,
                0 < d,
            ensures
                0 <= x / d,
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails verus_code! {
        #[verifier(nonlinear)]
        proof fn wrong_lemma_1(x: int, y: int, z: int)
            requires
                x <= y,
                0 <= z,
            ensures
                x * z < y * z, // FAILS
        {
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test2_fails verus_code! {
        #[verifier(nonlinear)]
        proof fn wrong_lemma_2(x: int, y: int, z: int)
            requires
                x > y,
                3 <= z,
            ensures
                y * z > x, // FAILS
        {
        }
    } => Err(e) => assert_one_fails(e)
}

// Test assert_nonlinear_by
test_verify_one_file! {
    #[test] test5 verus_code! {
        proof fn test5_bound_checking(x: u32, y: u32, z: u32)
            requires
                x <= 0xffff,
                y <= 0xffff,
                z <= 0xffff,
        {
            assert(x * z == mul(x, z)) by(nonlinear_arith)
                requires
                    x <= 0xffff,
                    z <= 0xffff,
            {
                assert(0 <= x * z);
                assert(x * z <= 0xffff * 0xffff);
            }
            assert(x * z == mul(x, z));

            assert(y * z == mul(y, z)) by(nonlinear_arith)
                requires
                    y <= 0xffff,
                    z <= 0xffff,
            {
                assert(0 <= y * z);
                assert(y * z <= 0xffff * 0xffff);
            }
            assert(y * z == mul(y, z));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test6 verus_code! {
        proof fn test6(x: u32, y: u32, z: u32)
            requires x < 0xfff
        {
            assert(add(mul(x, x), x) == mul(x, add(x, 1))) by(nonlinear_arith)
                requires x < 0xfff
            {
            }
            assert(add(mul(x, x), x) == mul(x, add(x, 1)));

            assert(mul(x, y) == mul(y, x)) by(nonlinear_arith);
            assert(mul(x, y) == mul(y, x));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_requires verus_code! {
        proof fn test(x: nat, y: nat, z: nat) {
            assert(x * x + x == x * (x + 1)) by(nonlinear_arith)
                requires x < 0xfff // FAILS
            {
            }
            assert(x * x + x == x * (x + 1));
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test7 verus_code! {
        proof fn test6(x: int, y: int, z: int) {
            assert((x + y) * z == x * z + y * z) by(nonlinear_arith);
            assert((x + y) * z == x * z + y * z);

            assert((x - y) * z == x * z - y * z) by(nonlinear_arith);
            assert((x - y) * z == x * z - y * z);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3_fails verus_code! {
        proof fn test3_fails(x: int, y: int, z: int) {
            assert(x * y == y * z) by(nonlinear_arith); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test4_fails verus_code! {
        proof fn test4_fails(x: u32, y: u32, z: u32) {
            assert(x * z == (mul(x, z) as int)) by(nonlinear_arith); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_assert_nonlinear_by_in_nonlinear verus_code! {
        #[verifier(nonlinear)]
        proof fn test(x: u32)
            requires x < 0xfff
        {
            assert(x * x + x == x * (x + 1)) by(nonlinear_arith)
                requires x < 0xfff
            {
            }
            assert(x * x + x == x * (x + 1));
        }
    } => Err(err) => assert_vir_error_msg(err, "assert_by_query not allowed in #[verifier::nonlinear] functions")
}

test_verify_one_file! {
    #[test] test_negative verus_code! {
        proof fn test6(x: int, y: int, z:int) {
            assert((x + y) * z == x * z + y * z) by(nonlinear_arith);
            assert(false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_unexpected_vars verus_code! {
        proof fn test6(x: int, y: int, z:int)
            requires
                y == 0,
                z == 0,
        {
            assert(x + y == x) by(nonlinear_arith)
                requires y == 0
            {
                assert(z == 0);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "not mentioned in requires/ensures")
}

test_verify_one_file! {
    #[test] test_complex_vars verus_code! {
        proof fn test6(a1: int, a2: int) {
            let (b1, b2) = if a1 <= a2 {
                (a1, a2)
            } else {
                (a2, a1)
            };
            assert(b1 <= b2) by(nonlinear_arith)
                requires b1 <= b2
            {
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_requires_no_block verus_code! {
        proof fn test6(a1: int, a2: int) {
            let (b1, b2) = if a1 <= a2 {
                (a1, a2)
            } else {
                (a2, a1)
            };
            assert(b1 <= b2) by(nonlinear_arith)
                requires b1 <= b2;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_new_vars verus_code! {
        proof fn test6(x: int)
            requires x == 5
        {
            assert({let z: int = 2; x * z == 10}) by(nonlinear_arith)
                requires ({let z: int = 5; x == z})
            {
                let y: nat = mul(x as nat, 2);
                assert(y == 10);
            }
            assert(x * 2 == 10);
        }

        fn test7(n: u32) {
            loop {
                assert(true) by (nonlinear_arith)
                    requires
                        ({let q = n; q <= n})
                { }
                break;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] // Z3 is too slow with this test
    #[test] nlarith1 verus_code! {
        fn test(x: int, y: int, z: int) {
            assume(x * y == z && x != 0);
            assert(z % x == 0) by(nonlinear_arith) requires x * y == z && x != 0 {}
        }
    } => Ok(())
}
