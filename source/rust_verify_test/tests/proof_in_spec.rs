#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] rec_assume verus_code! {
        spec fn f(i: int) -> int decreases i {
            proof {
                assume(false);
            }
            f(i) + 1
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] rec_assert_false verus_code! {
        spec fn f(i: int) -> int decreases i {
            proof {
                assert(false); // FAILS
            }
            f(i) + 1
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] rec_assert_assume verus_code! {
        spec fn f(i: int) -> int decreases i when i > 3 {
            proof {
                assert(i > 3);
                assume(false);
            }
            f(i) + 1
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] rec_assert_bitvector1 verus_code! {
        spec fn f(i: u64) -> int decreases i {
            if i == 0 {
                0
            } else {
                proof {
                    assert(i >> 1 < i) by(bit_vector)
                        requires i != 0;
                }
                f(i >> 1)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] rec_assert_bitvector2 verus_code! {
        spec fn f(i: u64) -> int decreases i {
            if i == 0 {
                0
            } else {
                proof {
                    assert(i >> 1 < i) by(bit_vector); // FAILS
                }
                f(i >> 1)
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] rec_assert_bitvector3 verus_code! {
        spec fn f(i: u64) -> int decreases i {
            if i == 0 {
                0
            } else {
                proof {
                    assert(i >> 1 <= i) by(bit_vector);
                }
                f(i >> 1) // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] rec_assert_result verus_code! {
        spec fn f(i: int) -> int decreases i {
            if i <= 0 {
                0
            } else {
                let x = f(i - 1);
                proof {
                    assert(x < x + 1);
                }
                x + 1
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] rec_proof_ok verus_code! {
        uninterp spec fn one() -> int;

        proof fn is_one() ensures one() == 1 { admit(); }

        spec fn f(i: int) -> int decreases i {
            if i <= 0 {
                0
            } else {
                proof {
                    is_one();
                }
                1 + f(i - one())
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] rec_proof_fails_requires verus_code! {
        uninterp spec fn one() -> int;

        proof fn is_one() requires false ensures one() == 1 { admit(); }

        spec fn f(i: int) -> int decreases i {
            if i <= 0 {
                0
            } else {
                proof {
                    is_one(); // FAILS
                }
                1 + f(i - one())
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] rec_proof_ineffective verus_code! {
        uninterp spec fn one() -> int;

        proof fn is_one() ensures one() != 1 { admit(); }

        spec fn f(i: int) -> int decreases i {
            if i <= 0 {
                0
            } else {
                proof {
                    is_one();
                }
                1 + f(i - one()) // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] rec_proof_ok_by verus_code! {
        uninterp spec fn one() -> int;

        proof fn is_one() ensures one() == 1 { admit(); }

        spec fn f(i: int) -> int decreases i {
            if i <= 0 {
                0
            } else {
                proof {
                    assert(one() == 1) by {
                        is_one();
                    }
                }
                1 + f(i - one())
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] rec_proof_fails_requires_by verus_code! {
        uninterp spec fn one() -> int;

        proof fn is_one() requires false ensures one() == 1 { admit(); }

        spec fn f(i: int) -> int decreases i {
            if i <= 0 {
                0
            } else {
                proof {
                    assert(one() == 1) by {
                        is_one(); // FAILS
                    }
                }
                1 + f(i - one())
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] rec_proof_ineffective_by verus_code! {
        uninterp spec fn one() -> int;

        proof fn is_one() ensures one() != 1 { admit(); }

        spec fn f(i: int) -> int decreases i {
            if i <= 0 {
                0
            } else {
                proof {
                    assert(one() != 1) by {
                        is_one();
                    }
                }
                1 + f(i - one()) // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] rec_proof_by_fails verus_code! {
        uninterp spec fn one() -> int;

        proof fn is_one() ensures one() != 1 { admit(); }

        spec fn f(i: int) -> int decreases i {
            if i <= 0 {
                0
            } else {
                proof {
                    assert(one() == 1) by { // FAILS
                        is_one();
                    }
                }
                1 + f(i - one())
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] nonrecursive_not_yet_supported1 verus_code! {
        spec fn f(i: int) -> int {
            proof {
                assert(true);
            }
            3
        }
    } => Err(err) => assert_vir_error_msg(err, "proof blocks inside spec code is currently supported only for")
}

test_verify_one_file! {
    #[test] nonrecursive_not_yet_supported2 verus_code! {
        spec fn f(i: int) -> int decreases i {
            proof {
                assert(true);
            }
            3
        }
    } => Err(err) => assert_vir_error_msg(err, "proof blocks inside spec code is currently supported only for")
}

// proof blocks inside proof fn are now allowed (redundant but harmless)
test_verify_one_file! {
    #[test] proof_block_in_proof_fn_allowed verus_code! {
        proof fn f(i: int) {
            let x: int = {
                proof {
                    assert(true);
                }
                3
            };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] return_not_allowed verus_code! {
        spec fn f(i: int) -> int decreases i {
            proof {
                if i > 0 {
                    return 3;
                }
            }
            4
        }
    } => Err(err) => assert_vir_error_msg(err, "return is not allowed inside spec")
}

// assignment inside proof block in proof fn is now allowed
test_verify_one_file! {
    #[test] assign_in_proof_block_in_proof_fn verus_code! {
        proof fn f(i: int) {
            let mut b = false;
            let x: int = {
                proof {
                    b = true;
                }
                3
            };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tracked_not_allowed1 verus_code! {
        #[verifier::external_body]
        proof fn g() -> (tracked i: int) {
            panic!()
        }
        proof fn h(tracked i: int) {
        }

        spec fn f(i: int) -> int decreases i {
            proof {
                let tracked x = g();
                h(x);
                h(x);
            }
            4
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

// tracked variables inside proof block in proof fn is now allowed
test_verify_one_file! {
    #[test] tracked_in_proof_block_in_proof_fn verus_code! {
        proof fn h(tracked i: int) {
        }
        proof fn f(tracked i: int) {
            let x: int = {
                proof {
                    h(i);
                }
                3
            };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] rec_cycle1 verus_code! {
        proof fn p() -> int {
            3
        }

        spec fn f(i: int) -> int decreases i {
            let x = proof { p() };
            x
        }
    } => Err(err) => assert_vir_error_msg(err, "proof block must have type")
}

test_verify_one_file! {
    #[test] rec_cycle2 verus_code! {
        proof fn p(i: int)
            ensures false
            decreases i
        {
            assert(f(3) == f(3) + 1); // FAILS
        }

        spec fn f(i: int) -> int decreases i when i > 0 {
            proof {
                p(i - 1)
            }
            f(i) + 1
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] rec_cycle3 verus_code! {
        proof fn p(i: int)
            ensures false
            decreases i
        {
            assert(f(3) == f(3) + 1); // FAILS
        }

        spec fn f(i: int) -> int decreases i {
            proof {
                p(i) // FAILS
            }
            f(i) + 1
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] rec_cycle4 verus_code! {
        proof fn p()
            ensures false
            decreases 1int
        {
            assert(f(3) == f(3) + 1); // FAILS
        }

        spec fn f(i: int) -> int decreases i {
            proof {
                p() // FAILS
            }
            f(i) + 1
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] rec_cycle5 verus_code! {
        proof fn p()
            ensures false
        {
            assert(f(3) == f(3) + 1);
        }

        spec fn f(i: int) -> int decreases i {
            proof {
                p()
            }
            f(i) + 1
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] proof_inside_pure1 verus_code! {
        spec fn f(n: int) -> bool
            decreases n
        {
            0 == choose|i: int| {
                proof {
                    assume(false);
                }
                f(i)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] proof_inside_pure2 verus_code! {
        spec fn f(n: int) -> bool
            decreases n
        {
            0 == choose|i: int| {
                proof {
                    assert(true);
                }
                f(i) // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] proof_inside_pure3 verus_code! {
        spec fn f(n: int) -> bool
            decreases n
        {
            0 == choose|i: int| {
                proof {
                    assert(false); // FAILS
                }
                f(i)
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] rec_spinoff_prover verus_code! {
        spec fn count(n: nat) -> nat
            decreases n,
        {
            proof {
                assert(true);
            }
            if n == 0 {
                0
            } else {
                count((n - 1) as nat)
            }
        }
        #[verifier::spinoff_prover]
        proof fn test() {
            assert(count(0) == 0);
        }
    } => Ok(())
}

// ============================================================================
// Tests for issue #2061: proof blocks inside proof fn should be allowed
// https://github.com/verus-lang/verus/issues/2061
// ============================================================================

// Basic case from the issue: proof { } directly in proof fn body
test_verify_one_file! {
    #[test] issue_2061_basic verus_code! {
        proof fn foo() {
            proof { }
        }
    } => Ok(())
}

// proof block with assertion in proof fn
test_verify_one_file! {
    #[test] issue_2061_with_assert verus_code! {
        proof fn foo() {
            proof {
                assert(1 + 1 == 2);
            }
        }
    } => Ok(())
}

// proof block with failing assertion in proof fn
test_verify_one_file! {
    #[test] issue_2061_with_failing_assert verus_code! {
        proof fn foo() {
            proof {
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

// nested proof blocks in proof fn
test_verify_one_file! {
    #[test] issue_2061_nested verus_code! {
        proof fn foo() {
            proof {
                proof {
                    assert(true);
                }
            }
        }
    } => Ok(())
}

// proof block in proof fn with local variable
test_verify_one_file! {
    #[test] issue_2061_with_local verus_code! {
        proof fn foo() {
            let x: int = 5;
            proof {
                assert(x == 5);
            }
        }
    } => Ok(())
}

// proof block in proof fn inside expression
test_verify_one_file! {
    #[test] issue_2061_in_expression verus_code! {
        proof fn foo() -> int {
            let result: int = {
                proof {
                    assert(true);
                }
                42
            };
            result
        }
    } => Ok(())
}

// Verify spec fn with decreases still works (regression test)
test_verify_one_file! {
    #[test] issue_2061_spec_fn_still_works verus_code! {
        spec fn factorial(n: nat) -> nat
            decreases n
        {
            if n == 0 {
                1
            } else {
                proof {
                    // This proof block in spec fn with decreases should still work
                    assert(n > 0);
                }
                n * factorial((n - 1) as nat)
            }
        }
    } => Ok(())
}

// Ensure proof blocks in spec fn WITHOUT decreases still error
test_verify_one_file! {
    #[test] issue_2061_spec_fn_no_decreases_still_errors verus_code! {
        spec fn f(i: int) -> int {
            proof {
                assert(true);
            }
            3
        }
    } => Err(err) => assert_vir_error_msg(err, "proof blocks inside spec code is currently supported only for")
}
