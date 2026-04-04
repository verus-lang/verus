#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// ============================================================
// Contradictory requires clauses
// ============================================================

// Positive: consistent requires, proof goes through
test_verify_one_file_with_options! {
    #[test] vacuity_requires_consistent ["-V check-vacuity"] => verus_code! {
        proof fn test(x: int)
            requires x > 3,
            ensures x >= 3,
        {
        }
    } => Ok(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_none());
    }
}

// Negative: contradictory requires
test_verify_one_file_with_options! {
    #[test] vacuity_requires_inconsistent ["-V check-vacuity"] => verus_code! {
        proof fn test(x: int)
            requires
                x > 10,
                x < 5,
            ensures x == 42,
        {
        }
    } => Err(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_some());
    }
}

// Negative: three requires that are pairwise consistent but jointly inconsistent
test_verify_one_file_with_options! {
    #[test] vacuity_requires_jointly_inconsistent ["-V check-vacuity"] => verus_code! {
        proof fn test(x: int)
            requires
                x % 2 == 0,
                x % 3 == 0,
                x == 7,
            ensures false,
        {
        }
    } => Err(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_some());
    }
}

// ============================================================
// Type invariants contradicting requires
// ============================================================

// Positive: u8 parameter with consistent requires
test_verify_one_file_with_options! {
    #[test] vacuity_type_invariant_consistent ["-V check-vacuity"] => verus_code! {
        proof fn test(x: u8)
            requires x > 100,
            ensures x >= 100,
        {
        }
    } => Ok(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_none());
    }
}

// Negative: requires contradicts the u8 type invariant (0..256)
test_verify_one_file_with_options! {
    #[test] vacuity_type_invariant_inconsistent ["-V check-vacuity"] => verus_code! {
        proof fn test(x: u8)
            requires x > 300,
            ensures false,
        {
        }
    } => Err(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_some());
    }
}

// Negative: two u8 params whose sum can't exceed 510, but requires says > 600
test_verify_one_file_with_options! {
    #[test] vacuity_type_invariant_joint ["-V check-vacuity"] => verus_code! {
        proof fn test(x: u8, y: u8)
            requires x as int + y as int > 600,
            ensures false,
        {
        }
    } => Err(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_some());
    }
}

// ============================================================
// Trait bounds
// ============================================================

// Positive: trait with spec method, consistent usage
test_verify_one_file_with_options! {
    #[test] vacuity_trait_consistent ["-V check-vacuity"] => verus_code! {
        trait Bounded {
            spec fn lo(&self) -> int;
            spec fn hi(&self) -> int;

            proof fn bounds_valid(&self)
                ensures self.lo() <= self.hi();
        }

        proof fn test<T: Bounded>(t: &T)
            requires t.lo() <= 5, t.hi() >= 5,
            ensures t.lo() <= t.hi(),
        {
        }
    } => Ok(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_none());
    }
}

// ============================================================
// Spec functions with contradictory requires
// ============================================================

// Negative: uninterpreted spec fn with contradictory requires
test_verify_one_file_with_options! {
    #[test] vacuity_spec_fn_contradictory ["-V check-vacuity"] => verus_code! {
        spec fn mystery(x: int) -> int;

        proof fn test(a: int)
            requires
                mystery(a) > 0,
                mystery(a) < 0,
            ensures a == 0,
        {
        }
    } => Err(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_some());
    }
}

// Positive: spec fn with consistent requires
test_verify_one_file_with_options! {
    #[test] vacuity_spec_fn_consistent ["-V check-vacuity"] => verus_code! {
        spec fn abs(x: int) -> int {
            if x >= 0 { x } else { -x }
        }

        proof fn test(x: int)
            requires abs(x) < 10, x > 0,
            ensures x < 10,
        {
        }
    } => Ok(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_none());
    }
}

// ============================================================
// Exec functions
// ============================================================

// Negative: exec fn with contradictory requires
test_verify_one_file_with_options! {
    #[test] vacuity_exec_fn_inconsistent ["-V check-vacuity"] => verus_code! {
        fn test(x: u64)
            requires x > 1000000, x < 5,
            ensures false,
        {
        }
    } => Err(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_some());
    }
}

// ============================================================
// No false positives for valid code patterns
// ============================================================

// No requires at all — should never be vacuous
test_verify_one_file_with_options! {
    #[test] vacuity_no_requires ["-V check-vacuity"] => verus_code! {
        proof fn test() {
            assert(1 + 1 == 2);
        }
    } => Ok(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_none());
    }
}

// If/else with consistent conditions — no false positive
test_verify_one_file_with_options! {
    #[test] vacuity_if_else_no_false_positive ["-V check-vacuity"] => verus_code! {
        proof fn test(x: int)
            requires x > 0,
        {
            if x > 10 {
                assert(x > 0);
            } else {
                assert(x <= 10);
            }
        }
    } => Ok(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_none());
    }
}

// If/else with contradictory requires — vacuity detected in both branches
test_verify_one_file_with_options! {
    #[test] vacuity_if_else_contradictory ["-V check-vacuity"] => verus_code! {
        proof fn test(x: int)
            requires x > 10, x < 5,
        {
            if x > 7 {
                assert(x > 100);
            } else {
                assert(x < -100);
            }
        }
    } => Err(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_some());
    }
}

// Early return — no false positive
test_verify_one_file_with_options! {
    #[test] vacuity_early_return_no_false_positive ["-V check-vacuity"] => verus_code! {
        fn test(x: u64) -> (r: u64)
            requires x < 100,
            ensures r <= 100,
        {
            if x == 0 {
                return 0;
            }
            x
        }
    } => Ok(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_none());
    }
}

// Early return with contradictory requires — vacuity detected
test_verify_one_file_with_options! {
    #[test] vacuity_early_return_contradictory ["-V check-vacuity"] => verus_code! {
        fn test(x: u64) -> (r: u64)
            requires x < 5, x > 1000,
            ensures r == 999,
        {
            if x == 0 {
                return 999;
            }
            999
        }
    } => Err(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_some());
    }
}

// Loop with consistent invariant — no false positive
test_verify_one_file_with_options! {
    #[test] vacuity_loop_no_false_positive ["-V check-vacuity"] => verus_code! {
        fn test() {
            let mut i: u64 = 0;
            while i < 10
                invariant i <= 10,
                decreases 10 - i,
            {
                i = i + 1;
            }
        }
    } => Ok(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_none());
    }
}

// Function call with consistent postconditions — no false positive
test_verify_one_file_with_options! {
    #[test] vacuity_call_no_false_positive ["-V check-vacuity"] => verus_code! {
        proof fn helper(x: int) -> (r: int)
            requires x > 0,
            ensures r > x,
        {
            x + 1
        }

        proof fn test()
        {
            let r = helper(5);
            assert(r > 5);
        }
    } => Ok(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_none());
    }
}

// Reveal/opaque — no false positive
test_verify_one_file_with_options! {
    #[test] vacuity_reveal_no_false_positive ["-V check-vacuity"] => verus_code! {
        #[verifier::opaque]
        spec fn secret(x: int) -> bool {
            x > 0
        }

        proof fn test(x: int)
            requires x == 5,
        {
            reveal(secret);
            assert(secret(x));
        }
    } => Ok(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_none());
    }
}

// ============================================================
// assume() builtin — assume(false) makes the context
// contradictory, so assert(1 == 2) is proved vacuously.
// This IS detected by the unsat core approach.
// ============================================================

test_verify_one_file_with_options! {
    #[test] vacuity_assume_builtin_detected ["-V check-vacuity"] => verus_code! {
        proof fn test() {
            assume(false);
            assert(1 == 2);
        }
    } => Err(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_some());
    }
}

// ============================================================
// external_body — contradictory ensures from a call ARE
// detected by the unsat-core approach (the assertion's tracking
// variable is not needed when assumptions are contradictory)
// ============================================================

test_verify_one_file_with_options! {
    #[test] vacuity_external_body_call_detected ["-V check-vacuity"] => verus_code! {
        #[verifier::external_body]
        proof fn magic(x: int) -> (r: int)
            ensures r > x, r < x,  // contradictory ensures — trusted
        {
            unimplemented!()
        }

        proof fn test() {
            let r = magic(5);
            // r > 5 and r < 5 are both assumed — contradictory
            assert(false);
        }
    } => Err(err) => {
        assert!(err.errors.iter().find(|e| e.message.contains("vacuity check failed")).is_some());
    }
}
