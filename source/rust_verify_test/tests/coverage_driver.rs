// Branch-condition (MC/DC) coverage tests: the verifier driver, command line, filters, lifetimes and trait-conflict check (rust_verify).
// Each test's comment names the decisions (file:line) and the conditions (atoms, numbered from 0
// in source order) for which the test supplies an evaluation that no other test supplies, so that
// the condition is shown to independently change the decision's outcome. See
// COVERAGE-UNREACHABLE.md for the conditions that no test can cover.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Independence pair for rust_verify/src/trait_check.rs:335 atom 1; rust_verify/src/trait_check.rs:338 atom 1; rust_verify/src/trait_check_emit.rs:128 atom 1; rust_verify/src/trait_check_emit.rs:136 atom 1
test_verify_one_file_with_options! {
    #[test] b859_alloc_rc_confusion ["--crate-name=alloc"] => verus_code! {
        use vstd::prelude::*;

        pub mod rc { pub struct Rc<T, A> { pub v: T, pub w: A } }
        use rc::Rc;
        // (mk removed: constructing Rc panics at vir/src/user_defined_type_invariants.rs:124, see b859_alloc_rc_mk_panic.rs)
        proof fn lemma(r1: Rc<u8, u16>, r2: Rc<u8, u16>) requires r1.v == r2.v ensures r1.w == r2.w {}
    } => Err(err) => assert_vir_error_msgs(err, &["duplicate definitions with name `A17_V`:", "duplicate definitions with name `A17_V`:"])
}

// Independence pair for rust_verify/src/driver.rs:339 atom 1 `verifier.args.no_erasure_check`
test_verify_one_file_with_options! {
    #[test] cli_no_erasure_check ["--no-erasure-check"] => verus_code! {
        use vstd::prelude::*;

        spec fn sq(x: nat) -> nat { x * x }
        proof fn p() { assert(sq(7) == 49) by (compute_only); }
        fn f(x: u8) ensures x <= 255 {}
    } => Ok(())
}

// Independence pair for rust_verify/src/verifier.rs:1794 atom 2 `default_prover_failed_assert_ids....`
test_verify_one_file_with_options! {
    #[test] fail_expand_bitvector ["--expand-errors"] => verus_code! {
        use vstd::prelude::*;

        proof fn p(x: u8) {
            assert(x & 1 == 0) by (bit_vector); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// Independence pair for rust_verify/src/verifier.rs:860 atom 0 `is_first_check`; rust_verify/src/verifier.rs:1786 atom 2 `!any_timed_out`
test_verify_one_file! {
    #[test] rlimit_after_first_error verus_code! {
        use vstd::prelude::*;

        spec fn f(x: int) -> int;
        #[verifier::rlimit(0.001)]
        proof fn p(a: int, b: int, c: int) // FAILS
            requires forall|x: int| #[trigger] f(x) == f(x + 1) + 1,
        {
            assert(a == b); // FAILS
            assert(f(a) == f(a + 30) + 30 && f(b) == f(b + 20) + 20);
        }
    } => Err(err) => assert_fails(err, 2)
}
