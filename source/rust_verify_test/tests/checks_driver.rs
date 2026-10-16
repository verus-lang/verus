// Tests for the verifier driver (rust_verify/src/verifier.rs).
// Each test exercises verifier code (a check, an error path or an encoding case) that no other test
// of the suite exercises; its comment names the source lines it covers.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Covers verifier.rs:860, 861, 869, 1603
test_verify_one_file_with_options! {
    #[test] funcs_spec_termination_timeout ["--output-json"] => verus_code! {
        use vstd::prelude::*;

        spec fn f(x: int) -> int;
        #[verifier::rlimit(0.0001)]
        spec fn h(x: int, y: int) -> int // FAILS
            decreases f(x), f(y), x
        {
            if x <= 0 { 0 } else { h(x - 1, y) }
        }
    } => Err(err) => {
        let mut msgs: Vec<String> = err.errors.iter().map(|e| e.message.clone()).collect();
        msgs.sort();
        assert_eq!(msgs, vec!["function body check: Resource limit (rlimit) exceeded; consider rerunning with --profile for more details".to_string()]);
        assert_fails(err.clone(), 1);
        assert_eq!(err.json_output.as_ref().unwrap()["verification-results"]["verified"], 0);
    }
}

// Covers verifier.rs:2989
test_verify_one_file! {
    #[test] propose_1_16850 verus_code! {
        use vstd::prelude::*;

        trait Tr { fn f(&self) -> impl Sized; }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: Verus does not yet support Opaque")
}
