#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test]
    test_json_proof_note_on_requires ["--output-json"] => verus_code! {
        fn example(x: u64, y: u64) -> (z: u64)
            requires
                #[verifier::proof_note("Property 732")]
                (x == y),
                #[verifier::proof_note("Label 451")]
                (x != y),
        {
            x + y
        }

        fn caller() {
            let _ = example(1, 2); // precondition "Property 732" fails
            let _ = example(3, 3); // precondition "Label 451" fails
        }
    } => Err(err) => {
        assert_help_error_msg(err.clone(), "note: Property 732");
        assert_help_error_msg(err.clone(), "note: Label 451");
        with_json_func_details(&err, "crate::caller", |details| {
            assert!(details.failed_proof_notes.contains("Property 732"));
            assert!(details.failed_proof_notes.contains("Label 451"));
        });
    }
}

test_verify_one_file_with_options! {
    #[test]
    test_json_proof_note_on_ensures ["--output-json"] => verus_code! {
        fn example(x: u64, y: u64) -> (z: u64)
            ensures
                // both postconditions fail
                #[verifier::proof_note("Property 732")]
                (z == x + y),
                #[verifier::proof_note("Label 451")]
                (z == x - y),
        {
            x
        }

        fn caller() {
            let _ = example(1, 2);
        }
    } => Err(err) => {
        assert_help_error_msg(err.clone(), "note: Property 732");
        assert_help_error_msg(err.clone(), "note: Label 451");
        with_json_func_details(&err, "crate::example", |details| {
            assert!(details.failed_proof_notes.contains("Property 732"));
            assert!(details.failed_proof_notes.contains("Label 451"));
        });
    }
}

test_verify_one_file_with_options! {
    #[test]
    test_json_proof_note_on_assert ["--output-json"] => verus_code! {
        fn caller() {
            assert(
                #[verifier::proof_note("Statement known to be false")]
                (1 > 2)
            ); // assertion fails
        }
    } => Err(err) => {
        assert_help_error_msg(err.clone(), "note: Statement known to be false");
        with_json_func_details(&err, "crate::caller", |details| {
            assert!(details.failed_proof_notes.contains("Statement known to be false"));
        });
    }
}

test_verify_one_file_with_options! {
    #[test]
    test_json_proof_note_on_assume_with_no_cheating ["--output-json", "--no-cheating"] =>
    verus_code! {
        fn caller() {
            assume(
                #[verifier::proof_note("Statement known to be false")]
                (1 > 2)
            ); // assumption fails
        }
    } => Err(err) => {
        assert_help_error_msg(err.clone(), "note: Statement known to be false");
        with_json_func_details(&err, "crate::caller", |details| {
            assert!(details.failed_proof_notes.contains("Statement known to be false"))
        });
    }
}

test_verify_one_file_with_options! {
    #[test]
    test_json_proof_note_on_assume_and_req_with_no_cheating ["--output-json", "--no-cheating"] =>
    verus_code! {
        fn func_with_precond(x: u64) -> u64
            requires
                #[verifier::proof_note("Precondition known to fail")]
                (x < 10),
        {
            2 * x
        }

        fn caller() {
            let _ = func_with_precond(42);
            assume(
                #[verifier::proof_note("Assumption forbidden by no-cheating")]
                (1 > 2)
            );
        }
    } => Err(err) => {
        assert_help_error_msg(err.clone(), "note: Assumption forbidden by no-cheating");
        assert_help_error_msg(err.clone(), "note: Precondition known to fail");
        with_json_func_details(&err, "crate::caller", |details| {
            assert!(details.failed_proof_notes.contains("Assumption forbidden by no-cheating"));
            assert!(details.failed_proof_notes.contains("Precondition known to fail"));
        });
    }
}

fn with_json_func_details(err: &TestErr, func: &str, body: impl Fn(&FuncDetails)) {
    let json = err.json_output.as_ref().expect("expected JSON summary output");

    dbg!(json);

    let func_details = json
        .get("func-details")
        .and_then(|v| v.as_object())
        .expect("`func-details` missing or not an object");

    let details_json =
        func_details.get(func).expect(&format!("func-details has no entry for `{func}`"));

    let details =
        serde_json::from_value(details_json.clone()).expect("failed to deserialize FuncDetails");

    body(&details);
}

#[derive(serde::Deserialize)]
pub struct FuncDetails {
    pub failed_proof_notes: std::collections::HashSet<String>,
}
