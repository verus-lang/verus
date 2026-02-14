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
        {
            x + y
        }

        fn caller() {
            let _ = example(1, 2); // precondition fails
        }
    } => Err(err) => {
        assert_help_error_msg(err.clone(), "note: Property 732");
        assert_json_func_details(&err, "crate::caller", |details| {
            details.failed_proof_notes.contains("Property 732")
        });
    }
}

test_verify_one_file_with_options! {
    #[test]
    test_json_proof_note_on_ensures ["--output-json"] => verus_code! {
        fn example(x: u64, y: u64) -> (z: u64)
            ensures
                #[verifier::proof_note("Property 732")]
                (z == x + y),
        {
            x
        }

        fn caller() {
            let _ = example(1, 2); // postcondition fails
        }
    } => Err(err) => {
        assert_help_error_msg(err.clone(), "note: Property 732");
        assert_json_func_details(&err, "crate::example", |details| {
            details.failed_proof_notes.contains("Property 732")
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
        assert_json_func_details(&err, "crate::caller", |details| {
            details.failed_proof_notes.contains("Statement known to be false")
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
        // TODO: This doesn't work, because `--no-cheating` mode prevents JSON output.
        // assert_json_func_details(&err, "crate::caller", |details| {
        //     details.failed_proof_notes.contains("Statement known to be false")
        // });
    }
}

fn assert_json_func_details(err: &TestErr, func: &str, predicate: impl Fn(&FuncDetails) -> bool) {
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

    assert!(predicate(&details));
}

#[derive(serde::Deserialize)]
pub struct FuncDetails {
    pub failed_proof_notes: std::collections::HashSet<String>,
}
