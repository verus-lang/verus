#![feature(rustc_private)]
#[macro_use]
mod common;
use std::{collections::HashSet, iter::FromIterator};

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
        let property_732 = "Property 732".to_string();
        let label_451 = "Label 451".to_string();
        assert_help_error_msg(err.clone(), &format!("note: {property_732}"));
        assert_help_error_msg(err.clone(), &format!("note: {label_451}"));

        let all_labels = HashSet::from_iter([property_732, label_451]);

        // Details about `example`
        with_json_func_details(&err, "crate::example", |details| {
            assert!(details.obligation_proof_notes.is_empty());
            assert!(details.failed_proof_notes.is_empty());
        });

        // Details about `caller`
        with_json_func_details(&err, "crate::caller", |details| {
            assert_eq!(details.obligation_proof_notes, all_labels);
            assert_eq!(details.failed_proof_notes, all_labels);
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
        let property_732 = "Property 732".to_string();
        let label_451 = "Label 451".to_string();
        assert_help_error_msg(err.clone(), &format!("note: {property_732}"));
        assert_help_error_msg(err.clone(), &format!("note: {label_451}"));

        let all_labels = HashSet::from_iter([property_732, label_451]);

        // Details about `example`
        with_json_func_details(&err, "crate::example", |details| {
            assert_eq!(details.obligation_proof_notes, all_labels);
            assert_eq!(details.failed_proof_notes, all_labels);
        });

        // Details about `caller`
        with_json_func_details(&err, "crate::caller", |details| {
            assert!(details.obligation_proof_notes.is_empty());
            assert!(details.failed_proof_notes.is_empty());
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
        let label = "Statement known to be false".to_string();
        assert_help_error_msg(err.clone(), &format!("note: {label}"));

        let all_labels = HashSet::from_iter([label]);

        // Details about `caller`
        with_json_func_details(&err, "crate::caller", |details| {
            assert_eq!(details.obligation_proof_notes, all_labels);
            assert_eq!(details.failed_proof_notes, all_labels);
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
        let label = "Statement known to be false".to_string();
        assert_help_error_msg(err.clone(), &format!("note: {label}"));

        // let all_labels = HashSet::from_iter([label]);

        // Details about `caller`
        // TODO: This doesn't work, because `--no-cheating` mode prevents verification altogether.
        // with_json_func_details(&err, "crate::caller", |details| {
        //     assert_eq!(details.obligation_proof_notes, all_labels);
        //     assert_eq!(details.failed_proof_notes, all_labels);
        // });
    }
}

fn with_json_func_details(err: &TestErr, func: &str, body: impl FnOnce(&FuncDetails)) {
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
    pub obligation_proof_notes: HashSet<String>,
    pub failed_proof_notes: HashSet<String>,
}
