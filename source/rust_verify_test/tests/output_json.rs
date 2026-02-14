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
    } => Err(err) => assert_help_error_msg(err, "note: Property 732")
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
    } => Err(err) => assert_help_error_msg(err, "note: Property 732")
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
    } => Err(err) => assert_help_error_msg(err, "note: Statement known to be false")
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
    } => Err(err) => assert_help_error_msg(err, "note: Statement known to be false")
}
