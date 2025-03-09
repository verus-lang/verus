#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] test_no_cheating_external_body ["--no-cheating"] => verus_code! {
        #[verifier::external_body] fn no_good() // FAILS
        {}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_external_body_trait ["--no-cheating"] => verus_code! {
        trait A {
            #[verifier::external_body] fn no_good(&self) // FAILS
            {}
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_external_body_trait_impl ["--no-cheating"] => verus_code! {
        trait A {
            fn no_good(&self) {}
        }

        struct S;

        impl A for S {
            #[verifier::external_body] fn no_good(&self) // FAILS
            {}
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_assume ["--no-cheating"] => verus_code! {
        proof fn test() {
            assume(1 + 1 == 3); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_admit ["--no-cheating"] => verus_code! {
        proof fn test() {
            admit(); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_assume_proof_block ["--no-cheating"] => verus_code! {
        fn test() {
            proof {
                assume(1 + 1 == 3); // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_admit_proof_block ["--no-cheating"] => verus_code! {
        fn test() {
            proof {
                admit(); // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_assume_spec ["--no-cheating"] => verus_code! {
        pub assume_specification<T, U> [Option::<(T, U)>::unzip](a: Option<(T, U)>) -> (r: (Option<T>, Option<U>))
            ensures false // FAILS
        ;
    } => Err(e) => assert_one_fails(e)
}
