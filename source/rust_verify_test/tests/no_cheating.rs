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
        use vstd::prelude::*;
        pub assume_specification<T, U> [Option::<(T, U)>::unzip](a: Option<(T, U)>) // FAILS
            -> (r: (Option<T>, Option<U>))
            ensures false
        ;
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_via_fn ["--no-cheating", "--no-verify"] => verus_code! {
        spec fn up(i: int) -> int
            decreases i via no_good
        {
            up(i + 1)
        }

        #[verifier::external_body]
        #[via_fn]
        proof fn no_good(i: int) // FAILS
        {}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_admit_exec_allows_no_decreases_clause ["--no-cheating"] => verus_code! {
        #[verifier::assume_termination]
        fn a(mut i: u64)
            requires i <= 10,
        {
            a(i)
        }
    } => Err(err) => assert_vir_error_msg(err, "`#[verifier::assume_termination]` not allowed with `--no-cheating`")
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_external_type_specification_ok ["--no-cheating"] => verus_code! {
        #[verifier::external]
        struct SomeStruct { t: u64 }

        #[verifier::external_type_specification]
        struct ExSomeStruct(SomeStruct);

        fn test() {
            let ss = SomeStruct { t: 5 };
            assert(ss.t == 5);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_external_type_specification_external_body ["--no-cheating"] => verus_code! {
        #[verifier::external]
        struct SomeStruct { t: u64 }

        #[verifier::external_type_specification]
        #[verifier::external_body]
        struct ExSomeStruct(SomeStruct);
    } => Err(err) => assert_vir_error_msg(err, "`external_type_specification` cannot be used with `external_body` when --no-cheating is enabled")
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_external_type_specification_drop ["--no-cheating"] => verus_code! {
        #[verifier::external]
        struct SomeStruct { t: u64 }

        #[verifier::external]
        impl Drop for SomeStruct {
            fn drop(&mut self) { }
        }

        #[verifier::external_type_specification]
        struct ExSomeStruct(SomeStruct);
    } => Err(err) => assert_vir_error_msg(err, "`external_type_specification` cannot be used for a type with a `Drop` impl when --no-cheating is enabled")
}

test_verify_one_file_with_options! {
    #[test] test_no_cheating_external_type_specification_drop_enum ["--no-cheating"] => verus_code! {
        #[verifier::external]
        enum SomeEnum { A, B }

        #[verifier::external]
        impl Drop for SomeEnum {
            fn drop(&mut self) { }
        }

        #[verifier::external_type_specification]
        struct ExSomeEnum(SomeEnum);
    } => Err(err) => assert_vir_error_msg(err, "`external_type_specification` cannot be used for a type with a `Drop` impl when --no-cheating is enabled")
}

test_verify_one_file! {
    #[test] test_external_type_specification_drop_and_external_body_without_no_cheating verus_code! {
        #[verifier::external]
        struct SomeStruct { t: u64 }

        #[verifier::external]
        impl Drop for SomeStruct {
            fn drop(&mut self) { }
        }

        #[verifier::external_type_specification]
        #[verifier::external_body]
        struct ExSomeStruct(SomeStruct);
    } => Ok(())
}
