#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_trait verus_code! {
        trait Tr {
            fn foo();
            fn bar();
        }

        struct X { }

        #[verifier::external]
        impl Tr for X {
            fn foo() { }
            fn bar() { }
        }

        #[verifier::external_fn_specification]
        fn ex_foo() {
            X::foo()
        }
    } => Err(err) => assert_vir_error_msg(err, "using external_fn_specification for this function requires you to specify all other functions for the same trait impl, but the method `bar` is missing")
}

test_verify_one_file! {
    #[test] test_trait_dupe verus_code! {
        trait Tr {
            fn foo();
            fn bar();
        }

        struct X { }

        #[verifier::external]
        impl Tr for X {
            fn foo() { }
            fn bar() { }
        }

        #[verifier::external_fn_specification]
        fn ex_foo() {
            X::foo()
        }

        #[verifier::external_fn_specification]
        fn ex_foo2() {
            X::foo()
        }

        #[verifier::external_fn_specification]
        fn ex_bar() {
            X::bar()
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate external_fn_specification for this method")
}

test_verify_one_file! {
    #[test] test_trait_dupe2 verus_code! {
        trait Tr {
            fn foo();
            fn bar();
        }

        struct X { }

        impl Tr for X {
            fn foo() { }
            fn bar() { }
        }

        #[verifier::external_fn_specification]
        fn ex_foo() {
            X::foo()
        }

        #[verifier::external_fn_specification]
        fn ex_bar() {
            X::bar()
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for this trait implementation")
}

test_verify_one_file! {
    #[test] test_trait_ok verus_code! {
        trait Tr {
            fn foo();
            fn bar();
        }

        struct X { }

        #[verifier::external]
        impl Tr for X {
            fn foo() { }
            fn bar() { }
        }

        #[verifier::external_fn_specification]
        fn ex_foo() {
            X::foo()
        }

        spec fn llama() -> bool;

        #[verifier::external_fn_specification]
        fn ex_bar()
            ensures llama(),
        {
            X::bar()
        }

        fn test() {
            X::bar();
            assert(llama());
        }
    } => Ok(())
}
