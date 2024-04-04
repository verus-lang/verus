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

test_verify_one_file! {
    #[test] test_trait_not_ext verus_code! {
        trait T {
        }
        #[verifier::external_trait_specification]
        trait Ex {
            type ExternalTraitSpecificationFor: T;
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification")
}

test_verify_one_file! {
    #[test] test_trait_dup verus_code! {
        #[verifier::external]
        trait T {
        }
        #[verifier::external_trait_specification]
        trait Ex1 {
            type ExternalTraitSpecificationFor: T;
        }
        #[verifier::external_trait_specification]
        trait Ex2 {
            type ExternalTraitSpecificationFor: T;
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification")
}

test_verify_one_file! {
    #[test] test_trait_body verus_code! {
        #[verifier::external]
        trait T {
            fn f() {}
        }
        #[verifier::external_trait_specification]
        trait Ex {
            type ExternalTraitSpecificationFor: T;
            fn f() {}
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_trait_specification` functions cannot have bodies")
}

test_verify_one_file! {
    #[test] test_trait_no_assoc verus_code! {
        #[verifier::external]
        trait T {
            fn f() {}
        }
        #[verifier::external_trait_specification]
        trait Ex {
            fn f() {}
        }
    } => Err(err) => assert_vir_error_msg(err, "trait must declare a type ExternalTraitSpecificationFor")
}

test_verify_one_file! {
    #[test] test_trait_different_generics1 verus_code! {
        #[verifier::external]
        trait T<A, B> {
        }
        #[verifier::external_trait_specification]
        trait Ex<A, B> {
            type ExternalTraitSpecificationFor: T<B, A>;
        }
    } => Err(err) => assert_vir_error_msg(err, "expected generics to match")
}

test_verify_one_file! {
    #[test] test_trait_different_generics2 verus_code! {
        #[verifier::external]
        trait T<A> {
        }
        #[verifier::external_trait_specification]
        trait Ex<A: Copy> {
            type ExternalTraitSpecificationFor: T<A>;
        }
    } => Err(err) => assert_vir_error_msg(err, "external_trait_specification trait bound mismatch")
}

test_verify_one_file! {
    #[test] test_trait1 verus_code! {
        #[verifier::external]
        trait T {
            fn f(&self, q: &Self, b: bool) -> usize;
            type X;
        }
        #[verifier::external_trait_specification]
        trait Ex {
            type ExternalTraitSpecificationFor: T;
            fn f(&self, q: &Self, b: bool) -> (r: usize)
                requires b
                ensures r > 7
                ;
            type X;
        }
        fn test<A: T>(a: &A) {
            let i = a.f(a, true);
            assert(i > 7);
            let i = a.f(a, false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_trait2 verus_code! {
        #[verifier::external]
        trait T {
            fn f(&self, q: &Self, b: bool) -> usize;
            type X;
        }
        #[verifier::external_trait_specification(ExternalTraitSpecificationForAlt)]
        trait Ex {
            type ExternalTraitSpecificationForAlt: T;
            fn f(&self, q: &Self, b: bool) -> (r: usize)
                requires b
                ensures r > 7
                ;
            type X;
        }
        fn test<A: T>(a: &A) {
            let i = a.f(a, true);
            assert(i > 7);
            let i = a.f(a, false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_trait3 verus_code! {
        #[verifier::external]
        trait T {
            fn f(&self, q: &Self, b: bool) -> usize;
            type X;
        }
        #[verifier::external_trait_specification]
        trait Ex {
            type ExternalTraitSpecificationFor: T;
            fn f(&self, q: &Self, b: bool) -> (r: usize)
                requires b
                ensures r > 7 // TRAIT
                ;
            type X;
        }
        impl T for u8 {
            fn f(&self, q: &Self, b: bool) -> (r: usize) {
                assert(b);
                8
            }
            type X = u16;
        }
        impl T for u32 {
            fn f(&self, q: &Self, b: bool) -> (r: usize) {
                assert(b);
                6
            } // FAILS
            type X = u16;
        }
    } => Err(e) => assert_one_fails(e)
}
