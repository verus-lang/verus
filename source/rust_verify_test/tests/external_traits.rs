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
            fn f();
        }
        #[verifier::external_trait_specification]
        trait Ex1 {
            type ExternalTraitSpecificationFor: T;
            fn f();
        }
        #[verifier::external_trait_specification]
        trait Ex2 {
            type ExternalTraitSpecificationFor: T;
            fn f();
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate method")
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

test_verify_one_file! {
    #[test] test_trait4 verus_code! {
        #[verifier::external_trait_specification]
        pub trait ExIntoIterator {
            type ExternalTraitSpecificationFor: core::iter::IntoIterator;
        }

        #[verifier::external_trait_specification]
        pub trait ExPartialEq<Rhs: ?Sized> {
            type ExternalTraitSpecificationFor: core::cmp::PartialEq<Rhs>;
        }

        #[verifier::external_trait_specification]
        pub trait ExEq: PartialEq {
            type ExternalTraitSpecificationFor: core::cmp::Eq;
        }

        #[verifier::external_trait_specification]
        pub trait ExPartialOrd<Rhs: ?Sized>: PartialEq<Rhs> {
            type ExternalTraitSpecificationFor: core::cmp::PartialOrd<Rhs>;
        }

        #[verifier::external_trait_specification]
        pub trait ExOrd: Eq + PartialOrd {
            type ExternalTraitSpecificationFor: Ord;
        }

        #[verifier::external_type_specification]
        pub struct ExOrdering(core::cmp::Ordering);

        #[verifier::external_type_specification]
        #[verifier::external_body]
        #[verifier::reject_recursive_types_in_ground_variants(I)]
        pub struct ExPeekable<I: Iterator>(core::iter::Peekable<I>);

        #[verifier::external_trait_specification]
        pub trait ExIterator1 {
            type ExternalTraitSpecificationFor: core::iter::Iterator;
            type Item;
            fn count(self) -> usize where Self: Sized;
            fn cmp<I>(self, other: I) -> core::cmp::Ordering where Self: core::iter::Iterator, I: core::iter::IntoIterator<Item = <Self as core::iter::Iterator>::Item>, <Self as core::iter::Iterator>::Item: Ord, Self: Sized;
        }

        #[verifier::external_trait_specification]
        pub trait ExIterator2 {
            type ExternalTraitSpecificationFor: core::iter::Iterator;
            type Item;
            fn peekable(self) -> core::iter::Peekable<Self> where Self: Sized, Self: core::iter::Iterator requires false;
        }

        fn test2<A: Iterator>(a: A) {
            let x = a.count();
        }

        fn test3<A: Iterator>(a: A) {
            let y = a.peekable(); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_trait5 verus_code! {
        #[verifier::external]
        trait T {
            type X;
            fn f() -> Self::X;
        }

        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;
            type X;

            fn f() -> Self::X;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_trait_auto_import verus_code! {
        #[verifier::external]
        trait T {}

        #[verifier::external]
        impl T for bool {}

        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;
        }

        trait U {
            type X: T;
        }

        impl U for u8 {
            type X = S;
        }

        impl U for u16 {
            type X = [S; 3];
        }

        struct S;

        #[verifier::external]
        impl T for S where bool: T {}

        #[verifier::external]
        impl<A: T, const N: usize> T for [A; N] {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_trait_defaults verus_code! {
        #[verifier::external]
        trait T {
            fn d(u: u32) -> u32 { u }
            fn f(u: u32) -> u32;
        }

        #[verifier::external]
        impl T for bool {
            fn f(u: u32) -> u32 { u }
        }

        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;
            fn d(u: u32) -> (r: u32) requires u >= 100;
            fn f(u: u32) -> (r: u32) requires u >= 100;
        }
        impl T for u8 {
            fn f(u: u32) -> u32 { u }
        }
        fn test() {
            <bool as T>::d(100);
            <u8 as T>::d(99); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}
