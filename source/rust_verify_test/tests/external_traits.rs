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
    } => Err(err) => assert_vir_error_msg(err, "using assume_specification for this function requires you to specify all other functions for the same trait impl, but the method `bar` is missing")
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
    } => Err(err) => assert_vir_error_msg(err, "duplicate assume_specification for this method")
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

        uninterp spec fn llama() -> bool;

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
                6 // FAILS
            }
            type X = u16;
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file_with_options! {
    #[test] test_trait4 ["--disable-internal-test-mode"] => verus_code! {
        #[verifier::external_trait_specification]
        pub trait ExIntoIterator {
            type ExternalTraitSpecificationFor: core::iter::IntoIterator;
        }

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

test_verify_one_file! {
    #[test] test_trait_default_external_body_issue1307 verus_code! {
        #[verifier::external]
        fn some_external_fn() { }

        trait T {
            #[verifier(external_body)]
            fn f1() -> (ret: bool)
                ensures
                    !ret
            {
                some_external_fn();
                false
            }

            fn f2() -> bool {
                Self::f1()
            }
        }

        struct S;

        impl T for S { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_trait_add verus_code! {
        #[verifier::external_trait_specification]
        pub trait ExAddBasic<Rhs> {
            type ExternalTraitSpecificationFor: core::ops::Add<Rhs>;
            type Output;
        }

        pub open spec fn spec_add<Lhs, Rhs, Output>(lhs: Lhs, rhs: Rhs) -> Output;

        #[verifier::external_trait_specification]
        pub trait ExAddMethod<Rhs> {
            type ExternalTraitSpecificationFor: core::ops::Add<Rhs>;
            type Output;
            // Required method does not have Sized but we added it here to pass lifetime checker
            fn add(self, rhs: Rhs) -> (ret: Self::Output) where Self: Sized
            returns spec_add::<_, _, Self::Output>(self, rhs);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_trait_add2 verus_code! {
        pub open spec fn spec_add<Lhs, Rhs, Output>(lhs: Lhs, rhs: Rhs) -> Output;

        #[verifier::external_trait_specification]
        pub trait ExAddMethod<Rhs> {
            type ExternalTraitSpecificationFor: core::ops::Add<Rhs>;
            type Output;

            // Required method does not have Sized but we added it here to pass lifetime checker
            fn add(self, rhs: Rhs) -> (ret: Self::Output) where Self: Sized
            returns spec_add::<_, _, Self::Output>(self, rhs);
        }

        // lifetime should not add ?Sized for the imported add function.
        fn test_add<T: core::ops::Add<Output = T>> (lhs: T, rhs: T) -> T {
            lhs.add(rhs)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_operator_overload verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::ops::*;
        use vstd::std_specs::cmp::*;

        fn check_sub<Out, T: core::ops::Sub<Output = Out> + core::cmp::PartialOrd>(x: T, y: T) -> (ret: Option<Out>)
            requires
                obeys_comparison_model::<T, T>(),
                vstd::std_specs::cmp::spec_gt(&x, &y) ==> spec_sub_requires(x, y)
            ensures
                ret.is_some() == vstd::std_specs::cmp::spec_gt(&x, &y),
                ret.is_some() ==> spec_sub_ensures(x, y, ret.unwrap()),
        {
            if x > y {
                assert(obeys_comparison_model::<T, T>() ==> spec_gt(&x, &y));
                Some(x - y)
            } else {
                None
            }
        }

        fn check_sub_u8(x: u8, y: u8)
        {
            let out = check_sub(x, y);
            assert(out.is_some() ==> (x >= y));
        }

        impl SpecPartialEqOp<A> for A {
            open spec fn spec_partial_eq(&self, rhs: &A) -> bool {
                self.0 == rhs.0
            }
        }

        #[derive(PartialEq)]
        struct A(pub usize);

        impl SpecSubOp<A> for A {
            type Output = usize;
            open spec fn spec_sub_requires(lhs: A, rhs: A) -> bool {
                lhs.0 >= 20 && rhs.0 < 10
            }

            open spec fn spec_sub_ensures(lhs: A, rhs: A, ret: usize) -> bool {
                ret == lhs.0 - rhs.0 - 10
            }
        }
        impl core::ops::Sub<A> for A {
            type Output = usize;
            fn sub(self, rhs: A) -> usize {
                assert(self.0 >= 20 && rhs.0 <= 10);
                self.0 - rhs.0 - 10
            }
        }

        impl SpecPartialOrdOp<A> for A {
            open spec fn spec_partial_cmp(&self, rhs: &A) -> Option<core::cmp::Ordering> {
                if self.0 > 30 && rhs.0 < 9 {
                    Some(core::cmp::Ordering::Greater)
                } else if self.0 == rhs.0 {
                    Some(core::cmp::Ordering::Equal)
                } else {
                    None
                }
            }
            proof fn lemma_cmp_eq_no_logic_err(&self, rhs: &A) {}
        }

        impl core::cmp::PartialOrd<A> for A {
            fn partial_cmp(&self, rhs: &A) -> Option<core::cmp::Ordering>{
                if self.0 > 30 && rhs.0 < 9 {
                    Some(core::cmp::Ordering::Greater)
                } else if self.0 == rhs.0  {
                    Some(core::cmp::Ordering::Equal)
                } else {
                    None
                }
            }
        }

        fn check_sub_special()
        {
            let a1 = A(30);
            let a2 = A(9);
            if a1 > a2 {
                assert(a1.0 > 30);
            }
            let res = a1 - a2;
            assert(res == 11);

        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] test_call_operator_trait_method verus_code! {
        use core::ops::Sub;
        use vstd::prelude::*;
        use vstd::std_specs::ops::*;
        struct A;
        impl SpecSubOp<A> for A {
            type Output = A;
            open spec fn spec_sub_requires(lhs: A, other: A) -> bool {
                true
            }
            open spec fn spec_sub_ensures(lhs: A, other: A, ret: A) -> bool {
                true
            }
        }
        impl Sub for A {
            type Output = A;
            fn sub(self, other: A) -> (ret: A)
            {
                proof{
                    broadcast use axiom_sub;
                }
                self
            }
        }
        // If it is a non-primitive type, it would work.
        fn test(x1: A, x2: A) {
            let ord2 = x1.sub(x2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_operator_overload_failed_precondition verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::ops::*;
        use vstd::std_specs::cmp::*;
        fn check_add<Out, T: core::ops::Sub<Output = Out> + core::cmp::PartialOrd>(x: T, y: T) -> (ret: Option<Out>)
            ensures obeys_comparison_model::<T, T>() ==>
                vstd::std_specs::cmp::spec_ge(&x, &y) ==> ret.is_some() && spec_sub_ensures(x, y, ret.unwrap()),
        {
            if x >= y {
                Some(x - y) // FAILS
            } else {
                None
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_operator_not_implemented verus_code! {
        struct A;
        fn test()
        {
            let a1 = A;
            if a1 == a1 {}
        }
    } => Err(e) => assert_rust_error_msg(e, "binary operation `==` cannot be applied to type `A`")
}
