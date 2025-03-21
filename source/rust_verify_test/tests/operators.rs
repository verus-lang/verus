#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_integer_using_trait_add verus_code! {
        use vstd::prelude::*;

        proof fn test_consistent_add(a: usize, b: usize, ret: usize)
        requires
            vstd::std_specs::ops::spec_add_requires(a, b),
        ensures
            vstd::std_specs::ops::spec_add_ensures(a, b, ret) <==> (ret == a + b)
        {}

        fn generic_add<T: core::ops::Add<Output = T>>(a: T, b: T) -> (ret: T)
        requires
            vstd::std_specs::ops::spec_add_requires(a, b),
        ensures
            vstd::std_specs::ops::spec_add_ensures(a, b, ret),
        {
            a + b
        }

        fn test(a: usize, b: usize)
        requires a + b < 10,
        {
            let c1 = a + b;
            let c2 = generic_add(a, b);
            assert(c1 == c2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_integer_trait_op_call_when_no_vstd verus_code! {
        use core::ops::Add;

        #[verifier::external_trait_specification]
        pub trait ExAddBasic<Rhs> {
            type ExternalTraitSpecificationFor: core::ops::Add<Rhs>;
            type Output;

            // No precondition (for test only).
            fn add(self, rhs: Rhs) -> (ret: Self::Output) where Self: Sized;
        }

        pub assume_specification[ <usize as core::ops::Add>::add ](a: usize, b: usize) -> (ret: usize);

        fn generic_add<T: core::ops::Add<Output = T>>(a: T, b: T) -> (ret: T)
        ensures
            call_ensures(<T as  core::ops::Add>::add, (a, b), ret),
        {
            a + b
        }

        fn test_trait_add_no_precondition(a: usize, b: usize)
        {
            let c2 = generic_add(a, b);
            let c3 = a.add(b);
            assert(call_ensures(usize::add, (a, b), c2));
            assert(call_ensures(usize::add, (a, b), c3));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_integer_op_different_from_generic_op_when_no_vstd_fails verus_code! {
        use core::ops::Add;

        pub closed spec fn spec_trait_add_ens<Lhs, Rhs, O>(lhs: Lhs, rhs: Rhs, ret: O) -> bool;

        #[verifier::external_trait_specification]
        pub trait ExAddBasic<Rhs> {
            type ExternalTraitSpecificationFor: core::ops::Add<Rhs>;
            type Output;
            // No precondition (for test only).
            fn add(self, rhs: Rhs) -> (ret: Self::Output) where Self: Sized
            ensures spec_trait_add_ens(self, rhs, ret);
        }

        pub assume_specification[ <usize as core::ops::Add>::add ](a: usize, b: usize) -> (ret: usize);

        fn generic_add<T: core::ops::Add<Output = T>>(a: T, b: T) -> (ret: T)
        ensures
            call_ensures(<T as  core::ops::Add>::add, (a, b), ret),
        {
            a + b
        }

        fn test_integer_add_diff_trait_add_operation1(a: usize, b: usize)
        requires a + b < 10
        {
            let c1 = a + b;
            assert(call_ensures(usize::add, (a, b), c1)); // FAILS
        }

        fn test_integer_add_diff_trait_add_operation2(a: usize, b: usize)
        requires a + b < 10
        {
            let c1 = a + b;
            let c2 = generic_add(a, b);
            let c3 = a.add(b);
            assert(c1 == c2 || c1 == c3); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
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
