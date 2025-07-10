#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_integer_using_trait_add verus_code! {
        use vstd::prelude::*;
        use core::ops::Add;

        fn generic_add<T: Add<Output = T>>(a: T, b: T) -> (ret: T)
            requires
                call_requires(<T as Add>::add, (a, b))
            ensures
                call_ensures(<T as Add>::add, (a, b), ret)
        {
            a + b
        }

        fn test(a: usize, b: usize)
            requires
                a + b < 10,
        {
            let c1 = a + b;
            let c2 = generic_add(a, b);
            let c3 = a.add(b);
            assert(c1 == c2);
            assert(c1 == c3);
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

        fn test_integer_add_diff_trait_add_operation1(a: usize, b: usize)
            requires
                a + b < 10,
        {
            let c1 = a + b;
            assert(call_ensures(usize::add, (a, b), c1)); // FAILS
        }

        fn test_integer_add_diff_trait_add_operation2(a: usize, b: usize)
            requires
                a + b < 10,
        {
            let c1 = a + b;
            let c2 = generic_add(a, b);
            let c3 = a.add(b);
            assert(c1 == c2 || c1 == c3); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] test_partial_eq_overload verus_code! {
        use core::cmp::PartialEq;

        pub struct S(pub usize);

        #[verifier::external_trait_specification]
        pub trait ExPartialEqBasic<Rhs: ?Sized> {
            type ExternalTraitSpecificationFor: PartialEq<Rhs>;
            fn eq(&self, rhs: &Rhs) -> (ret: bool);
        }

        impl PartialEq<S> for S {
            fn eq(&self, rhs: &S) -> (ret: bool)
                ensures
                    ret <==> (self.0 != rhs.0)
            {
                self.0 != rhs.0
            }
        }

        fn test_usize_cmp(a: S, b: S) {
            let c2 = (a == b);
            assert(c1 == (a@ != b@)); //FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_cmp_usize_diff verus_code! {
        use core::cmp::PartialEq;

        #[verifier::external_trait_specification]
        pub trait ExPartialEqBasic<Rhs: ?Sized> {
            type ExternalTraitSpecificationFor: PartialEq<Rhs>;
            fn eq(&self, rhs: &Rhs) -> (ret: bool);
        }

        pub assume_specification[ <usize as PartialEq>::eq ](a: &usize, b: &usize) -> (ret: bool);

        fn test_usize_cmp(a: usize, b: usize) {
            let c1 = (a == b);
            let c2 = a.eq(&b);
            assert(c1 == c2); //FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_trait_add verus_code! {
        #[verifier::external_trait_specification]
        pub trait ExAddMethod<Rhs> {
            type ExternalTraitSpecificationFor: core::ops::Add<Rhs>;
            type Output;

            // Required method does not have Sized but we added it here to pass lifetime checker
            fn add(self, rhs: Rhs) -> (ret: Self::Output) where Self: Sized;
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

        pub struct S(pub usize);

        impl core::ops::Sub<S> for S {
            type Output = usize;
            fn sub(self, rhs: S) -> (ret: usize)
                ensures
                    ret == self.0 - rhs.0 - 10
            {
                assert(self.0 >= 20 && rhs.0 <= 10);
                self.0 - rhs.0 - 10
            }
        }

        impl vstd::std_specs::ops::SubSpecImpl<S> for S {
            open spec fn obeys_sub_spec() -> bool {
                true
            }
            open spec fn sub_spec(self, rhs: S) -> usize {
                (self.0 - rhs.0 - 10) as usize
            }
            open spec fn sub_req(self, rhs: S) -> bool {
                self.0 >= 20 && rhs.0 < 10
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_call_operator_trait_method verus_code! {
        use core::ops::Sub;
        use vstd::prelude::*;
        use vstd::std_specs::ops::*;
        struct S;

        impl Sub for S {
            type Output = S;
            fn sub(self, other: S) -> (ret: S) {
                self
            }
        }

        impl vstd::std_specs::ops::SubSpecImpl<S> for S {
            open spec fn obeys_sub_spec() -> bool {
                true
            }
            open spec fn sub_spec(self, rhs: S) -> S {
                self
            }
            open spec fn sub_req(self, rhs: S) -> bool {
                true
            }
        }

        // If it is a non-primitive type, it would work.
        fn test(x1: S, x2: S) {
            let ord2 = x1.sub(x2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_operator_not_implemented verus_code! {
        struct S;
        fn test()
        {
            let s1 = S;
            if s1 == s1 {}
        }
    } => Err(e) => assert_rust_error_msg(e, "binary operation `==` cannot be applied to type `S`")
}

test_verify_one_file! {
    #[test] test_eq_overload verus_code! {
        use vstd::prelude::*;
        use core::cmp::PartialEq;

        pub struct S {
            a: u8,
            b: usize,
            c: bool,
        }

        impl PartialEq for S {
            fn eq(&self, other: &S) -> (ret: bool)
                ensures
                    !ret
            {
                false
            }
        }

        impl vstd::std_specs::cmp::PartialEqSpecImpl for S {
            closed spec fn obeys_eq_spec() -> bool {
                false
            }

            closed spec fn eq_spec(&self, s: &S) -> bool {
                false
            }
        }

        fn test(s1: S, s2: S)
        {
            let c1 = (s1 == s2);
            assert(!c1);
            let c2 = (s1.eq(&s2));
            assert(!c2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_structural_eq verus_code! {
        use vstd::prelude::*;

        #[derive(PartialEq, Structural)]
        pub struct S {
            a: u8,
            b: usize,
            c: bool,
        }

        // This does not take effect since structural equality has higher priority than the trait spec.
        pub assume_specification[ S::eq ](lhs: &S, rhs: &S) -> (ret: bool)
            ensures
                ret == false,
        ;

        fn test(s1: S, s2: S)
            requires s1 == s2
        {
            let c = (s1 == s2);
            assert(c);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_arith verus_code! {
        use vstd::prelude::*;

        fn test_shl(u: u16) {
            use core::ops::Shl;
            let _ = u.shl(15u16);
            let _ = u.shl(16u16); // FAILS
        }

        fn test_shr(u: i16) {
            use core::ops::Shr;
            let _ = u.shr(15i16);
            let _ = u.shr(16i16); // FAILS
        }

        fn test_signed_div() {
            let x = 53i8 / 10i8;
            assert(x == 5);
            let x = (-53i8) / 10i8;
            assert(x == -5);
            let x = 53i8 / (-10i8);
            assert(x == -5);
            let x = (-53i8) / (-10i8);
            assert(x == 5);
            let x = (-128i8) / (-1i8); // FAILS
        }

        fn test_signed_mod() {
            let x = 53i8 % 10i8;
            assert(x == 3);
            let x = (-53i8) % 10i8;
            assert(x == -3);
            let x = 53i8 % (-10i8);
            assert(x == 3);
            let x = (-53i8) % (-10i8);
            assert(x == -3);
            let x = (-128i8) % (-1i8); // FAILS
        }
    } => Err(e) => assert_fails(e, 4)
}
