#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_supported_8 verus_code! {
        mod M1 {
            pub trait T<A> {
                fn f(&self, a: &A);
            }
        }
        mod M2 {
            pub struct S<A> { a: A }
        }
        mod M3 {
            impl crate::M1::T<u8> for crate::M2::S<u8> {
                fn f(&self, a: &u8) {}
            }
        }
        mod M4 {
            impl crate::M1::T<bool> for crate::M2::S<bool> {
                fn f(&self, a: &bool) {}
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_supported_9 verus_code! {
        mod M1 {
            pub trait T<A> {
                fn f(&self, a: A) -> A;
            }
        }
        mod M2 {
            pub struct S {}
            impl crate::M1::T<bool> for S {
                fn f(&self, a: bool) -> bool { !a }
            }
        }
        mod M3 {
            impl crate::M1::T<u64> for crate::M2::S {
                fn f(&self, a: u64) -> u64 { a / 2 }
            }
        }
        mod M4 {
            use crate::M1::T;
            fn test() {
                let s = crate::M2::S {};
                s.f(true);
                s.f(10);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ill_formed_7 code! {
        mod M1 {
            pub trait T1 {
                fn f(&self) {
                    builtin::no_method_body()
                }
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T1 for S {
                fn f(&self) {
                    builtin::no_method_body() // can't appear in implementation
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "no_method_body can only appear in trait method declarations")
}

test_verify_one_file! {
    #[test] test_ill_formed_8 verus_code! {
        mod M1 {
            pub trait T1 {
                fn f(&self);
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T1 for S {
                fn f(&self)
                    requires true // no requires allowed
                {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "trait method implementation cannot declare requires")
}

test_verify_one_file! {
    #[test] test_mode_matches_1 verus_code! {
        mod M1 {
            pub trait T1 {
                spec fn f(&self);
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T1 for S {
                fn f(&self) {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "function must have mode spec")
}

test_verify_one_file! {
    #[test] test_mode_matches_2 verus_code! {
        mod M1 {
            pub trait T1 {
                fn f(&self);
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T1 for S {
                closed spec fn f(&self) {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "function must have mode exec")
}

test_verify_one_file! {
    #[test] test_mode_matches_3 verus_code! {
        mod M1 {
            pub trait T1 {
                fn f(#[verifier::spec] &self);
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T1 for S {
                fn f(&self) {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "parameter must have mode spec")
}

test_verify_one_file! {
    #[test] test_mode_matches_4 verus_code! {
        mod M1 {
            pub trait T1 {
                fn f(&self);
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T1 for S {
                fn f(#[verifier::spec] &self) {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "parameter must have mode exec")
}

test_verify_one_file! {
    #[test] test_mode_matches_5 verus_code! {
        mod M1 {
            pub trait T1 {
                fn f(&self, #[verifier::spec] b: bool);
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T1 for S {
                fn f(&self, b: bool) {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "parameter must have mode spec")
}

test_verify_one_file! {
    #[test] test_mode_matches_6 verus_code! {
        mod M1 {
            pub trait T1 {
                fn f(&self, b: bool);
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T1 for S {
                fn f(&self, #[verifier::spec] b: bool) {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "parameter must have mode exec")
}

test_verify_one_file! {
    #[test] test_mode_matches_7 verus_code! {
        mod M1 {
            pub trait T1 {
                #[verifier::returns(spec)] /* vattr */
                fn f(&self) -> bool;
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T1 for S {
                fn f(&self) -> bool {
                    true
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "function return value must have mode spec")
}

test_verify_one_file! {
    #[test] test_mode_matches_8 verus_code! {
        mod M1 {
            pub trait T1 {
                fn f(&self) -> bool;
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T1 for S {
                #[verifier::returns(spec)] /* vattr */
                fn f(&self) -> bool {
                    true
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "function return value must have mode exec")
}

test_verify_one_file! {
    #[test] test_termination_1 verus_code! {
        mod M1 {
            pub trait T {
                spec fn f(&self);
            }

            pub closed spec fn rec<A: T>(x: &A) {
                x.f();
            }
        }

        mod M2 {
            pub struct S {}

            impl crate::M1::T for S {
                closed spec fn f(&self) {
                    crate::M1::rec(self);
                }
            }
        }

        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            proof fn test() {
                let s = crate::M2::S {};
                s.f();
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_2 verus_code! {
        mod M1 {
            pub trait T {
                spec fn f<A: T>(&self, x: &A);
            }
        }

        mod M2 {
            pub struct S {}

            impl crate::M1::T for S {
                closed spec fn f<A: crate::M1::T>(&self, x: &A) {
                    x.f(x)
                }
            }
        }

        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            proof fn test() {
                let s = crate::M2::S {};
                s.f(&s);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_3 verus_code! {
        mod M1 {
            pub trait T {
                spec fn f(&self);
            }
        }

        mod M2 {
            struct S {}

            impl crate::M1::T for S {
                closed spec fn f(&self) {
                    self.f()
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] test_termination_4_ok verus_code! {
        mod M1 {
            pub trait T {
                fn f(&self, x: &Self, n: u64);
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T for S {
                fn f(&self, x: &Self, n: u64) {
                    builtin::decreases(n);
                    if n > 0 {
                        self.f(x, n - 1);
                        x.f(self, n - 1);
                    }
                }
            }
        }
    } => Ok(err) => {
        assert!(err.warnings.iter().find(|x| x.message.contains("decreases checks in exec functions do not guarantee termination of functions with loops or of their callers")).is_some());
    }
}

test_verify_one_file! {
    #[test] test_termination_4_fail_1a verus_code! {
        mod M1 {
            pub trait T {
                fn f(&self, x: &Self, n: u64);
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T for S {
                fn f(&self, x: &Self, n: u64)
                {
                    builtin::decreases(0);
                    self.f(x, n - 1); // FAILS
                }
            }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(relevant_error_span(&err.errors[0].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
        assert!(relevant_error_span(&err.errors[1].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
    }
}

test_verify_one_file! {
    #[test] test_termination_4_fail_1b verus_code! {
        mod M1 {
            pub trait T {
                fn f(&self, x: &Self, n: u64);
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T for S {
                fn f(&self, x: &Self, n: u64) {
                    builtin::decreases(n);
                    self.f(x, n - 1); // FAILS
                }
            }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(relevant_error_span(&err.errors[0].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
        assert!(relevant_error_span(&err.errors[1].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
    }
}

test_verify_one_file! {
    #[test] test_termination_4_fail_1c verus_code! {
        mod M1 {
            pub trait T {
                fn f(&self, x: &Self, n: u64);
            }
        }
        mod M2 {
            #[allow(unused_imports)] use crate::M1::T;
            struct S {}
            impl crate::M1::T for S {
                fn f(&self, x: &Self, n: u64) {
                    builtin::decreases(n);
                    g(self, x, n - 1); // FAILS
                }
            }
            fn g(x: &S, y: &S, n: u64) {
                if 0 < n {
                    x.f(y, n - 1);
                }
            }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(relevant_error_span(&err.errors[0].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
        assert!(relevant_error_span(&err.errors[1].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
    }
}

test_verify_one_file! {
    #[test] test_termination_4_fail_2a verus_code! {
        mod M1 {
            pub trait T {
                fn f(&self, x: &Self, n: u64);
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T for S {
                fn f(&self, x: &Self, n: u64) {
                    builtin::decreases(0);
                    x.f(self, n - 1); // FAILS
                }
            }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(relevant_error_span(&err.errors[0].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
        assert!(relevant_error_span(&err.errors[1].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
    }
}

test_verify_one_file! {
    #[test] test_termination_4_fail_2b verus_code! {
        mod M1 {
            pub trait T {
                fn f(&self, x: &Self, n: u64);
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T for S {
                fn f(&self, x: &Self, n: u64) {
                    builtin::decreases(n);
                    x.f(self, n - 1); // FAILS
                }
            }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(relevant_error_span(&err.errors[0].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
        assert!(relevant_error_span(&err.errors[1].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
    }
}

test_verify_one_file! {
    #[test] test_verify_1 verus_code! {
        mod M1 {
            pub trait T {
                fn f(&self)
                    requires false;
            }
        }
        mod M2 {
            #[allow(unused_imports)] use crate::M1::T;
            struct S {}
            impl crate::M1::T for S {
                fn f(&self) {}
            }
            fn test() {
                let s = S {};
                s.f(); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_2 verus_code! {
        mod M1 {
            pub trait T {
                fn f(&self)
                    ensures false; // TRAIT
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T for S {
                fn f(&self) {} // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_3 verus_code! {
        mod M1 {
            pub trait T {
                spec fn req(&self) -> bool;
                fn f(&self)
                    requires self.req();
            }
        }
        mod M2 {
            pub struct S {}
            impl crate::M1::T for S {
                closed spec fn req(&self) -> bool { false }
                fn f(&self) {}
            }
        }
        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            fn test() {
                let s = crate::M2::S {};
                s.f(); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_4 verus_code! {
        mod M1 {
            pub trait T {
                spec fn ens(&self) -> bool;
                fn f(&self)
                    ensures self.ens(); // TRAIT
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T for S {
                closed spec fn ens(&self) -> bool { false }
                fn f(&self) {} // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_5_private verus_code! {
        mod M1 {
            pub trait T {
                spec fn req(&self) -> bool;
                fn f(&self)
                    requires self.req();
            }
        }
        mod M2 {
            pub struct S {}
            impl crate::M1::T for S {
                closed spec fn req(&self) -> bool { true }
                fn f(&self) {}
            }
        }
        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            fn test1(s: &crate::M2::S) {
                s.f(); // FAILS
            }
        }
        mod M4 {
            fn test2<A: crate::M1::T>(a: &A) {
                a.f(); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_verify_5_publish verus_code! {
        mod M1 {
            pub trait T {
                spec fn req(&self) -> bool;
                fn f(&self)
                    requires self.req();
            }
        }
        mod M2 {
            pub struct S {}
            impl crate::M1::T for S {
                open spec fn req(&self) -> bool { true }
                fn f(&self) {}
            }
        }
        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            fn test1(s: &crate::M2::S) {
                s.f();
            }
        }
        mod M4 {
            fn test2<A: crate::M1::T>(a: &A) {
                a.f(); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_6 verus_code! {
        mod M1 {
            pub trait T<A> {
                spec fn req(&self, a: A) -> bool;

                spec fn ens(&self, a: A, r: A) -> bool;

                fn f(&self, a: &A) -> (ra: A)
                    requires self.req(*a),
                    ensures self.ens(*a, ra); // TRAIT
            }
        }

        mod M2 {
            pub struct B {
                pub x: bool,
            }
        }

        mod M3 {
            pub struct I {
                pub x: u64,
            }
        }

        mod M4 {
            impl crate::M1::T<bool> for crate::M2::B {
                closed spec fn req(&self, a: bool) -> bool {
                    a
                }

                closed spec fn ens(&self, a: bool, r: bool) -> bool {
                    r == (a && self.x)
                }

                fn f(&self, a: &bool) -> bool {
                    *a && self.x
                }
            }
        }

        mod M5 {
            use builtin::*;
            impl crate::M1::T<u64> for crate::M3::I {
                closed spec fn req(&self, a: u64) -> bool {
                    self.x < a && a < 100
                }

                closed spec fn ens(&self, a: u64, r: u64) -> bool {
                    self.x <= r && r < 100
                }

                fn f(&self, a: &u64) -> u64 {
                    self.x / 2 + a
                } // FAILS
            }
        }

        mod M6 {
            pub fn p<A, Z: crate::M1::T<A>>(a: &A, z: &Z) -> (rz: A)
                requires z.req(*a)
                ensures z.ens(*a, rz)
            {
                z.f(a)
            }
        }

        mod M7 {
            fn test() {
                let i = crate::M3::I { x: 30 };
                vstd::pervasive::print_u64(crate::M6::p(&10, &i)); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_multiple verus_code! {
        mod M1 {
            use builtin::*;
            pub trait T1 {
                fn f1(&self, u: u64)
                    requires u > 10;
            }
        }
        mod M2 {
            use builtin::*;
            pub trait T2 {
                fn f2(&self, u: u64)
                    requires u > 20;
            }
        }
        mod M3 {
            pub struct S {}
        }
        mod M4 {
            impl crate::M1::T1 for crate::M3::S {
                fn f1(&self, u: u64) {}
            }
        }
        mod M5 {
            impl crate::M2::T2 for crate::M3::S {
                fn f2(&self, u: u64) {}
            }
        }
        mod M6 {
            fn test<A: crate::M1::T1 + crate::M2::T2>(a: &A) {
                a.f1(25);
                a.f2(25);
                a.f1(15);
                a.f2(15); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_generic_1_private verus_code! {
        mod M1 {
            pub trait T<A> {
                spec fn apple(&self, b: A) -> bool;
            }
        }

        mod M2 {
            pub struct S<A, B>(pub A, pub B);
        }

        mod M3 {
            use builtin::*;
            impl<C> crate::M1::T<(C, u16)> for crate::M2::S<bool, C> {
                closed spec fn apple(&self, b: (C, u16)) -> bool {
                    b.1 > 10
                }
            }
        }

        mod M4 {
            #[allow(unused_imports)] use crate::M1::T;
            proof fn test() -> (b: bool)
                ensures b // FAILS
            {
                let i: u8 = 10;
                let s = crate::M2::S(true, i);
                let b: bool = s.apple((i, 20));
                b
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_generic_1_public_ok verus_code! {
        mod M1 {
            pub trait T<A> {
                spec fn apple(&self, b: A) -> bool;
            }
        }

        mod M2 {
            pub struct S<A, B>(pub A, pub B);
        }

        mod M3 {
            use builtin::*;
            impl<C> crate::M1::T<(C, u16)> for crate::M2::S<bool, C> {
                open spec fn apple(&self, b: (C, u16)) -> bool {
                    b.1 > 10
                }
            }
        }

        mod M4 {
            #[allow(unused_imports)] use crate::M1::T;
            proof fn test() -> (b: bool)
                ensures b
            {
                let i: u8 = 10;
                let s = crate::M2::S(true, i);
                let b: bool = s.apple((i, 20));
                b
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_generic_1_ok_markers verus_code! {
        mod M1 {
            pub trait T<A: Sized> : Sized {
                spec fn apple(&self, b: A) -> bool;
            }
        }

        mod M2 {
            use builtin::*;
            pub struct S<A: Sized, B: Sized>(pub A, pub B);

            impl<C: Sized> crate::M1::T<(C, u16)> for S<bool, C> {
                open spec fn apple(&self, b: (C, u16)) -> bool {
                    b.1 > 10
                }
            }
        }

        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            proof fn test() -> (b: bool)
                ensures b
            {
                let i: u8 = 10;
                let s = crate::M2::S(true, i);
                let b: bool = s.apple((i, 20));
                b
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_generic_1_fail verus_code! {
        mod M1 {
            pub trait T<A> {
                spec fn apple(&self, b: A) -> bool;
                fn banana(&self, b: A) -> A;
            }
        }

        mod M2 {
            use builtin::*;
            pub struct S<A, B>(pub A, pub B);

            impl<C> crate::M1::T<(C, u16)> for S<bool, C> {
                closed spec fn apple(&self, b: (C, u16)) -> bool {
                    b.1 > 10
                }
                fn banana(&self, b: (C, u16)) -> (C, u16) {
                    (b.0, 10)
                }
            }
        }

        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            proof fn test() -> (b: bool)
                ensures b // FAILS
            {
                let i: u8 = 10;
                let s = crate::M2::S(true, i);
                let b: bool = s.apple((i, 5));
                b
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_generic_2 verus_code! {
        mod M1 {
            pub trait T<A> {
                spec fn apple(&self, b: A) -> bool;
                fn banana(&self, b: A) -> A;
            }
        }

        mod M2 {
            use builtin::*;
            pub struct S<A, B>(pub A, pub B);

            impl crate::M1::T<u8> for S<u16, u32> {
                open spec fn apple(&self, b: u8) -> bool {
                    b > 10
                }
                fn banana(&self, b: u8) -> u8 {
                    b / 2
                }
            }
        }

        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            proof fn test() -> (b: bool)
                ensures b // FAILS
            {
                let s = crate::M2::S(10, 20);
                let b: bool = s.apple(5);
                b
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_generic_3 verus_code! {
        mod M1 {
            pub trait T {
                spec fn apple(&self, b: bool) -> bool;

                fn banana(&self)
                    requires self.apple(true),
                    ensures true;
            }
        }

        mod M2 {
            pub struct S<A, B>(pub A, pub B);
        }

        mod M3 {
            pub fn f1<A: crate::M1::T>(a: &A)
                requires a.apple(true)
            {
                a.banana();
            }
        }

        mod M4 {
            impl crate::M1::T for crate::M2::S<bool, bool> {
                open spec fn apple(&self, b: bool) -> bool {
                    self.0 && self.1 && b
                }

                fn banana(&self) {
                }
            }
        }

        mod M5 {
            #[allow(unused_imports)] use crate::M1::T;
            fn test1() {
                let s = crate::M2::S(true, true);
                s.banana();
                crate::M3::f1(&s);
            }
        }

        mod M6 {
            #[allow(unused_imports)] use crate::M1::T;
            fn test2() {
                let s = crate::M2::S(true, false);
                s.banana(); // FAILS
            }
        }

        mod M7 {
            fn test3() {
                let s = crate::M2::S(true, false);
                crate::M3::f1(&s); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_self_ok verus_code! {
        mod M1 {
            pub trait T {
                spec fn r<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self;

                fn f<'a>(&'a self, x: &'a Self, b: bool) -> (r: &'a Self)
                    ensures
                        b ==> r === self,
                        !b ==> r === x;
            }

            fn p<A: T>(a1: &A, a2: &A) {
                let a3 = a1.f(a2, true);
                assert(a3 === a1);
            }
        }

        mod M2 {
            pub struct S(pub u8);

            impl crate::M1::T for S {
                closed spec fn r<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self {
                    if b { self } else { x }
                }

                fn f<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self {
                    let x = if b { self } else { x };
                    assert(x === self.r(x, b));
                    x
                }
            }
        }

        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            fn test() {
                let s1 = crate::M2::S(1);
                let s2 = crate::M2::S(2);
                let s3 = s1.f(&s2, true);
                assert(s1.0 === s3.0);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_self_fail verus_code! {
        mod M1 {
            pub trait T {
                fn f<'a>(&'a self, x: &'a Self, b: bool) -> (r: &'a Self)
                    ensures
                        b ==> r === self,
                        !b ==> r === x; // TRAIT
            }
        }

        mod M2 {
            fn p<A: crate::M1::T>(a1: &A, a2: &A) {
                let a3 = a1.f(a2, false);
                assert(a3 === a1); // FAILS
            }
        }

        mod M3 {
            pub struct S(pub u8);

            impl crate::M1::T for S {
                fn f<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self {
                    if b { self } else { self }
                } // FAILS
            }
        }

        mod M4 {
            #[allow(unused_imports)] use crate::M1::T;
            fn test() {
                let s1 = crate::M3::S(1);
                let s2 = crate::M3::S(2);
                let s3 = s1.f(&s2, false);
                assert(s1.0 === s3.0); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 3)
}
