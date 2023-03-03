#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_not_yet_supported_1 code! {
        mod M1 { pub trait T1 {} }
        mod M2 {
            trait T2 {
                // need to add A: T1 to termination checking before supporting this
                fn f<A: crate::M1::T1>(a: &A) {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, ": trait generics")
}

test_verify_one_file! {
    #[test] test_not_yet_supported_8 code! {
        mod M1 {
            pub trait T<A> {
                fn f(&self, a: &A) {
                    builtin::no_method_body()
                }
            }
        }
        mod M2 {
            pub struct S<A> { a: A }
            // not yet supported: multiple implementations of same trait for single datatype:
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
    } => Err(err) => assert_vir_error_msg(err, ": multiple definitions of same function")
}

test_verify_one_file! {
    #[test] test_not_yet_supported_9 code! {
        mod M1 {
            pub trait T<A> {
                fn f(&self, a: A) -> A { builtin::no_method_body() }
            }
        }
        mod M2 {
            pub struct S {}
            // not yet supported: multiple implementations of same trait for single datatype:
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
    } => Err(err) => assert_vir_error_msg(err, ": multiple definitions of same function")
}

test_verify_one_file! {
    #[test] test_not_yet_supported_10 verus_code! {
        mod M1 {
            pub trait T {
                spec fn f(&self) -> bool;

                proof fn p(&self)
                    ensures exists|x: &Self| self.f() != x.f();
            }
        }

        mod M2 {
            #[verifier(external_body)] /* vattr */
            #[verifier(broadcast_forall)] /* vattr */
            proof fn f_not_g<A: crate::M1::T>()
                ensures exists|x: &A, y: &A| x.f() != y.f()
            {
            }
        }

        mod M3 {
            struct S {}
        }

        mod M4 {
            fn test() {
                assert(false);
            }
        }
    } => Err(err) => assert_error_msg(err, ": bounds on broadcast_forall function type parameters")
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
    #[test] test_ill_formed_8 code! {
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
                    builtin::requires(true); // no requires allowed
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "trait method implementation cannot declare requires/ensures")
}

test_verify_one_file! {
    #[test] test_ill_formed_9 code! {
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
                    builtin::ensures(true); // no ensures allowed
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "trait method implementation cannot declare requires/ensures")
}

test_verify_one_file! {
    #[test] test_mode_matches_1 code! {
        mod M1 {
            pub trait T1 {
                #[verifier::spec]
                fn f(&self) {
                    builtin::no_method_body()
                }
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
    #[test] test_mode_matches_2 code! {
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
                #[verifier::spec]
                fn f(&self) {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "function must have mode exec")
}

test_verify_one_file! {
    #[test] test_mode_matches_3 code! {
        mod M1 {
            pub trait T1 {
                fn f(#[verifier::spec] &self) {
                    builtin::no_method_body()
                }
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
    #[test] test_mode_matches_4 code! {
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
                fn f(#[verifier::spec] &self) {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "self has mode spec, function has mode exec")
}

test_verify_one_file! {
    #[test] test_mode_matches_5 code! {
        mod M1 {
            pub trait T1 {
                fn f(&self, #[verifier::spec] b: bool) {
                    builtin::no_method_body()
                }
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
    #[test] test_mode_matches_6 code! {
        mod M1 {
            pub trait T1 {
                fn f(&self, b: bool) {
                    builtin::no_method_body()
                }
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
    #[test] test_mode_matches_7 code! {
        mod M1 {
            pub trait T1 {
                #[verifier(returns(spec))] /* vattr */
                fn f(&self) -> bool {
                    builtin::no_method_body()
                }
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
    #[test] test_mode_matches_8 code! {
        mod M1 {
            pub trait T1 {
                fn f(&self) -> bool {
                    builtin::no_method_body()
                }
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T1 for S {
                #[verifier(returns(spec))] /* vattr */
                fn f(&self) -> bool {
                    true
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "function return value must have mode exec")
}

test_verify_one_file! {
    #[test] test_termination_1 code! {
        mod M1 {
            pub trait T {
                #[verifier::spec]
                fn f(&self) { builtin::no_method_body() }
            }

            #[verifier::spec]
            pub fn rec<A: T>(x: &A) {
                x.f();
            }
        }

        mod M2 {
            pub struct S {}

            impl crate::M1::T for S {
                #[verifier::spec]
                fn f(&self) {
                    crate::M1::rec(self);
                }
            }
        }

        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            #[verifier::proof]
            fn test() {
                let s = crate::M2::S {};
                s.f();
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a trait definition")
}

test_verify_one_file! {
    #[test] test_termination_2 code! {
        mod M1 {
            pub trait T {
                #[verifier::spec]
                fn f<A: T>(&self, x: &A);
            }
        }

        mod M2 {
            pub struct S {}

            impl crate::M1::T for S {
                #[verifier::spec]
                fn f<A: crate::M1::T>(&self, x: &A) {
                    x.f(x)
                }
            }
        }

        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            #[verifier::proof]
            fn test() {
                let s = crate::M2::S {};
                s.f(&s);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: trait generics") // note: the error message will change when this feature is supported
}

test_verify_one_file! {
    #[test] test_termination_3 code! {
        mod M1 {
            pub trait T {
                #[verifier::spec]
                fn f(&self) { builtin::no_method_body() }
            }
        }

        mod M2 {
            struct S {}

            impl crate::M1::T for S {
                #[verifier::spec]
                fn f(&self) {
                    self.f()
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] test_termination_4_ok code! {
        mod M1 {
            pub trait T {
                fn f(&self, x: &Self, n: u64) {
                    builtin::no_method_body()
                }
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
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_termination_4_fail_1a code! {
        mod M1 {
            pub trait T {
                fn f(&self, x: &Self, n: u64) {
                    builtin::no_method_body()
                }
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
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_termination_4_fail_1b code! {
        mod M1 {
            pub trait T {
                fn f(&self, x: &Self, n: u64) {
                    builtin::no_method_body()
                }
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
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_termination_4_fail_1c code! {
        mod M1 {
            pub trait T {
                fn f(&self, x: &Self, n: u64) {
                    builtin::no_method_body()
                }
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
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_termination_4_fail_2a code! {
        mod M1 {
            pub trait T {
                fn f(&self, x: &Self, n: u64) {
                    builtin::no_method_body()
                }
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
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_termination_4_fail_2b code! {
        mod M1 {
            pub trait T {
                fn f(&self, x: &Self, n: u64) {
                    builtin::no_method_body()
                }
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
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_1 code! {
        mod M1 {
            pub trait T {
                fn f(&self) {
                    builtin::requires(false);
                    builtin::no_method_body()
                }
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
    #[test] test_verify_2 code! {
        mod M1 {
            pub trait T {
                fn f(&self) {
                    builtin::ensures(false); // TRAIT
                    builtin::no_method_body()
                }
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
    #[test] test_verify_3 code! {
        mod M1 {
            pub trait T {
                #[verifier::spec]
                fn req(&self) -> bool { builtin::no_method_body() }
                fn f(&self) {
                    builtin::requires(self.req());
                    builtin::no_method_body()
                }
            }
        }
        mod M2 {
            pub struct S {}
            impl crate::M1::T for S {
                #[verifier::spec]
                fn req(&self) -> bool { false }
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
    #[test] test_verify_4 code! {
        mod M1 {
            pub trait T {
                #[verifier::spec]
                fn ens(&self) -> bool { builtin::no_method_body() }
                fn f(&self) {
                    builtin::ensures(self.ens()); // TRAIT
                    builtin::no_method_body()
                }
            }
        }
        mod M2 {
            struct S {}
            impl crate::M1::T for S {
                #[verifier::spec]
                fn ens(&self) -> bool { false }
                fn f(&self) {} // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_5_private code! {
        mod M1 {
            pub trait T {
                #[verifier::spec]
                fn req(&self) -> bool { builtin::no_method_body() }
                fn f(&self) {
                    builtin::requires(self.req());
                    builtin::no_method_body()
                }
            }
        }
        mod M2 {
            pub struct S {}
            impl crate::M1::T for S {
                #[verifier::spec]
                fn req(&self) -> bool { true }
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
    #[test] test_verify_5_publish code! {
        mod M1 {
            pub trait T {
                #[verifier::spec]
                fn req(&self) -> bool { builtin::no_method_body() }
                fn f(&self) {
                    builtin::requires(self.req());
                    builtin::no_method_body()
                }
            }
        }
        mod M2 {
            pub struct S {}
            impl crate::M1::T for S {
                #[verifier::spec]
                #[verifier(publish)] /* vattr */
                fn req(&self) -> bool { true }
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
    #[test] test_verify_6 code! {
        mod M1 {
            pub trait T<A> {
                #[verifier::spec]
                fn req(&self, a: A) -> bool { builtin::no_method_body() }

                #[verifier::spec]
                fn ens(&self, a: A, r: A) -> bool { builtin::no_method_body() }

                fn f(&self, a: &A) -> A {
                    builtin::requires(self.req(*a));
                    builtin::ensures(|ra: A| self.ens(*a, ra)); // TRAIT
                    builtin::no_method_body()
                }
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
                #[verifier::spec]
                fn req(&self, a: bool) -> bool {
                    a
                }

                #[verifier::spec]
                fn ens(&self, a: bool, r: bool) -> bool {
                    r == (a && self.x)
                }

                fn f(&self, a: &bool) -> bool {
                    *a && self.x
                }
            }
        }

        mod M5 {
            impl crate::M1::T<u64> for crate::M3::I {
                #[verifier::spec]
                fn req(&self, a: u64) -> bool {
                    self.x < a && a < 100
                }

                #[verifier::spec]
                fn ens(&self, a: u64, r: u64) -> bool {
                    self.x <= r && r < 100
                }

                fn f(&self, a: &u64) -> u64 {
                    self.x / 2 + a
                } // FAILS
            }
        }

        mod M6 {
            pub fn p<A, Z: crate::M1::T<A>>(a: &A, z: &Z) -> A {
                builtin::requires(z.req(*a));
                builtin::ensures(|rz: A| z.ens(*a, rz));
                z.f(a)
            }
        }

        mod M7 {
            fn test() {
                let i = crate::M3::I { x: 30 };
                crate::pervasive::print_u64(crate::M6::p(&10, &i)); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_multiple code! {
        mod M1 {
            pub trait T1 {
                fn f1(&self, u: u64) {
                    builtin::requires(u > 10);
                    builtin::no_method_body()
                }
            }
        }
        mod M2 {
            pub trait T2 {
                fn f2(&self, u: u64) {
                    builtin::requires(u > 20);
                    builtin::no_method_body()
                }
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
    #[test] test_generic_1_private code! {
        mod M1 {
            pub trait T<A> {
                #[verifier::spec]
                fn apple(&self, #[verifier::spec] b: A) -> bool {
                    builtin::no_method_body()
                }
            }
        }

        mod M2 {
            pub struct S<A, B>(pub A, pub B);
        }

        mod M3 {
            impl<C> crate::M1::T<(C, u16)> for crate::M2::S<bool, C> {
                #[verifier::spec]
                fn apple(&self, #[verifier::spec] b: (C, u16)) -> bool {
                    b.1 > 10
                }
            }
        }

        mod M4 {
            #[allow(unused_imports)] use crate::M1::T;
            #[verifier::proof]
            fn test() -> bool {
                builtin::ensures(|b: bool| b); // FAILS

                let i: u8 = 10;
                let s = crate::M2::S(true, i);
                let b: bool = s.apple((i, 20));
                b
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_generic_1_public_ok code! {
        mod M1 {
            pub trait T<A> {
                #[verifier::spec]
                fn apple(&self, #[verifier::spec] b: A) -> bool {
                    builtin::no_method_body()
                }
            }
        }

        mod M2 {
            pub struct S<A, B>(pub A, pub B);
        }

        mod M3 {
            impl<C> crate::M1::T<(C, u16)> for crate::M2::S<bool, C> {
                #[verifier::spec]
                #[verifier(publish)] /* vattr */
                fn apple(&self, #[verifier::spec] b: (C, u16)) -> bool {
                    b.1 > 10
                }
            }
        }

        mod M4 {
            #[allow(unused_imports)] use crate::M1::T;
            #[verifier::proof]
            fn test() -> bool {
                builtin::ensures(|b: bool| b);

                let i: u8 = 10;
                let s = crate::M2::S(true, i);
                let b: bool = s.apple((i, 20));
                b
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_generic_1_ok_markers code! {
        mod M1 {
            pub trait T<A: Sized> : Sized {
                #[verifier::spec]
                fn apple(&self, #[verifier::spec] b: A) -> bool {
                    builtin::no_method_body()
                }
            }
        }

        mod M2 {
            pub struct S<A: Sized, B: Sized>(pub A, pub B);

            impl<C: Sized> crate::M1::T<(C, u16)> for S<bool, C> {
                #[verifier::spec]
                #[verifier(publish)] /* vattr */
                fn apple(&self, #[verifier::spec] b: (C, u16)) -> bool {
                    b.1 > 10
                }
            }
        }

        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            #[verifier::proof]
            fn test() -> bool {
                builtin::ensures(|b: bool| b);

                let i: u8 = 10;
                let s = crate::M2::S(true, i);
                let b: bool = s.apple((i, 20));
                b
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_generic_1_fail code! {
        mod M1 {
            pub trait T<A> {
                #[verifier::spec]
                fn apple(&self, #[verifier::spec] b: A) -> bool {
                    builtin::no_method_body()
                }
                fn banana(&self, b: A) -> A {
                    builtin::no_method_body()
                }
            }
        }

        mod M2 {
            pub struct S<A, B>(pub A, pub B);

            impl<C> crate::M1::T<(C, u16)> for S<bool, C> {
                #[verifier::spec]
                fn apple(&self, #[verifier::spec] b: (C, u16)) -> bool {
                    b.1 > 10
                }
                fn banana(&self, b: (C, u16)) -> (C, u16) {
                    (b.0, 10)
                }
            }
        }

        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            #[verifier::proof]
            fn test() -> bool {
                builtin::ensures(|b: bool| b); // FAILS

                let i: u8 = 10;
                let s = crate::M2::S(true, i);
                let b: bool = s.apple((i, 5));
                b
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_generic_2 code! {
        mod M1 {
            pub trait T<A> {
                #[verifier::spec]
                fn apple(&self, #[verifier::spec] b: A) -> bool {
                    builtin::no_method_body()
                }
                fn banana(&self, b: A) -> A {
                    builtin::no_method_body()
                }
            }
        }

        mod M2 {
            pub struct S<A, B>(pub A, pub B);

            impl crate::M1::T<u8> for S<u16, u32> {
                #[verifier::spec]
                #[verifier(publish)]
                fn apple(&self, #[verifier::spec] b: u8) -> bool {
                    b > 10
                }
                fn banana(&self, b: u8) -> u8 {
                    b / 2
                }
            }
        }

        mod M3 {
            #[allow(unused_imports)] use crate::M1::T;
            #[verifier::proof]
            fn test() -> bool {
                builtin::ensures(|b: bool| b); // FAILS

                let s = crate::M2::S(10, 20);
                let b: bool = s.apple(5);
                b
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_generic_3 code! {
        mod M1 {
            pub trait T {
                #[verifier::spec]
                fn apple(&self, #[verifier::spec] b: bool) -> bool {
                    builtin::no_method_body()
                }

                fn banana(&self) {
                    builtin::requires(self.apple(true));
                    builtin::ensures(true);
                    builtin::no_method_body()
                }
            }
        }

        mod M2 {
            pub struct S<A, B>(pub A, pub B);
        }

        mod M3 {
            pub fn f1<A: crate::M1::T>(a: &A) {
                builtin::requires(a.apple(true));
                a.banana();
            }
        }

        mod M4 {
            impl crate::M1::T for crate::M2::S<bool, bool> {
                #[verifier::spec]
                #[verifier(publish)] /* vattr */
                fn apple(&self, #[verifier::spec] b: bool) -> bool {
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
                spec fn r<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self {
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
