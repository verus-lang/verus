#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] trait_poly verus_code! {
        use vstd::{prelude::*, vec::*};
        proof fn p<A: View>(x: A) -> (r: (A::V, A::V))
            ensures r.1 == x.view(),
        {
            (x.view(), x.view())
        }
        struct S {}
        impl View for S {
            type V = u8;
            closed spec fn view(&self) -> u8 { 7 }
        }
        fn test() {
            let mut v = Vec::new();
            v.push(true);
            proof {
                let x = p(S {});
                assert(x.0 < 256);
                assert(x.1 == 7);
                let y = p(v);
                assert(y.1[0]);
            }
        }
    } => Ok(_err) => { /* TODO: fix warning */ }
}

test_verify_one_file! {
    #[test] trait_poly_fail verus_code! {
        use vstd::{prelude::*, vec::*};
        proof fn p<A: View>(x: A) -> (r: (A::V, A::V))
            ensures r.1 == x.view(),
        {
            (x.view(), x.view())
        }
        struct S {}
        impl View for S {
            type V = int;
            closed spec fn view(&self) -> int { 7 }
        }
        fn test() {
            let mut v = Vec::new();
            v.push(true);
            proof {
                let x = p(S {});
                assert(x.0 == 7); // FAILS
                assert(x.1 == 7);
                let y = p(v);
                assert(y.1[0]);
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] assoc_poly_trait verus_code! {
        trait T<A> {
            type X;
            spec fn req_x(x: Self::X) -> bool;
            fn to_u64(x: Self::X) -> u64
                requires Self::req_x(x);
        }

        struct S {}

        impl T<bool> for S {
            type X = u8;
            spec fn req_x(x: u8) -> bool {
                x < 100
            }
            fn to_u64(x: u8) -> u64 { x as u64 }
        }

        impl T<u32> for S {
            type X = u16;
            spec fn req_x(x: u16) -> bool {
                x < 100
            }
            fn to_u64(x: u16) -> u64 { x as u64 }
        }

        fn test3(x: u8, y: u8)
            requires x < 100
        {
            let a: u64 = <S as T<bool>>::to_u64(x);
            let b: u64 = <S as T<u32>>::to_u64(x as u16);
            let c: u64 = <S as T<bool>>::to_u64(y); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] assoc_poly_different verus_code! {
        trait T<A> {
            type X;
            proof fn f() -> Self::X;
        }
        struct S {}
        impl T<u8> for S {
            type X = u8;
            proof fn f() -> u8 { 10 }
        }
        impl T<u16> for S {
            type X = u16;
            proof fn f() -> u16 { 20 }
        }
        proof fn test() {
            let x8 = <S as T<u8>>::f();
            let x16 = <S as T<u16>>::f();
            assert(x8 < 0x100);
            assert(x16 < 0x10000);
            assert(x16 < 0x100); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] assoc_poly_struct verus_code! {
        trait T {
            type X;
        }
        struct S<A> { a: A }
        impl T for S<u8> {
            type X = (bool, u16);
        }
        impl T for S<u32> {
            type X = u64;
        }
        impl<A: T> T for S<(A, A)> {
            type X = (A::X, bool);
        }
        trait TT<A> { type X; }
        struct Q {}
        impl<A> TT<A> for Q { type X = (bool, A); }

        impl TT<bool> for (Q, Q) { type X = (bool, bool); }

        proof fn id<A: T>(x: A::X) -> A::X {
            x
        }

        proof fn test() {
            let (b, u) = id::<S<u8>>((true, 10));
            assert(u < 0x10000);
            assert(u < 0x100); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] assoc_poly_struct_member verus_code! {
        trait T { type X; }
        struct S<A: T>(A::X);
        struct Q;
        impl T for Q { type X = u8; }
        proof fn test1(s: S<Q>) {
            assert(s.0 < 256);
        }
        proof fn test2(s: S<Q>) {
            assert(s.0 < 255); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] assoc_normalize verus_code! {
        trait T { type X; }
        struct S;
        impl T for S { type X = u8; }
        proof fn test1(x: <S as T>::X) {
            assert(x < 256);
        }
        proof fn test2(x: <S as T>::X) {
            assert(x < 255); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] assoc_self_bound verus_code! {
        trait T { type X; }
        struct S(<Self as T>::X) where Self: T;
        impl T for S { type X = u8; }
        proof fn test1(s: S) {
            assert(s.0 < 256);
        }
        proof fn test2(s: S) {
            assert(s.0 < 255); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
