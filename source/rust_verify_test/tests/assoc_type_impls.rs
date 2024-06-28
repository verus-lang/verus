#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] trait_poly verus_code! {
        use vstd::{prelude::*};
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
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_poly_fail verus_code! {
        use vstd::{prelude::*};
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
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

fn trait_assoc_type_bound_code(pass: bool) -> String {
    (verus_code! {
        trait A {
            spec fn a(&self) -> bool;
        }
        trait B {
            type T: A;

            spec fn req(t: Self::T) -> bool;

            proof fn foo(t: Self::T)
                requires Self::req(t),
                ensures t.a(); // FAILS
        }
    }) + (if pass {
        verus_code_str! {
            impl A for bool {
                spec fn a(&self) -> bool {
                    *self
                }
            }
        }
    } else {
        verus_code_str! {
            impl A for bool {
                spec fn a(&self) -> bool {
                    !*self
                }
            }
        }
    }) + verus_code_str! {
        struct BB { }
        impl B for BB {
            type T = bool;

            spec fn req(t: Self::T) -> bool { t }

            proof fn foo(t: Self::T) { }
        }
    }
}

test_verify_one_file! {
    #[test] trait_assoc_type_bound_pass trait_assoc_type_bound_code(true) => Ok(())
}

test_verify_one_file! {
    #[test] trait_assoc_type_bound_fail trait_assoc_type_bound_code(false) => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] trait_assoc_type_bound_generic verus_code! {
        trait A {
            spec fn a(&self) -> bool;
        }
        trait B {
            type T: A;

            spec fn ens(t: Self::T) -> bool;

            proof fn foo(t: Self::T)
                requires t.a(),
                ensures Self::ens(t);
        }

        proof fn bar<BB: B>(t: BB::T)
            requires t.a(),
            ensures BB::ens(t),
        {
            BB::foo(t);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_assoc_type_bound_self verus_code! {
        trait A {
            spec fn a(&self) -> bool;
        }
        trait B where Self: A {
            spec fn b(&self) -> bool;
        }
        impl A for bool {
            spec fn a(&self) -> bool { *self }
        }
        impl B for bool {
            spec fn b(&self) -> bool { self.a() }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_assoc_type_bound_lifetimes verus_code! {
        trait U<'a> {
            spec fn a(&self) -> bool;
        }
        trait T<'a> {
            type X: U<'a>;

            spec fn b(&self) -> Self::X;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_assoc_type_bound_no_lifetimes verus_code! {
        trait U {
            spec fn a(&self) -> bool;
        }
        trait T {
            type X: U;

            spec fn b(&self, x: Self::X) -> bool;
        }
        struct S;
        impl U for bool {
            spec fn a(&self) -> bool { true }
        }
        impl T for S {
            type X = bool;

            spec fn b(&self, x: bool) -> bool {
                x.a()
            }
        }
        proof fn test1(s: S)
        {
            assert(s.b(false));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_assoc_type_bound_inner_lifetimes verus_code! {
        pub trait T<'x> {
            type One<'a>;
            type Two<'b, 'c>;

            fn f<'a>(x: &<Self as T<'x>>::Two<'static, 'a>);
            fn g<'a>(x: &'a bool);
        }

        impl<'x> T<'x> for bool {
            type One<'a> = &'a bool;

            type Two<'b, 'c> = bool;

            fn f<'a>(x: &<Self as T<'x>>::Two<'static, 'a>) {}
            fn g<'a>(x: &'a bool) {}
        }

        fn test<'a>(x: &'a bool, y: &'static bool) {
            <bool as T<'a>>::g(x);
            <bool as T<'a>>::g(y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_assoc_type_bound_axiom verus_code! {
        trait Q {}

        trait T<M: Q> {
            spec fn f() -> int;
        }

        struct S<A>(A);

        impl<M: Q, A: T<M>> T<M> for S<A> {
            spec fn f() -> int { 3 }
        }

        trait U<M: Q> {
            type X: T<M>;
        }

        proof fn test2<M: Q, Z: U<M>>() {
            assert(<S<Z::X> as T<M>>::f() == 3);
            assert(<S<Z::X> as T<M>>::f() == 4); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] trait_typ_equality1 verus_code! {
        trait T {
            type X;
            type Y: Copy;
            spec fn f(x: &Self::X, y: &Self::Y) -> Self::X {
                *x
            }
            fn g(x: &Self::X, y: &Self::Y) -> Self::Y {
                *y
            }
        }

        impl T for bool {
            type X = u8;
            type Y = u16;
            spec fn f(x: &Self::X, y: &Self::Y) -> Self::X {
                (*x + *y) as u8
            }
            fn g(x: &Self::X, y: &Self::Y) -> (r: Self::Y)
                ensures r == *x as u16 + *y / 2
            {
                *x as u16 + *y / 2
            }
        }

        spec fn s1<A: T<X = u8>>(y: A::Y) -> u8 {
            A::f(&3u8, &y)
        }

        spec fn s2<A: T<X = u8>>(y: A::Y) -> u8 {
            A::f(&3u8, &y) / 2
        }

        proof fn test1<A: T<X = u8>>(y: A::Y) {
            assert(s1::<A>(y) == A::f(&3u8, &y));
        }

        fn test2() {
            assert(s1::<bool>(7u16) == <bool as T>::f(&3u8, &7u16));
            assert(s1::<bool>(7u16) == 10u8);
            assert(s2::<bool>(7u16) == 5u8);
            let r = <bool as T>::g(&3u8, &7u16);
            assert(r == 6u8);
            assert(r == 7u8); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] trait_typ_equality_struct verus_code! {
        trait T {
            type X;
            type Y;
        }

        struct S<A: T<X = u8>> {
            x: A::X,
        }
        impl T for bool {
            type X = u8;
            type Y = u16;
        }
        proof fn test() {
            let s: S<bool> = S { x: 10u8 };
            assert(s.x == 10);
            assert(s.x == 11); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] trait_typ_equality_broadcast verus_code! {
        trait T {
            type X;
            type Y;
        }

        spec fn p<A>(a: A) -> bool;
        spec fn q<A, B>(a: A, b: B) -> bool { true }

        #[verifier::external_body]
        proof fn p_u8(u: u8)
            ensures p(u)
        {
        }

        broadcast proof fn b<A: T<X = u8>>(x: A::X, a: A)
            ensures #[trigger] q(a, x) && p(x)
        {
            p_u8(x);
        }

        impl T for u16 {
            type X = u8;
            type Y = i8;
        }

        impl T for u32 {
            type X = u64;
            type Y = i64;
        }

        proof fn test() {
            broadcast use b;
            assert(q(5u16, 10u8));
            assert(p(10u8));
            assert(q(5u32, 11u8));
            assert(p(11u8)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] trait_typ_equality_dispatch_spec verus_code! {
        trait U { type X; }
        impl U for char { type X = u8; }
        impl U for bool { type X = u16; }

        trait T { spec fn f() -> int; }
        impl<A: U<X = u8>> T for A { spec fn f() -> int { 100 } }
        impl T for bool { spec fn f() -> int { 200 } }

        proof fn test() {
            assert(<char as T>::f() == 100);
            assert(<bool as T>::f() == 200);
            assert(<char as T>::f() == 200); // FAILS
            assert(<bool as T>::f() == 100);
            assert(false);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] trait_typ_equality_dispatch_proof verus_code! {
        trait U { type X; }
        impl U for char { type X = u8; }
        impl U for bool { type X = u16; }

        trait T { proof fn f() -> int; }
        impl<A: U<X = u8>> T for A { proof fn f() -> (r: int) ensures r == 100 { 100 } }
        impl T for bool { proof fn f() -> (r: int) ensures r == 200 { 200 } }

        proof fn test() {
            let x = <char as T>::f();
            assert(x == 100);
            let x = <bool as T>::f();
            assert(x == 200);
            let x = <char as T>::f();
            assert(x == 200); // FAILS
            let x = <bool as T>::f();
            assert(x == 100);
            assert(false);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] trait_typ_bound_no_dispatch verus_code! {
        trait R {}
        impl R for u8 {}
        trait T {
            spec fn f() -> int;
        }
        trait U {
            type X;
        }
        impl<A: U> T for A where A::X: R { spec fn f() -> int { 100 } }
        impl U for char { type X = u8; }
        impl U for bool { type X = u16; }
        impl T for bool { spec fn f() -> int { 200 } }

        proof fn test() {
            assert(<char as T>::f() == 100);
            assert(<bool as T>::f() == 200);
            assert(<char as T>::f() == 200);
            assert(<bool as T>::f() == 100);
            assert(false);
        }
    } => Err(err) => assert_rust_error_msg(err, "conflicting implementations")
}

test_verify_one_file! {
    #[test] trait_typ_bound_prune_ok verus_code! {
        pub trait T {
            spec fn f();
        }

        pub trait U {
            type X: T;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_assoc_type_bound_mutual_bounds_0 verus_code! {
        trait A: B {
            spec fn a(&self) -> Self::AT;
        }

        trait B: A {
            spec fn b(&self) -> Self::BT;
        }
    } => Err(err) => assert_rust_error_msg(err, "cycle detected when computing the super predicates of `A`")
}

test_verify_one_file! {
    #[test] trait_assoc_type_bound_mutual_bounds_1 verus_code! {
        trait A where Self: B {
            spec fn a(&self) -> Self::AT;
        }

        trait B where Self: A {
            spec fn b(&self) -> Self::BT;
        }
    } => Err(err) => assert_rust_error_msg(err, "cycle detected when computing the super predicates of `A`")
}

test_verify_one_file! {
    #[test] trait_assoc_type_bound_mutual_bounds_2 verus_code! {
        trait A {
            type AT: B;

            spec fn a(v: Self::AT) -> bool;
        }

        trait B {
            type BT: A;

            spec fn b(v: Self::BT) -> bool;
        }

        impl A for bool {
            type AT = bool;

            spec fn a(v: Self::AT) -> bool {
                bool::b(v)
            }
        }

        impl B for bool {
            type BT = bool;

            spec fn b(v: Self::BT) -> bool {
                bool::a(v)
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition, which may result in nontermination")
}

test_verify_one_file! {
    #[test] view_ref_unsized verus_code! {
        // https://github.com/verus-lang/verus/issues/1104
        use vstd::prelude::*;
        fn id<T: View>(t: T) -> T {
            t
        }
        fn test() {
            let bytes: [u8; 4] = [0, 0, 0, 0];
            let byte_slice: &[u8] = bytes.as_slice();
            id(byte_slice);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assoc_equality_lifetime verus_code! {
        // https://github.com/verus-lang/verus/issues/1130
        trait T<J, K> {
            type X;
            fn f() -> Self::X;
        }

        fn test<A, J, K, B: T<J, K, X = A>>(a: A, b: B) -> (A, A) {
            (a, B::f())
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] supertrait_assoc_type_lifetime verus_code! {
        // https://github.com/verus-lang/verus/issues/1132
        enum E<A, B> {
            Ok(A),
            Err(B),
        }

        trait T {
            type X;
            spec fn foo(&self) -> E<Self::X, ()>;
        }

        trait U: T {}

        proof fn test<A: U>(x: (A, )) {
            match x.0.foo() {
                E::Ok(_) => {}
                E::Err(_) => {}
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] supertrait_assoc_type_lifetime2 verus_code! {
        // https://github.com/verus-lang/verus/issues/1144
        pub trait T {
            type X;
        }

        pub trait U: T {
        }

        impl T for u8 {
            type X = u8;
        }

        impl U for u8 {
        }

        pub struct Q<A: U>(pub A);

        fn test1() -> Q<u8> {
            Q::<u8>(0)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] supertrait_assoc_type_lifetime3 verus_code! {
        // https://github.com/verus-lang/verus/issues/1155
        trait T: Copy {}
        trait U: T {}
        trait V<A> { fn f(a: A) -> (A, A); }

        struct S<A>(A);

        impl<A: U> V<A> for S<A> {
            fn f(a: A) -> (A, A) { (a, a) }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] wildcard_assoc_type_lifetime verus_code! {
        // https://github.com/verus-lang/verus/issues/1158
        struct S<A>(A);

        trait Foo {
            type T<'a>;

            fn foo<'a>(x: Self::T<'a>) -> S<Self::T<'a>> {
                S(x)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assoc_type_lifetime_for verus_code! {
        // https://github.com/verus-lang/verus/issues/1161
        pub trait Foo {
            type T<'a>;
        }

        pub trait From<T> {}

        pub trait Mapper<S: From<Self::U>> {
            type U: From<S>;
        }

        pub struct MapFoo<F, M>(F, M);

        impl<F, M> Foo for MapFoo<F, M> where
            F: Foo,
            for <'a>M: Mapper<F::T<'a>>,
            for <'a>F::T<'a>: From<<M as Mapper<F::T<'a>>>::U>,
            for <'a><M as Mapper<F::T<'a>>>::U: From<F::T<'a>>,
        {
            type T<'a> = <M as Mapper<F::T<'a>>>::U;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assoc_type_lifetime_for_rename verus_code! {
        // https://github.com/verus-lang/verus/issues/1161
        pub trait Bar {
            type U<'a>;
        }

        pub trait Foo<S>
            where
                S: for<'b> Bar<U<'b> = Self::T<'b>>,
        {
            type T<'c>;
            fn foo_<'b>(&self, o: Self::T<'b>);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assoc_type_lifetime_for_syntax verus_code! {
        // https://github.com/verus-lang/verus/issues/1161
        pub trait T {
            type X;
        }

        trait U {
            type Y<'a>;
        }

        struct S<A>(A);

        impl<A> T for S<A> where A: U, for<'a> A::Y<'a>: T {
            type X = S<A>;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assoc_type_lifetime_equality_syntax verus_code! {
        // https://github.com/verus-lang/verus/issues/1161
        trait T {
            type X<'a>;
            fn f<'a>(s: Self::X<'a>);
        }

        struct S<A>(A);

        impl<A> S<A> where
            for<'a> A: T<X<'a> = &'a [u8]>,
        {
            fn f<'a>(&self, s: &'a [u8]) {
                A::f(s)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assoc_type_lifetime_trait_impl_worklist verus_code! {
        // https://github.com/verus-lang/verus/issues/1161
        trait Foo
        {
            type R<'a>;
            fn foo<'a>(&self, s: &'a [u8]) -> Self::R<'a>;
        }

        trait Bar<Other>
        where
            Self: Foo,
            Other: Foo,
        {
            fn bar(&self, other: &Other);
        }

        impl<U1, U2, V1, V2> Bar<Pair<U2, V2>> for Pair<U1, V1>
        where
            U1: Foo,
            U2: for<'a> Foo<R<'a> = ()>,
            V1: Foo,
            V2: Foo,
        {
            fn bar(&self, c: &Pair<U2, V2>) {
            }
        }


        struct Pair<S, T>(S, T);

        impl<S, T> Foo for Pair<S, T>
        where
            S: Foo,
            T: Foo,
        {
            type R<'a> = T::R<'a>;
            fn foo<'a>(&self, s: &'a [u8]) -> Self::R<'a> {
                self.1.foo(s)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mention_external_trait_with_assoc_type verus_code! {
        use vstd::prelude::*;
        fn foo<A: IntoIterator>(a: &A) {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lifetime_generate_alias_infer verus_code! {
        // test lifetime_generate TyKind::Alias case that was normalizing to TyKind::Infer
        #[verifier::external]
        struct S<T>(T);

        #[verifier(external_type_specification)]
        #[verifier(external_body)]
        #[verifier::accept_recursive_types(T)]
        struct ExS<T>(S<T>);

        pub trait DeepView {
            type V;
        }

        struct W<T>(T);
        impl<T: DeepView> DeepView for S<T> {
            type V = W<T::V>;
        }

        #[allow(unconditional_recursion)]
        #[verifier(external_body)]
        fn new_s<T>() -> S<T> {
            new_s()
        }
    } => Ok(())
}
