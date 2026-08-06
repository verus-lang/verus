#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_basic verus_code! {
        trait Tr {
            fn stuff() -> ((a, _): (u8, u8))
                ensures 0 <= a < 20;
        }

        struct X { }

        impl Tr for X {
            fn stuff() -> ((a, b): (u8, u8))
                ensures 25 <= b < 40,
            {
                return (10, 90); // FAILS
            }
        }

        fn test() {
            let r = X::stuff();
            assert(0 <= r.0 < 20);
            assert(25 <= r.1 < 40);
            assert(false); // FAILS
        }

        fn test2() {
            let r = X::stuff();
            assert(0 <= r.0 < 20);
            assert(25 <= r.1 < 40);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_basic2 verus_code! {
        trait Tr {
            fn stuff() -> (res: (u8, u8));
        }

        struct X { }

        impl Tr for X {
            fn stuff() -> (res: (u8, u8))
                ensures 25 <= res.1 < 40,
            {
                return (10, 90); // FAILS
            }
        }

        fn test() {
            let r = X::stuff();
            assert(25 <= r.1 < 40);
            assert(false); // FAILS
        }

        fn test2() {
            let r = X::stuff();
            assert(25 <= r.1 < 40);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_renaming verus_code! {
        trait Tr {
            fn stuff(x: u8, y: u8) -> (res: u8)
                requires x + 2 * y <= 200,
                ensures res <= 220;
        }

        struct X { }

        impl Tr for X {
            // args flipped
            fn stuff(y: u8, x: u8) -> (foo: u8)
                ensures foo == y + 2 * x,
            {
                return y + 2 * x;
            }
        }

        fn test() {
            let r = X::stuff(20, 30);
            assert(r == 80);
            assert(false); // FAILS
        }

        struct Y { }

        impl Tr for Y {
            // args flipped
            fn stuff(y: u8, x: u8) -> (foo: u8)
                ensures 200 <= foo <= 240,
                    y + 2 * x <= 200
            {
                return 100; // FAILS
            }
        }

        fn test2() {
            let r = Y::stuff(20, 30);
            assert(200 <= r <= 220);
            assert(false); // FAILS
        }

        struct Z { }

        impl Tr for Z {
            // args flipped
            fn stuff(y: u8, x: u8) -> (foo: u8)
                ensures
                    x + 2 * y <= 200
            {
                return 100; // FAILS
            }
        }

        fn test3() {
            let r = Z::stuff(100, 50);
            assert(false);
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] test_basic_generic verus_code! {
        trait Tr {
            fn stuff<T>(x: T) -> T;
        }

        struct X { }

        impl Tr for X {
            fn stuff<T>(x: T) -> (res: T)
                ensures res == x
            {
                return x;
            }
        }

        fn test() {
            let r = X::stuff(15);
            assert(r == 15);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_basic_generic2 verus_code! {
        trait Tr<Y, Z> {
            fn stuff<T>(x: T, y: &Y, z: &Z) -> T;
        }

        struct X<A, B, C, D, E, F>(A, B, C, D, E, F);

        impl<A, B, C, D, E, F> Tr<A, bool> for X<A, B, C, D, E, F> {
            fn stuff<Q>(x: Q, y: &A, z: &bool) -> (res: Q)
                ensures res == x
            {
                return x;
            }
        }

        fn test() {
            let r = <X::<u8, u16, u32, u64, u128, int> as Tr<u8, bool>>::stuff(15, &12, &true);
            assert(r == 15);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_basic_proof_mode verus_code! {
        trait Tr {
            proof fn stuff() -> (res: (u8, u8))
                ensures 0 <= res.0 < 20;
        }

        struct X { }

        impl Tr for X {
            proof fn stuff() -> (res: (u8, u8))
                ensures 25 <= res.1 < 40,
            {
                return (10, 90); // FAILS
            }
        }

        proof fn test() {
            let r = X::stuff();
            assert(0 <= r.0 < 20);
            assert(25 <= r.1 < 40);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_spec_mode_fail verus_code! {
        trait Tr {
            spec fn stuff() -> bool;
        }

        struct X { }

        impl Tr for X {
            spec fn stuff() -> bool
                ensures true,
            {
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "spec functions cannot have requires/ensures")
}

test_verify_one_file! {
    #[test] test_trait_arg verus_code! {
        trait T<A> {
            proof fn f(a: &A) ensures true;
        }
        struct S;
        impl<B> T<B> for S {
            proof fn f(b: &B) ensures true {  }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_trait_arg2 verus_code! {
        struct Y { j: int }

        trait Tr<B> {
            proof fn stuff(a: B, b: B) -> (res: (B, B, B))
                ensures res.0 == res.1;
        }

        struct X<B> { b: B }

        impl<B> Tr<B> for X<B> {
            proof fn stuff(a: B, b: B) -> (res: (B, B, B))
                ensures res.1 == res.2
            {
                return (a, a, b); // FAILS
            }
        }

        struct X2<B> { b: B }

        impl<B> Tr<B> for X2<B> {
            proof fn stuff(a: B, b: B) -> (res: (B, B, B))
                ensures res.1 == res.2
            {
                return (a, b, b); // FAILS
            }
        }

        proof fn test(a: Y, b: Y) {
            let r = X::<Y>::stuff(a, b);
            assert(r.0 == r.1);
            assert(r.1 == r.2);
            assert(false); // FAILS
        }

        struct Z { j: int }

        impl Tr<u8> for Z {
            proof fn stuff(a: u8, b: u8) -> (res: (u8, u8, u8))
                ensures res.1 == res.2
            {
                return (0, 0, 1); // FAILS
            }
        }

        proof fn test2(a: u8, b: u8) {
            let r = Z::stuff(a, b);
            assert(r.0 == r.1);
            assert(r.1 == r.2);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file! {
    #[test] test_trait_arg3 verus_code! {
        trait Compare {
            spec fn comp(&self, other: &Self) -> bool;
        }

        struct Y { j: int }
        impl Compare for Y {
            spec fn comp(&self, other: &Self) -> bool {
                self.j == other.j + 1
            }
        }

        trait Tr<B: Compare> {
            proof fn stuff(a: B, b: B, c: B) -> ((x, y, _): (B, B, B))
                requires a.comp(&b), b.comp(&c),
                ensures x.comp(&y);
        }

        struct X<B> { b: B }

        impl<B: Compare> Tr<B> for X<B> {
            proof fn stuff(a: B, b: B, c: B) -> ((_, y, z): (B, B, B))
                ensures y.comp(&z)
            {
                return (a, a, b); // FAILS
            }
        }

        struct X2<B> { b: B }

        impl<B: Compare> Tr<B> for X2<B> {
            proof fn stuff(a: B, b: B, c: B) -> ((_, y, z): (B, B, B))
                ensures y.comp(&z)
            {
                return (a, b, b); // FAILS
            }
        }

        struct X3<B> { b: B }

        impl<B: Compare> Tr<B> for X3<B> {
            proof fn stuff(a: B, b: B, c: B) -> ((_, y, z): (B, B, B))
                ensures y.comp(&z)
            {
                return (a, b, c);
            }
        }

        proof fn test(a: Y, b: Y, c: Y)
            requires a.comp(&b), b.comp(&c),
        {
            let r = X::<Y>::stuff(a, b, c);
            assert(r.0.comp(&r.1));
            assert(r.1.comp(&r.2));
            assert(false); // FAILS
        }

        impl Compare for u8 {
            spec fn comp(&self, other: &Self) -> bool {
                self == other + 1
            }
        }

        struct Z { j: int }

        impl Tr<u8> for Z {
            proof fn stuff(a: u8, b: u8, c: u8) -> ((_, y, z): (u8, u8, u8))
                ensures y.comp(&z)
            {
                return (1, 1, 0); // FAILS
            }
        }

        proof fn test2(a: u8, b: u8, c: u8)
            requires a == b + 1, b == c + 1,
        {
            let r = Z::stuff(a, b, c);
            assert(r.0 == r.1 + 1);
            assert(r.1 == r.2 + 1);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file! {
    #[test] test_trait_arg4 verus_code! {
        trait Compare {
            spec fn comp(&self, other: &Self) -> bool;
        }

        trait Tr<B: Compare> {
            proof fn stuff(a: B, b: B, c: B) -> (res: (B, B, B))
                requires a.comp(&b), b.comp(&c),
                ensures res.0.comp(&res.1);
        }

        struct X<B> { b: B }

        impl<B: Compare> Compare for X<B> {
            spec fn comp(&self, other: &Self) -> bool {
                other.b.comp(&self.b)
            }
        }

        struct Y<B> { b: B }

        impl<B: Compare> Tr<X<B>> for Y<B> {
            proof fn stuff(a: X<B>, b: X<B>, c: X<B>) -> (res: (X<B>, X<B>, X<B>))
                ensures res.1.comp(&res.2)
            {
                return (a, a, b); // FAILS
            }
        }

        struct Y2<B> { b: B }

        impl<B: Compare> Tr<X<B>> for Y2<B> {
            proof fn stuff(a: X<B>, b: X<B>, c: X<B>) -> (res: (X<B>, X<B>, X<B>))
                ensures res.1.comp(&res.2)
            {
                return (a, a, b); // FAILS
            }
        }

        struct Y3<B> { b: B }

        impl<B: Compare> Tr<X<B>> for Y3<B> {
            proof fn stuff(a: X<B>, b: X<B>, c: X<B>) -> (res: (X<B>, X<B>, X<B>))
                ensures res.1.comp(&res.2)
            {
                return (a, b, c);
            }
        }

        impl Compare for u8 {
            spec fn comp(&self, other: &Self) -> bool {
                self == other + 1
            }
        }

        proof fn test(a: X<u8>, b: X<u8>, c: X<u8>)
            requires a.comp(&b), b.comp(&c),
        {
            let r = Y3::<u8>::stuff(a, b, c);
            assert(r.0.comp(&r.1));
            assert(r.1.comp(&r.2));
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_disallow_default_ensures1 verus_code! {
        trait T {
            fn f(i: u32) -> (r: u32)
                ensures
                    r <= i,
                default_ensures
                    r == i / 2;
        }
    } => Err(err) => assert_vir_error_msg(err, "default_ensures not allowed here")
}

test_verify_one_file! {
    #[test] test_disallow_default_ensures2 verus_code! {
        trait T {
            fn f(i: u32) -> (r: u32)
                requires
                    (verus_builtin::default_ensures)(true),
                ensures
                    r <= i,
            {
                i / 2
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "default_ensures not allowed here")
}

test_verify_one_file! {
    #[test] test_disallow_default_ensures3 verus_code! {
        fn f(i: u32) -> (r: u32)
            ensures
                r <= i,
            default_ensures
                r == i / 2,
        {
            i / 2
        }
    } => Err(err) => assert_vir_error_msg(err, "default_ensures not allowed here")
}

test_verify_one_file! {
    #[test] test_disallow_default_ensures4 verus_code! {
        fn f(i: u32) -> (r: u32)
            ensures
                r <= i,
        {
            assert((verus_builtin::default_ensures)(true));
            i / 2
        }
    } => Err(err) => assert_vir_error_msg(err, "default_ensures not allowed here")
}

test_verify_one_file! {
    #[test] test_disallow_default_ensures5 verus_code! {
        trait T {
            fn f(i: u32) -> (r: u32)
                ensures
                    r <= i;
        }
        impl T for u8 {
            fn f(i: u32) -> (r: u32)
                default_ensures
                    r <= i,
            {
                i / 2
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "default_ensures not allowed here")
}

test_verify_one_file! {
    #[test] test_disallow_default_ensures6 verus_code! {
        trait T {
            fn f(i: u32) -> (r: u32)
                ensures
                    r <= i,
            {
                i / 2
            }
        }
        impl T for u8 {
            fn f(i: u32) -> (r: u32)
                default_ensures
                    r <= i,
            {
                i / 2
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "default_ensures not allowed here")
}

test_verify_one_file! {
    #[test] test_default_ensures1 verus_code! {
        trait T {
            fn f(i: u32) -> (r: u32)
                ensures
                    r <= i,
                default_ensures
                    r == i / 2, // FAILS
            {
                i
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_default_ensures_ret_val_collision verus_code! {
        trait T {
            fn f(i: u32) -> (f: u32)
                ensures
                    f <= i,
                default_ensures
                    f == i / 2,
            {
                i / 2
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_default_ensures2 verus_code! {
        trait T {
            fn f(i: u32) -> (r: u32)
                ensures
                    r <= i,
                default_ensures
                    r == i / 2,
            {
                i / 2
            }
        }
        impl T for u8 {
        }
        impl T for u16 {
            fn f(i: u32) -> u32 {
                i / 3
            }
        }
        impl T for i16 {
            fn f(i: u32) -> (r: u32)
                ensures r == i / 5
            {
                i / 5
            }
        }
        fn generic<A: T>() {
            let r = A::f(6);
            assert(r <= 6);
            assert(r == 3); // FAILS
        }
        fn inheritor() {
            let r = <u8 as T>::f(6);
            assert(r == 3);
        }
        fn overrider1() {
            let r = <u16 as T>::f(6);
            assert(r == 3); // FAILS
        }
        fn overrider2() {
            let r = <i16 as T>::f(6);
            assert(r == 3); // FAILS
        }
        fn overrider3() {
            let r = <i16 as T>::f(15);
            assert(r == 3);
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_default_ensures3 verus_code! {
        trait T {
            fn f(i: u32) -> (r: u32)
                ensures
                    r <= i,
                default_ensures
                    r == i / 2,
            {
                i / 2
            }
        }
        impl T for u8 {
        }
        impl T for u16 {
            fn f(i: u32) -> u32 {
                i / 3
            }
        }
        impl T for i16 {
            fn f(i: u32) -> (r: u32)
                ensures r == i / 5
            {
                i / 5
            }
        }
        fn generic<A: T>() {
            assert(forall|r| call_ensures(A::f, (6,), r) ==> r <= 6);
            assert(forall|r| call_ensures(A::f, (6,), r) ==> r == 3); // FAILS
        }
        fn inheritor() {
            assert(forall|r| call_ensures(<u8 as T>::f, (6,), r) ==> r == 3);
        }
        fn overrider1() {
            assert(forall|r| call_ensures(<u16 as T>::f, (6,), r) ==> r == 3); // FAILS
        }
        fn overrider2() {
            assert(forall|r| call_ensures(<i16 as T>::f, (6,), r) ==> r == 3); // FAILS
        }
        fn overrider3() {
            assert(forall|r| call_ensures(<i16 as T>::f, (15,), r) ==> r == 3);
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_default_ensures_extern_impl verus_code! {
        trait T {
            fn f();
            fn g() {
                Self::f();
            }
        }

        #[verifier::external]
        impl T for bool {
            fn f() {
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_default_ensures_extern1 verus_code! {
        #[verifier::external]
        trait T {
            fn f(i: u32) -> u32 {
                i / 2
            }
        }
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;
            fn f(i: u32) -> (r: u32)
                ensures
                    r <= i,
                default_ensures
                    r == i / 2;
        }
        impl T for u8 {
        }
        #[verifier::external]
        impl T for i8 {
        }
        impl T for u16 {
            fn f(i: u32) -> u32 {
                i / 3
            }
        }
        impl T for i16 {
            fn f(i: u32) -> (r: u32)
                ensures r == i / 5
            {
                i / 5
            }
        }
        #[verifier::external]
        impl T for bool {
            fn f(i: u32) -> u32
            {
                i / 7
            }
        }
        assume_specification[ <bool as T>::f ](i: u32) -> (r: u32)
            ensures r == i / 7
        ;
        fn generic<A: T>() {
            let r = A::f(6);
            assert(r <= 6);
            assert(r == 3); // FAILS
        }
        fn inheritor1() {
            let r = <u8 as T>::f(6);
            assert(r == 3);
        }
        fn inheritor2() {
            let r = <i8 as T>::f(6);
            assert(r == 3);
        }
        fn overrider1() {
            let r = <u16 as T>::f(6);
            assert(r == 3); // FAILS
        }
        fn overrider2() {
            let r = <i16 as T>::f(6);
            assert(r == 3); // FAILS
        }
        fn overrider3() {
            let r = <i16 as T>::f(15);
            assert(r == 3);
        }
        fn overrider4() {
            let r = <bool as T>::f(6);
            assert(r == 3); // FAILS
        }
        fn overrider5() {
            let r = <bool as T>::f(21);
            assert(r == 3);
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] test_default_ensures_extern2 verus_code! {
        #[verifier::external]
        trait T {
            fn f(i: u32) -> u32 {
                i / 2
            }
        }
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;
            fn f(i: u32) -> (r: u32)
                ensures
                    r <= i,
                default_ensures
                    r == i / 2;
        }
        impl T for u8 {
        }
        #[verifier::external]
        impl T for i8 {
        }
        impl T for u16 {
            fn f(i: u32) -> u32 {
                i / 3
            }
        }
        impl T for i16 {
            fn f(i: u32) -> (r: u32)
                ensures r == i / 5
            {
                i / 5
            }
        }
        #[verifier::external]
        impl T for bool {
            fn f(i: u32) -> u32
            {
                i / 7
            }
        }
        assume_specification[ <bool as T>::f ](i: u32) -> (r: u32)
            ensures r == i / 7
        ;
        fn generic<A: T>() {
            assert(forall|r| call_ensures(A::f, (6,), r) ==> r <= 6);
            assert(forall|r| call_ensures(A::f, (6,), r) ==> r == 3); // FAILS
        }
        fn inheritor1() {
            assert(forall|r| call_ensures(<u8 as T>::f, (6,), r) ==> r == 3);
        }
        fn inheritor2() {
            assert(forall|r| call_ensures(<i8 as T>::f, (6,), r) ==> r <= 6);
            // Because T for i8 is external, we shouldn't know whether it inherits the default
            assert(forall|r| call_ensures(<i8 as T>::f, (6,), r) ==> r == 3); // FAILS
        }
        fn overrider1() {
            assert(forall|r| call_ensures(<u16 as T>::f, (6,), r) ==> r == 3); // FAILS
        }
        fn overrider2() {
            assert(forall|r| call_ensures(<i16 as T>::f, (6,), r) ==> r == 3); // FAILS
        }
        fn overrider3() {
            assert(forall|r| call_ensures(<i16 as T>::f, (15,), r) ==> r == 3);
        }
        fn overrider4() {
            assert(forall|r| call_ensures(<bool as T>::f, (6,), r) ==> r == 3); // FAILS
        }
        fn overrider5() {
            assert(forall|r| call_ensures(<bool as T>::f, (21,), r) ==> r == 3);
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file! {
    #[test] test_default_ensures_inner_typ_params verus_code! {
        trait T1<A1> {}
        trait T2<A2, B2> {}

        trait Q<A: T1<A>, Z> {
            proof fn p<B: T2<A, B>>(a: &A, b: &B, z: &Z) -> (i: int)
                requires
                    a == a,
                default_ensures
                    i == 5,
            {
                5
            }

            spec fn f<B: T2<A, B>>(a: &A, b: &B, z: &Z) -> int {
                5
            }
        }

        impl T1<u16> for u16 {}
        impl T2<u16, f32> for f32 {}

        impl<C> Q<u16, C> for bool {
        }

        proof fn test() {
            assert(<bool as Q<u16, nat>>::f::<f32>(&6u16, &1.0, &7nat) == 5);
            let i = <bool as Q<u16, nat>>::p::<f32>(&6u16, &1.0, &7nat);
            assert(i == 5);
            assert(i == 6); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_trait_decl_only1 verus_code! {
        #[verifier::impls_cannot_extend_spec]
        fn e();
    } => Err(err) => assert_vir_error_msg(err, "only exec trait functions can be marked impls_cannot_extend_spec")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_trait_decl_only2 verus_code! {
        trait T {
            fn e();
        }
        impl T for u8 {
            #[verifier::impls_cannot_extend_spec]
            fn e() {}
        }
    } => Err(err) => assert_vir_error_msg(err, "only exec trait functions can be marked impls_cannot_extend_spec")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_no_spec verus_code! {
        trait T {
            #[verifier::impls_cannot_extend_spec]
            spec fn e();
        }
    } => Err(err) => assert_vir_error_msg(err, "only exec trait functions can be marked impls_cannot_extend_spec")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_no_proof verus_code! {
        trait T {
            #[verifier::impls_cannot_extend_spec]
            proof fn e();
        }
    } => Err(err) => assert_vir_error_msg(err, "only exec trait functions can be marked impls_cannot_extend_spec")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_no_add_ensures verus_code! {
        trait T {
            #[verifier::impls_cannot_extend_spec]
            fn e();
        }
        impl T for u8 {
            fn e() ensures true {}
        }
    } => Err(err) => assert_vir_error_msg(err, "trait method implementation cannot declare ensures clauses because the trait declaration is marked impls_cannot_extend_spec")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_allow_self_bound verus_code! {
        trait T {
            #[verifier::impls_cannot_extend_spec]
            fn e<A: T>();
        }

        trait T1 {
            fn e<A: T2>();
        }
        trait T2 {
            #[verifier::impls_cannot_extend_spec]
            fn e<A: T1>();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_cycle1 verus_code! {
        spec fn r() -> bool { f::<u8>() }
        trait T { fn e() requires r(); }
        spec fn f<A: T>() -> bool { call_requires(A::e, ()) }
        impl T for u8 { fn e() {} }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_cycle2 verus_code! {
        spec fn r() -> bool { f() }
        trait T { fn e() requires r(); }
        impl T for u8 { fn e() {} }
        spec fn f() -> bool { call_requires(u8::e, ()) }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_cycle3 verus_code! {
        spec fn r() -> bool { f::<u8>() }
        trait T { fn e() ensures r(); }
        spec fn f<A: T>() -> bool { call_ensures(A::e, (), ()) }
        impl T for u8 { fn e() {} }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_cycle4 verus_code! {
        spec fn r() -> bool { f() }
        trait T { fn e() ensures r(); }
        impl T for u8 { fn e() {} }
        spec fn f() -> bool { call_ensures(u8::e, (), ()) }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_cycle1b verus_code! {
        spec fn r() -> bool { f::<u8>() }
        trait T { #[verifier::impls_cannot_extend_spec]fn e() requires r(); }
        spec fn f<A: T>() -> bool { call_requires(A::e, ()) }
        impl T for u8 { fn e() {} }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_cycle2b verus_code! {
        spec fn r() -> bool { f() }
        trait T { #[verifier::impls_cannot_extend_spec]fn e() requires r(); }
        impl T for u8 { fn e() {} }
        spec fn f() -> bool { call_requires(u8::e, ()) }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_cycle3b verus_code! {
        spec fn r() -> bool { f::<u8>() }
        trait T { #[verifier::impls_cannot_extend_spec]fn e() ensures r(); }
        spec fn f<A: T>() -> bool { call_ensures(A::e, (), ()) }
        impl T for u8 { fn e() {} }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_cycle4b verus_code! {
        spec fn r() -> bool { f() }
        trait T { #[verifier::impls_cannot_extend_spec] fn e() ensures r(); }
        impl T for u8 { fn e() {} }
        spec fn f() -> bool { call_ensures(u8::e, (), ()) }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_example verus_code! {
        trait Iter1 {
            spec fn next1_spec(self) -> u8;

            fn next1(self) -> (r: u8) ensures r == self.next1_spec();

            #[verifier::impls_cannot_extend_spec]
            fn zip1<U: Iter1>(self, other: U) -> ((x, y): (u8, u8))
                ensures x == self.next1_spec() && y == other.next1_spec();
        }

        struct Always42 {}

        impl Iter1 for Always42 {
            spec fn next1_spec(self) -> u8 {
                42
            }

            fn next1(self) -> u8 {
                42
            }

            fn zip1<U: Iter1>(self, other: U) -> ((x, y): (u8, u8)) {
                let y = other.next1();
                (42, y)
            }
        }

        fn generic<I: Iter1>(i1: I, i2: I) -> ((x, y): (u8, u8))
            ensures x == i1.next1_spec() && y == i2.next1_spec()
        {
            i1.zip1(i2)
        }

        fn test() {
            let i1 = Always42 {};
            let i2 = Always42 {};
            let v = generic(i1, i2);
            assert(v == (42, 42));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_bad1 verus_code! {
        trait T {
            fn f<A: T>();
        }
        impl T for u8 {
            fn f<A: T>()
                ensures !call_ensures(u8::f::<A>, (), ()) // must be rejected
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_bad2 verus_code! {
        trait T {
            #[verifier::impls_cannot_extend_spec]
            fn f<A: T>();
        }
        impl T for u8 {
            fn f<A: T>()
                ensures !call_ensures(u8::f::<A>, (), ()) // must be rejected
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "trait method implementation cannot declare ensures clauses because the trait declaration is marked impls_cannot_extend_spec")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_bad3 verus_code! {
        trait T {
            fn f<A: T>()
                requires !call_requires(A::f::<A>, ());
        }
        impl T for u8 {
            fn f<A: T>() {
                assert(false);
            }
        }
        fn test() {
            u8::f::<u8>();
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_bad4 verus_code! {
        trait T {
            #[verifier::impls_cannot_extend_spec]
            fn f<A: T>()
                requires !call_requires(A::f::<A>, ());
        }
        impl T for u8 {
            fn f<A: T>() {
                assert(false);
            }
        }
        fn test() {
            u8::f::<u8>();
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_bad5 verus_code! {
        trait T {
            fn f<A: T>()
                ensures !call_ensures(A::f::<A>, (), ());
        }
        impl T for u8 {
            fn f<A: T>() {
            }
        }
        fn test() {
            u8::f::<u8>();
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency")
}

test_verify_one_file! {
    #[test] test_impls_cannot_extend_spec_bad6 verus_code! {
        trait T {
            #[verifier::impls_cannot_extend_spec]
            fn f<A: T>()
                ensures !call_ensures(A::f::<A>, (), ());
        }
        impl T for u8 {
            fn f<A: T>() {
            }
        }
        fn test() {
            u8::f::<u8>();
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency")
}
