#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_basic verus_code! {
        trait Tr {
            fn stuff() -> (res: (u8, u8))
                ensures 0 <= res.0 < 20;
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
            proof fn stuff(a: B, b: B, c: B) -> (res: (B, B, B))
                requires a.comp(&b), b.comp(&c),
                ensures res.0.comp(&res.1);
        }

        struct X<B> { b: B }

        impl<B: Compare> Tr<B> for X<B> {
            proof fn stuff(a: B, b: B, c: B) -> (res: (B, B, B))
                ensures res.1.comp(&res.2)
            {
                return (a, a, b); // FAILS
            }
        }

        struct X2<B> { b: B }

        impl<B: Compare> Tr<B> for X2<B> {
            proof fn stuff(a: B, b: B, c: B) -> (res: (B, B, B))
                ensures res.1.comp(&res.2)
            {
                return (a, b, b); // FAILS
            }
        }

        struct X3<B> { b: B }

        impl<B: Compare> Tr<B> for X3<B> {
            proof fn stuff(a: B, b: B, c: B) -> (res: (B, B, B))
                ensures res.1.comp(&res.2)
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
            proof fn stuff(a: u8, b: u8, c: u8) -> (res: (u8, u8, u8))
                ensures res.1.comp(&res.2)
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
