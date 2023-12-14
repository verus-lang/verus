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
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: trait generics")
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
