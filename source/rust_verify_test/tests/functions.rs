#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_use_fun_ext verus_code! {
        proof fn test_use_fun_ext(f: spec_fn(int) -> int) {
            assert((|i: int| i + 1) =~= (|i: int| 1 + i));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_use_fun_ext2 verus_code! {
        spec fn drop<A>(f: spec_fn(int) -> A, k: nat) -> spec_fn(int) -> A {
            |n: int| f(n + k)
        }

        /// prove a rule for simplifying drop(drop(f, ...))
        proof fn test_use_fun_ext2<A>(f: spec_fn(int) -> A, k1: nat, k2: nat)
            ensures drop(drop(f, k1), k2) === drop(f, k1 + k2)
        {
            assert(drop(drop(f, k1), k2) =~= drop(f, k1 + k2));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ensures_returns_default_regression_392_1 verus_code! {
        fn returns_nothing(a: u8, b: u8)
            requires a == b,
            ensures a == b,
        {
        }

        fn test() {
            let x: () = returns_nothing(0, 0);
            assert(x == ());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ensures_returns_default_regression_497 verus_code! {
        trait Foo {
            exec fn foo(&self);
        }

        struct X;

        impl Foo for X {
            exec fn foo(&self) {
                // do nothing
            }
        }

        exec fn bar() {
            let z: X = X;
            let x: () = z.foo();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ensures_returns_default_regression_392_2 verus_code! {
        spec fn foo() -> bool { true }

        fn returns_unit() ensures foo() { }

        fn test(b: bool) {
            let x: ();
            if b {
                x = returns_unit();
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ensures_returns_default_regression_392_3 verus_code! {
        spec fn foo() -> bool { true }

        fn returns_unit() ensures foo() { }

        fn takes_unit(u: ()) { }

        fn test(b: bool) {
            takes_unit(returns_unit());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_returns_named_unit verus_code! {
        proof fn test() -> (u: ())
            ensures u == ()
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_async_external_fn_accepted verus_code! {
        #[verifier(external)]
        async fn foo(_c: usize) -> Result<usize, ()> {
            Ok(21)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_non_async_opaque_types_disallowed verus_code! {
        trait Foo {
            fn bar(&self) -> bool;
        }

        type OT = impl Foo;
    } => Err(err) => {
        assert!(err.errors.iter().find(|p| p.message == "`impl Trait` in type aliases is unstable").is_some());
    }
}
