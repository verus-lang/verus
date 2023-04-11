#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_use_fun_ext verus_code! {
        use vstd::function::*;

        proof fn test_use_fun_ext(f: FnSpec(int) -> int) {
          fun_ext::<int, int>(|i: int| i + 1, |i: int| 1 + i);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_use_fun_ext2 verus_code! {
        use vstd::function::*;

        spec fn drop<A>(f: FnSpec(int) -> A, k: nat) -> FnSpec(int) -> A {
          |n: int| f(n + k)
        }

        /// prove a rule for simplifying drop(drop(f, ...))
        proof fn test_use_fun_ext2<A>(f: FnSpec(int) -> A, k1: nat, k2: nat)
          ensures drop(drop(f, k1), k2) === drop(f, k1 + k2) {
          fun_ext::<int, A>(drop(drop(f, k1), k2), drop(f, k1 + k2));
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
