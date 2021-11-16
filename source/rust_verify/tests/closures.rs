#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 code! {
        #[proof]
        fn takefun<F: Fn(u32, u64) -> bool>(f: F) -> bool {
            ensures(|b: bool| b == f(10, 20));

            #[spec] let b: bool = f(10, 20);
            b
        }

        #[proof]
        fn testtake() {
            let b: bool = takefun(|x: u32, y: u64| (x as u64) < y);
            assert(b);
        }

        #[spec]
        fn polytestfun<A, F: Fn(A, A) -> A>(a: A, f: F) -> A{
            f(a, a)
        }

        #[proof]
        fn testfun<A>(a: A, b: bool) {
            let aa = polytestfun(a, |x: A, y: A| (if b { x } else { y }));
            assert(equal(a, aa));
        }

        #[spec]
        fn specf<F: Fn(u32) -> u32>(x: u32, f: F) -> u32 {
            f(f(x))
        }

        #[proof]
        fn test_specf(p: u32) {
            requires(p < 100);

            let q: u32 = 3;
            assert(specf(10, |z: u32| z + 1 + p + q) == 18 + 2 * p);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 code! {
        #[proof]
        fn takefun<F: Fn(u32, u64) -> bool>(f: F) -> bool {
            ensures(|b: bool| b == f(10, 20));

            #[spec] let b: bool = f(10, 20);
            b
        }

        #[proof]
        fn testtake() {
            let b: bool = takefun(|x: u32, y: u64| (x as u64) < y);
            assert(!b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2 code! {
        #[spec]
        fn polytestfun<A, F: Fn(A, A) -> A>(a: A, f: F) -> A{
            f(a, a)
        }

        #[proof]
        fn testfun<A>(a: A, b: bool) {
            let aa = polytestfun(a, |x: A, y: A| (if b { x } else { y }));
            assert(!equal(a, aa)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails3 code! {
        #[spec]
        fn specf<F: Fn(u32) -> u32>(x: u32, f: F) -> u32 {
            f(f(x))
        }

        #[proof]
        fn test_specf(p: u32) {
            let q: u32 = 3;
            assert(specf(10, |z: u32| z + 1 + p + q) == 18 + 2 * p); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
