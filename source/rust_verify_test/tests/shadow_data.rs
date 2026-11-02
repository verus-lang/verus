#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        #[verifier::shadow_data]
        fn ident(x: &u64) -> (r: &u64)
            ensures shadow_data(r) == shadow_data(x)
        {
            x
        }

        #[verifier::shadow_data]
        fn test_ident1(x: &u64, y: &u64) {
            let xx = ident(x);
            let yy = ident(&*y);
            assert(shadow_data(xx) == shadow_data(x));
            assert(shadow_data(yy) == shadow_data(y)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1b verus_code! {
        #[verifier::shadow_data]
        fn ident1(x: &u64) -> (r: &u64)
            ensures shadow_data(r) == shadow_data(x)
        {
            x
        }

        // no #[verifier::shadow_data]
        fn ident2(x: &u64) -> (r: &u64) {
            x
        }

        #[verifier::shadow_data]
        fn check(x: &u64, y: &u64)
            requires shadow_data(x) == shadow_data(y)
        {
        }

        #[verifier::shadow_data]
        fn check_ident1(x: &u64, y: &u64) {
            let xx = ident1(x);
            check(x, xx);
            let yy = ident2(y);
            check(y, yy); // FAILS
        }

        // missing #[verifier::shadow_data]
        fn check_ident2(x: &u64, y: &u64) {
            let xx = ident1(x);
            check(x, xx); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        #[verifier::shadow_data]
        fn ident(x: &u64) -> (r: &u64)
            ensures shadow_data(r) == shadow_data(x) // FAILS
        {
            &*x
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3 verus_code! {
        #[verifier::shadow_data]
        fn test1() {
            let a = 10u32;
            let b = &a;
            let c = b;
            let d = &a;
            assert(shadow_data(b) == shadow_data(c));
            assert(shadow_data(b) == shadow_data(d)); // FAILS
        }

        #[verifier::shadow_data]
        fn test2() {
            let a = 10u32;
            let b = &a;
            let c = &*b;
            assert(shadow_data(b) == shadow_data(c)); // FAILS
        }

        #[verifier::shadow_data]
        fn test3(a: &u32, b: &u32) {
            let mut c = a;
            assert(shadow_data(a) == shadow_data(c));
            let ptr = &mut c;
            *ptr = b;
            assert(shadow_data(a) == shadow_data(c)); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_exec_only2 verus_code! {
        #[verifier::shadow_data]
        spec fn test() -> int { 5 }
    } => Err(err) => assert_vir_error_msg(err, "shadow_data only allowed for exec and proof functions")
}

test_verify_one_file! {
    #[test] test_shadow_data_only verus_code! {
        // missing #[verifier::shadow_data]
        fn test(x: &u32) {
            assert(shadow_data(x) == shadow_data(x));
        }
    } => Err(err) => assert_vir_error_msg(err, "shadow_data is not supported in this location")
}

test_verify_one_file! {
    #[test] test_traits1 verus_code! {
        trait T {
            fn f();
        }
        impl T for bool {
            #[verifier::shadow_data]
            fn f();
        }
    } => Err(err) => assert_vir_error_msg(err, "shadow_data only allowed in trait, not in impl")
}

test_verify_one_file! {
    #[test] test_traits2 verus_code! {
        trait T {
            #[verifier::shadow_data]
            fn f();
        }
        impl T for bool {
            #[verifier::shadow_data]
            fn f();
        }
    } => Err(err) => assert_vir_error_msg(err, "shadow_data only allowed in trait, not in impl")
}

test_verify_one_file! {
    #[test] test_traits3 verus_code! {
        trait T {
            #[verifier::shadow_data]
            fn f(x: &u32);
        }
        impl T for bool {
            fn f(x: &u32) {
                assert(shadow_data(x) == shadow_data(x));
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_call_requires_ensures verus_code! {
        #[verifier::shadow_data]
        fn f(a: &bool, b: &bool) -> (r: bool)
            requires
                *b,
                shadow_data(a) == shadow_data(b),
            ensures
                r,
        {
            true
        }
        fn test1() {
            assert(call_requires(f, (&true, &true,))); // FAILS
        }
        fn test2(r: bool) {
            assert(call_ensures(f, (&true, &true), r) ==> r); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_option verus_code! {
        use vstd::prelude::*;

        uninterp spec fn option_some_shadow_data<T>(s: ShadowData<T>) -> ShadowData<Option<T>>;
        uninterp spec fn option_unwrap_shadow_data<T>(s: ShadowData<Option<T>>) -> ShadowData<T>;

        #[verifier::shadow_data]
        #[verifier::external_body]
        fn option_some_with_shadow<T>(x: T) -> (r: Option<T>)
            ensures
                r == Some(x),
                shadow_data(r) == option_some_shadow_data(shadow_data(x)),
                // TODO: this should be a separate axiom:
                shadow_data(x) == option_unwrap_shadow_data(option_some_shadow_data(shadow_data(x))),
        {
            Some(x)
        }

        #[verifier::shadow_data]
        #[verifier::external_body]
        fn option_unwrap_with_shadow<T>(x: Option<T>) -> (r: T)
            requires
                x.is_some(),
            ensures
                r == x.unwrap(),
                shadow_data(r) == option_unwrap_shadow_data(shadow_data(x)),
        {
            x.unwrap()
        }

        #[verifier::shadow_data]
        fn test_option(x: &u64) {
            let o = option_some_with_shadow(x);
            let y = option_unwrap_with_shadow(o);
            assert(shadow_data(y) == shadow_data(x));
        }
    } => Ok(())
}
