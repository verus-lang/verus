#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] basics verus_code! {
        trait Tr { spec fn stuff(self) -> int; }

        struct X { }
        struct Y { }
        struct Z { }

        impl Tr for Y { spec fn stuff(self) -> int { 1 } }
        impl Tr for Z { spec fn stuff(self) -> int { 2 } }

        spec fn helper<T: Tr>(t: T) -> int {
            t.stuff()
        }

        #[verifier::if_trait_bound_then_redirect_to(helper)]
        spec fn foo<T>(t: T) -> int {
            0 // if bound(T: Tr) { t.stuff() } else { 0 }
        }

        proof fn test1() {
            // We don't have any negative trait bounds, so this fails
            assert(foo::<X>(X{}) == 0); // FAILS
        }

        proof fn test2() {
            assert(foo::<Y>(Y{}) == 1);
            assert(foo::<Z>(Z{}) == 2);
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] basics_with_eq_bound verus_code! {
        trait Tr {
            type T;
        }

        struct X { }
        struct Y { }

        impl Tr for X {
            type T = u64;
        }

        spec fn true_fn<T, U>() -> bool
            where T: Tr<T = U>
        {
            true
        }

        #[verifier::if_trait_bound_then_redirect_to(true_fn)]
        spec fn foo<T, U>() -> bool {
            false
        }

        proof fn testY() {
            // We don't have any negative trait bounds, so this fails
            assert(!foo::<Y, u64>()); // FAILS
        }

        proof fn testY_2() {
            assert(foo::<Y, u64>()); // FAILS
        }

        proof fn testX() {
            assert(foo::<X, u64>());
        }

        proof fn testX_2() {
            // We don't have any negative trait bounds, so this fails
            assert(foo::<X, u32>()); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] prophecy verus_code! {
        trait Tr { }

        #[verifier::prophetic]
        spec fn true_fn<T, U>() -> bool
            where T: Tr,
        {
            true
        }

        #[verifier::if_trait_bound_then_redirect_to(true_fn)]
        spec fn foo<T, U>() -> bool {
            false
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for body of non-prophetic spec function")
}

test_verify_one_file! {
    #[test] path_not_found verus_code! {
        trait Tr { }

        #[verifier::if_trait_bound_then_redirect_to(this_fn_does_not_exist)]
        spec fn foo<T, U>() -> bool {
            false
        }
    } => Err(err) => assert_vir_error_msg(err, "no function found for path test_crate::this_fn_does_not_exist")
}

test_verify_one_file! {
    #[test] uninterp_fn verus_code! {
        trait Tr { }

        spec fn true_fn<T, U>() -> bool
            where T: Tr,
        {
            true
        }

        #[verifier::if_trait_bound_then_redirect_to(true_fn)]
        uninterp spec fn foo<T, U>() -> bool;
    } => Err(err) => assert_vir_error_msg(err, "'if_trait_bound_then_redirect_to' may only be applied to a function with a body")
}

test_verify_one_file! {
    #[test] not_spec_mode_1 verus_code! {
        trait Tr { }

        spec fn true_fn<T, U>() -> bool
            where T: Tr,
        {
            true
        }

        #[verifier::if_trait_bound_then_redirect_to(true_fn)]
        proof fn foo<T, U>() -> bool {
            false
        }
    } => Err(err) => assert_vir_error_msg(err, "if_trait_bound_then_redirect_to' may only be applied to a spec-mode function")
}

test_verify_one_file! {
    #[test] not_spec_mode_2 verus_code! {
        trait Tr { }

        proof fn true_fn<T, U>() -> bool
            where T: Tr,
        {
            true
        }

        #[verifier::if_trait_bound_then_redirect_to(true_fn)]
        spec fn foo<T, U>() -> bool {
            false
        }
    } => Err(err) => assert_vir_error_msg(err, "'if_trait_bound_then_redirect_to': the function `test_crate::true_fn` is not a spec function")
}

test_verify_one_file! {
    #[test] different_named_params verus_code! {
        trait Tr { }

        spec fn true_fn<U, T>() -> bool
            where T: Tr,
        {
            true
        }

        #[verifier::if_trait_bound_then_redirect_to(true_fn)]
        spec fn foo<T, U>() -> bool {
            false
        }
    } => Err(err) => assert_vir_error_msg(err, "the functions `test_crate::foo` and `test_crate::true_fn` must have the same generic type parameters (but not necessarily the same bounds)")
}

test_verify_one_file! {
    #[test] different_num_args verus_code! {
        trait Tr { }

        spec fn true_fn<T, U>(u: u64) -> bool
            where T: Tr,
        {
            true
        }

        #[verifier::if_trait_bound_then_redirect_to(true_fn)]
        spec fn foo<T, U>() -> bool {
            false
        }
    } => Err(err) => assert_vir_error_msg(err, "the functions `test_crate::foo` and `test_crate::true_fn` must have the same number of parameters")
}

test_verify_one_file! {
    #[test] different_arg_typs verus_code! {
        trait Tr { }

        spec fn true_fn<T, U>(t: T) -> bool
            where T: Tr,
        {
            true
        }

        #[verifier::if_trait_bound_then_redirect_to(true_fn)]
        spec fn foo<T, U>(t: U) -> bool {
            false
        }
    } => Err(err) => assert_vir_error_msg(err, "the functions `test_crate::foo` and `test_crate::true_fn` must have the same argument types (different in parameter 0)")
}

test_verify_one_file! {
    #[test] different_return_typs verus_code! {
        trait Tr { }

        #[verifier::prophetic]
        spec fn true_fn<T, U>() -> u64
            where T: Tr,
        {
            0
        }

        #[verifier::if_trait_bound_then_redirect_to(true_fn)]
        spec fn foo<T, U>() -> bool {
            false
        }
    } => Err(err) => assert_vir_error_msg(err, "the functions `test_crate::foo` and `test_crate::true_fn` must have the same return types")
}

test_verify_one_file! {
    #[test] cycle_checking verus_code! {
        trait Tr { spec fn stuff(self) -> bool; }

        struct X { }

        impl Tr for X { spec fn stuff(self) -> bool { foo::<X>(self) } }

        spec fn helper<T: Tr>(t: T) -> bool {
            !t.stuff()
        }

        #[verifier::if_trait_bound_then_redirect_to(helper)]
        spec fn foo<T>(t: T) -> bool {
            false
        }

        proof fn test1() {
            // We don't have any negative trait bounds, so this fails
            let x = X { };
            assert(foo::<X>(x) != x.stuff());
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "cycle")
}
