#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Use external_fn_specification on an external function from the same crate

test_verify_one_file! {
    #[test] test_basics verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }

        fn test1() {
            let ret_b = negate_bool(true, 1);
            assert(ret_b == false);
        }

        fn test2() {
            let ret_b = negate_bool(true, 0); // FAILS
        }

        fn test3() {
            let ret_b = negate_bool(true, 1);
            assert(ret_b == true); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

// Apply external_fn_specification on a function from an external crate
// don't import vstd for this test (it would cause overlap)

test_verify_one_file! {
    #[test] test_apply_spec_to_external verus_code! {
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }

        fn test1() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 7 && y == 5);
        }

        fn test2() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// Import a specification from vstd of a function from std

test_verify_one_file! {
    #[test] test_import_spec_from_vstd verus_code! {
        use vstd::*;

        fn test1() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 7 && y == 5);
        }

        fn test2() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// Test for overlap

test_verify_one_file! {
    #[test] test_overlap verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures2(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `crate::negate_bool`")
}

test_verify_one_file! {
    #[test] test_overlap2 verus_code! {
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }

        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures2<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `core::mem::swap`")
}

test_verify_one_file! {
    #[test] test_overlap3 verus_code! {
        use vstd::*;

        // This will conflict with the mem::swap specification declared in vstd
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `core::mem::swap`")
}

// Test sane error message if you call a proxy

test_verify_one_file! {
    #[test] test_call_proxy verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }

        fn test() {
            negate_bool_requires_ensures(false, 1);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function marked `external_fn_specification` directly; call `crate::negate_bool` instead")
}

test_verify_one_file! {
    #[test] test_call_proxy2 verus_code! {
        fn test() {
            let x: u8 = 5;
            let y: u8 = 7;
            vstd::std_specs::core::ex_swap(&mut x, &mut y);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function marked `external_fn_specification` directly; call `core::mem::swap` instead")
}

test_verify_one_file! {
    #[test] test_call_external verus_code! {
        #[verifier(external)]
        fn some_external_fn() { }

        fn test() {
            some_external_fn();
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function marked `external`")
}

// If you wrongly try to apply a mode

test_verify_one_file! {
    #[test] test_proxy_marked_spec verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        spec fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
        {
            negate_bool(b, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "a function marked `external_fn_specification` cannot be marked `spec`")
}

test_verify_one_file! {
    #[test] test_proxy_marked_proof verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        proof fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
        {
            negate_bool(b, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "a function marked `external_fn_specification` cannot be marked `proof`")
}

// test visibility stuff

test_verify_one_file! {
    #[test] test_refers_to_closed_fn verus_code! {
        mod X {
            pub closed spec fn foo(b: bool, x: u8) -> bool {
                b && x == 0
            }

            #[verifier(external_fn_specification)]
            pub fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
                requires foo(b, x)
            {
                crate::negate_bool(b, x)
            }
        }

        #[verifier(external)]
        pub fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        pub fn test() {
            // this should fail because foo is closed
            negate_bool(true, 0); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_refers_to_open_fn verus_code! {
        mod X {
            pub open spec fn foo(b: bool, x: u8) -> bool {
                b && x == 0
            }

            #[verifier(external_fn_specification)]
            pub fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
                requires foo(b, x)
            {
                crate::negate_bool(b, x)
            }
        }

        #[verifier(external)]
        pub fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        pub fn test() {
            negate_bool(true, 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_refers_to_private_fn verus_code! {
        mod X {
            fn foo(b: bool, x: u8) -> bool {
                b && x == 0
            }

            #[verifier(external_fn_specification)]
            pub fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
                requires foo(b, x)
            {
                negate_bool(b, x)
            }

            #[verifier(external)]
            pub fn negate_bool(b: bool, x: u8) -> bool {
                !b
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "public function requires cannot refer to private items")
}

test_verify_one_file! {
    #[test] test_proxy_is_more_private verus_code! {
        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
        {
            negate_bool(b, x)
        }

        #[verifier(external)]
        pub fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }
    } => Err(err) => assert_vir_error_msg(err, "a function marked `external_fn_specification` must be visible to the function it provides a spec for")
}

test_verify_one_file! {
    #[test] test_proxy_is_more_private2 verus_code! {
        #[verifier(external_fn_specification)]
        fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "a function marked `external_fn_specification` must be visible to the function it provides a spec for")
}

// Test the attribute in weird places

test_verify_one_file! {
    #[test] test_attr_on_const verus_code! {
        #[verifier(external_fn_specification)]
        const x: u8 = 5;
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_struct verus_code! {
        #[verifier(external_fn_specification)]
        struct X { }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_impl verus_code! {
        struct X { }

        #[verifier(external_fn_specification)]
        impl X { }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_trait verus_code! {
        #[verifier(external_fn_specification)]
        trait Tr { }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_trait_fn verus_code! {
        trait Tr {
            #[verifier(external_fn_specification)]
            fn foo();
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_trait_fn_impl verus_code! {
        trait Tr {
            fn foo();
        }

        struct X { }

        impl Tr for X {
            #[verifier(external_fn_specification)]
            fn foo() { }
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_member_function verus_code! {
        struct X { }

        impl X {
            #[verifier(external_fn_specification)]
            fn stuff(&self) { }
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_assoc_function verus_code! {
        struct X { }

        impl X {
            #[verifier(external_fn_specification)]
            fn stuff() { }
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_foreign_function verus_code! {
        extern "C" {
            #[verifier(external_fn_specification)]
            fn stuff();
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported on foreign items")
}

// Mismatched type signatures

test_verify_one_file! {
    #[test] mismatch_params verus_code! {
        #[verifier(external)]
        fn x(b: bool) -> bool {
            b
        }

        #[verifier(external_fn_specification)]
        fn y(b: bool, c: bool) -> (ret_b: bool)
        {
            x(b)
        }
    } => Err(err) => assert_vir_error_msg(err, "external_fn_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] mismatch_params2 verus_code! {
        #[verifier(external)]
        fn x(b: bool) -> bool {
            b
        }

        #[verifier(external_fn_specification)]
        fn y(b: u8) -> (ret_b: bool)
        {
            x(false)
        }
    } => Err(err) => assert_vir_error_msg(err, "external_fn_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] mismatch_return verus_code! {
        #[verifier(external)]
        fn x<'a>(b: &'a mut bool) -> &'a mut bool {
            b
        }

        #[verifier(external_fn_specification)]
        fn y<'a>(b: &'a mut bool) -> (ret_b: &'a bool)
        {
            x(b)
        }
    } => Err(err) => assert_vir_error_msg(err, "external_fn_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] mismatch_type_params verus_code! {
        #[verifier(external)]
        fn x<S, T>(s: S, t: T) {
        }

        #[verifier(external_fn_specification)]
        fn y<S, T>(s: T, t: S)
        {
            x(t, s)
        }
    } => Err(err) => assert_vir_error_msg(err, "external_fn_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] mismatch_lt_params verus_code! {
        #[verifier(external)]
        fn x<'a, 'b>(u: &'a u8, v: &'b u8) -> &'a u8 {
            u
        }

        #[verifier(external_fn_specification)]
        fn y<'a, 'b>(u: &'b u8, v: &'a u8) -> &'a u8 {
            x(v, u)
        }
    } => Err(err) => assert_vir_error_msg(err, "external_fn_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] mismatch_extra_trait_bound verus_code! {
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T: Copy>(a: &mut T, b: &mut T)
        {
            core::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "external_fn_specification requires function type signature to match exactly (trait bound mismatch)")
}

test_verify_one_file! {
    #[test] mismatch_extra_trait_bound2 verus_code! {
        #[verifier(external)]
        fn sw<T>(a: &mut T, b: &mut T) {
        }

        #[verifier(external_fn_specification)]
        fn swap_requires_ensures<T: Copy>(a: &mut T, b: &mut T)
        {
            sw(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "external_fn_specification requires function type signature to match exactly (trait bound mismatch)")
}

test_verify_one_file! {
    #[test] mismatch_trait_bound verus_code! {
        trait Tr1 { }
        trait Tr2 { }

        struct Stuff { }
        impl Tr1 for Stuff { }

        #[verifier(external)]
        fn x<T: Tr1>() {
        }

        #[verifier(external_fn_specification)]
        fn y<T: Tr2>()
        {
            x::<Stuff>()
        }
    } => Err(err) => assert_vir_error_msg(err, "external_fn_specification requires function type signature to match exactly (trait bound mismatch)")
}

test_verify_one_file! {
    #[test] correct_trait_bound verus_code! {
        trait Tr1 { }

        struct Stuff { }
        impl Tr1 for Stuff { }

        #[verifier(external)]
        fn x<T: Tr1>() {
        }

        #[verifier(external_fn_specification)]
        fn y<T: Tr1>()
        {
            x::<Stuff>()
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] correct_trait_bound_renamed verus_code! {
        trait Tr1 { }

        struct Stuff { }
        impl Tr1 for Stuff { }

        #[verifier(external)]
        fn x<T: Tr1>() {
        }

        #[verifier(external_fn_specification)]
        fn y<S: Tr1>()
        {
            x::<S>()
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mismatch_trait_bound2 verus_code! {
        trait Tr1 { }

        #[verifier(external)]
        fn f1<S, T: Tr1>(x: S, y: T) {
        }

        #[verifier(external_fn_specification)]
        fn f2<T: Tr1, S>(x: T, y: S)
        {
            f1(y, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "external_fn_specification requires function type signature to match exactly (trait bound mismatch)")
}

test_verify_one_file! {
    #[test] mismatch_trait_bound3 verus_code! {
        trait Tr1 { }

        #[verifier(external)]
        fn f1<S, T: Tr1>() {
        }

        #[verifier(external_fn_specification)]
        fn f2<T: Tr1, S>()
        {
            f1::<S, T>()
        }
    } => Err(err) => assert_vir_error_msg(err, "external_fn_specification requires function type signature to match exactly (trait bound mismatch)")
}

// Lifetime checking

test_verify_one_file! {
    #[test] checking_lifetime verus_code! {
        use vstd::*;
        fn main(x: u8) {
            let mut a = x;
            core::mem::swap(&mut a, &mut a);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `a` as mutable more than once at a time")
}

test_verify_one_file! {
    #[test] checking_lifetime2 verus_code! {
        #[verifier(external)]
        fn foo<'a>(b: &'a bool) -> &'a bool {
            b
        }

        #[verifier(external_fn_specification)]
        fn foo_requires_ensures<'a>(b: &'a bool) -> &'a bool
        {
            foo(b)
        }

        fn test() {
            let mut x: bool = true;
            let y = foo(&x);
            x = false;
            foo(y);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot assign to `x` because it is borrowed")
}

// Check that you can't apply it to a trait function

test_verify_one_file! {
    #[test] apply_to_trait_fn_not_supported verus_code! {
        struct X { }

        trait Tr { fn f(); }

        #[verifier(external)]
        impl Tr for X {
            fn f() { }
        }

        #[verifier(external_fn_specification)]
        fn ex_f() {
            X::f()
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` not supported for trait functions")
}

// Associated functions

test_verify_one_file! {
    #[test] apply_to_assoc_fn_not_supported verus_code! {
        struct X { }

        impl X {
            #[verifier(external)]
            fn f() { }
        }

        // This shouldn't be hard to support

        #[verifier(external_fn_specification)]
        fn ex_f() {
            X::f()
        }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` not yet supported for associated methods")
}

// Other

test_verify_one_file! {
    #[test] test_attr_with_external verus_code! {
        #[verifier(external_fn_specification)]
        #[verifier(external)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "a function cannot be marked both `external_fn_specification` and `external`")
}

test_verify_one_file! {
    #[test] test_attr_with_external_body verus_code! {
        #[verifier(external_fn_specification)]
        #[verifier(external_body)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "a function cannot be marked both `external_fn_specification` and `external_body`")
}

test_verify_one_file! {
    #[test] test_attr_with_builtin verus_code! {
        #[verifier(external_fn_specification)]
        pub fn x() {
            admit()
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot apply `external_fn_specification` to Verus builtin functions")
}
