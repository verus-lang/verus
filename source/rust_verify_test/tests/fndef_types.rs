#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] basic_test ["vstd"] => verus_code! {
        fn llama(x: u8) -> (b: bool)
            requires x == 4 || x == 7,
            ensures b == (x == 4)
        {
            x == 4
        }

        fn test() {
            let t = llama;

            let b = t(4);
            assert(b);

            let b = t(7);
            assert(!b);

            assert(forall |x| (x == 4 || x == 7) ==> call_requires(llama, (x,)));
            assert(forall |x, y| call_ensures(llama, (x,), y) ==> x == 4 ==> y);
            assert(forall |x, y| call_ensures(llama, (x,), y) ==> x == 7 ==> !y);
        }

        fn test2() {
            let t = llama;

            let b = t(4);
            assert(!b);     // FAILS
        }

        fn test3() {
            let t = llama;

            t(12); // FAILS
        }

        fn test4() {
            assert(forall |x| (x == 5) ==> call_requires(llama, (x,))); // FAILS
        }

        fn test5() {
            assert(forall |x, y| call_ensures(llama, (x,), y) ==> x == 4 ==> !y); // FAILS
        }

        fn takes_fn1<F: Fn(u8) -> bool>(f: F)
            requires
                call_requires(f, (4,)),
                call_requires(f, (7,)),
                forall |x, y| call_ensures(f, (x,), y) ==> x == 4 ==> y
        {
        }

        fn test_take1() {
            takes_fn1(llama);
        }

        fn takes_fn2<F: Fn(u8) -> bool>(f: F)
            requires
                call_requires(f, (6,)),
        {
        }

        fn test_take2() {
            takes_fn2(llama); // FAILS
        }

        fn takes_fn3<F: Fn(u8) -> bool>(f: F)
            requires
                forall |x, y| call_ensures(f, (x,), y) ==> x == 7 ==> y
        {
        }

        fn test_take3() {
            takes_fn3(llama); // FAILS
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] generics_test ["vstd"] => verus_code! {
        fn llama<T>(x: T, y: T, z: T) -> (b: bool)
            requires x == y,
            ensures b == (y == z),
        {
            // We can't actually implement this, but it doesn't matter for the test
            assume(false);
            true
        }

        fn test() {
            let t = llama;

            let b = t(4, 4, 6);
            assert(!b);

            let b = t(4, 4, 4);
            assert(b);

            assert(forall |x: u8, y: u8, z: u8| (x == y) ==> call_requires(llama, (x,y,z)));
            assert(forall |x: u8, y: u8, z: u8, b| call_ensures(llama, (x,y,z),b) ==> b == (y == z));
        }

        fn test2() {
            let t = llama;

            let b = t(4, 4, 4);
            assert(!b);     // FAILS
        }

        fn test3() {
            let t = llama;

            t(12, 13, 14); // FAILS
        }

        fn test4() {
            assert(forall |x: u8, y: u8, z: u8| (y == z) ==> call_requires(llama, (x,y,z))); // FAILS
        }

        fn test5() {
            assert(forall |x: u8, y: u8, z: u8, b| call_ensures(llama, (x,y,z),b) ==> b == (y != z)); // FAILS
        }

        struct X { x: u8 }

        fn takes_fn1<F: Fn(X, X, X) -> bool>(f: F)
            requires
                call_requires(f, (X { x: 4 }, X { x: 4 } , X { x: 4 })),
                call_requires(f, (X { x: 7 }, X { x: 7 } , X { x: 4 })),
                forall |x: X, y: X, z: X, b| call_ensures(f, (x,y,z), b) ==> b == (y == z)
        {
        }

        fn test_take1() {
            takes_fn1(llama);
        }

        fn takes_fn2<F: Fn(u8, u8, u8) -> bool>(f: F)
            requires
                call_requires(f, (6,7,8)),
        {
        }

        fn test_take2() {
            takes_fn2(llama); // FAILS
        }

        fn takes_fn3<F: Fn(u8, u8, u8) -> bool>(f: F)
            requires
                forall |x: u8, y: u8, z: u8, b| call_ensures(f, (x,y,z), b) ==> b == (y != z)
        {
        }

        fn test_take3() {
            takes_fn3(llama); // FAILS
        }

        fn takes_fn4<T, F: Fn(T, T, T) -> bool>(f: F)
            requires
                forall |x: T, y: T, z: T, b| call_ensures(f, (x,y,z), b) ==> b == (y != z)
        {
        }

        fn test_take4() {
            takes_fn4(llama::<u8>); // FAILS
        }

    } => Err(err) => assert_fails(err, 7)
}

test_verify_one_file_with_options! {
    #[test] with_trait ["vstd"] => verus_code! {
        trait Tr : Sized {
            fn llama(self, y: Self, z: Self) -> (b: bool)
                requires self == y,
                ensures b == (y == z);
        }

        struct X {
            t: u8,
        }

        impl Tr for X {
            fn llama(self, y: Self, z: Self) -> (b: bool)
            {
                assume(false);
                true
            }
        }

        fn test() {
            let t = <X as Tr>::llama;

            let x = X { t: 4 };
            let y = X { t: 4 };
            let z = X { t: 6 };

            let b = t(x, y, z);
            assert(!b);

            let x = X { t: 4 };
            let y = X { t: 4 };
            let z = X { t: 4 };

            let b = t(x, y, z);
            assert(b);

            assert(forall |x: X, y: X, z: X| (x == y) ==> call_requires(X::llama, (x,y,z)));
            assert(forall |x: X, y: X, z: X, b| call_ensures(X::llama, (x,y,z),b) ==> b == (y == z));
        }

        fn test2() {
            let t = <X as Tr>::llama;

            let x = X { t: 4 };
            let y = X { t: 4 };
            let z = X { t: 4 };

            let b = t(x, y, z);
            assert(!b);     // FAILS
        }

        fn test3() {
            let t = <X as Tr>::llama;

            let x = X { t: 12 };
            let y = X { t: 13 };
            let z = X { t: 14 };

            t(x, y, z); // FAILS
        }

        fn test4() {
            assert(forall |x: X, y: X, z: X| (y == z) ==> call_requires(X::llama, (x,y,z))); // FAILS
        }

        fn test5() {
            assert(forall |x: X, y: X, z: X, b| call_ensures(X::llama, (x,y,z),b) ==> b == (y != z)); // FAILS
        }

        fn takes_fn1<F: Fn(X, X, X) -> bool>(f: F)
            requires
                call_requires(f, (X { t: 4 }, X { t: 4 } , X { t: 4 })),
                call_requires(f, (X { t: 7 }, X { t: 7 } , X { t: 4 })),
                forall |x: X, y: X, z: X, b| call_ensures(f, (x,y,z), b) ==> b == (y == z)
        {
        }

        fn test_take1() {
            takes_fn1(X::llama);
        }

        fn takes_fn2<F: Fn(X, X, X) -> bool>(f: F)
            requires
                call_requires(f, (X { t: 6 }, X { t: 7 }, X { t: 8 })),
        {
        }

        fn test_take2() {
            takes_fn2(X::llama); // FAILS
        }

        fn takes_fn3<F: Fn(X, X, X) -> bool>(f: F)
            requires
                forall |x: X, y: X, z: X, b| call_ensures(f, (x,y,z), b) ==> b == (y != z)
        {
        }

        fn test_take3() {
            takes_fn3(X::llama); // FAILS
        }

        fn takes_fn4<T, F: Fn(T, T, T) -> bool>(f: F)
            requires
                forall |x: T, y: T, z: T, b| call_ensures(f, (x,y,z), b) ==> b == (y != z)
        {
        }

        fn test_take4() {
            takes_fn4(X::llama); // FAILS
        }
    } => Err(err) => assert_fails(err, 7)
}

test_verify_one_file! {
    #[test] spec_fn_error verus_code! {
        spec fn foo() -> bool { true }

        fn test() {
            let x = foo;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use a function as a value unless it as mode 'exec'")
}

test_verify_one_file! {
    #[test] proof_fn_error verus_code! {
        proof fn foo() -> bool { true }

        fn test() {
            let x = foo;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use a function as a value unless it as mode 'exec'")
}

test_verify_one_file! {
    #[test] proof_fn_error2 verus_code! {
        proof fn foo() -> bool { true }

        spec fn test() -> bool {
            call_requires(foo, ())
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use a function as a value unless it as mode 'exec'")
}

test_verify_one_file! {
    #[test] external_fn_error verus_code! {
        #[verifier::external]
        fn foo() -> bool { true }

        spec fn test() -> bool {
            call_requires(foo, ())
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function marked `external`")
}

test_verify_one_file! {
    #[test] mut_params_error verus_code! {
        fn stuff(x: &mut u8) { }

        fn test() {
            let x = stuff;
        }
    } => Err(err) => assert_vir_error_msg(err, "not supported: using a function that takes '&mut' params as a value")
}

test_verify_one_file! {
    #[test] recursion1 verus_code! {
        fn test(x: u8)
            requires call_requires(test, (x,)),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion2 verus_code! {
        spec fn s(x: u8) -> bool {
            call_requires(test, (x,))
        }

        fn test(x: u8)
            requires s(x),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion3 verus_code! {
        spec fn s(x: u8) -> bool {
            call_requires(test, (x,))
        }

        fn test(x: u8)
            ensures s(x),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion4 verus_code! {
        spec fn s(x: u8) -> bool {
            call_ensures(test, (x,), ())
        }

        fn test(x: u8)
            requires s(x),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion5_okay verus_code! {
        // This is ok because we're only referencing the *type* FnDef(test),
        // but not the 'requires' or 'ensures',
        // which is just a singleton.
        fn test(x: u8)
            requires test == test,
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] recursion6_via_fn_once verus_code! {
        spec fn foo<F: FnOnce(u8) -> bool>(f: F) -> bool {
            call_requires(f, (0,))
        }

        fn test(x: u8) -> bool
            requires foo(test)
        {
            false
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion7_via_fn_once verus_code! {
        spec fn foo<F: FnOnce<(u8,)>>(f: F) -> bool {
            call_requires(f, (0,))
        }

        fn test(x: u8) -> bool
            requires foo(test)
        {
            false
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion8_via_fn_once verus_code! {
        spec fn foo<F: FnOnce(u8) -> bool>(f: F) -> bool;

        fn test(x: u8) -> bool
            requires foo(test)
        {
            false
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion9_via_fn_once_with_ref verus_code! {
        spec fn foo<F: FnOnce(u8) -> bool>(f: F) -> bool;

        fn test(x: u8) -> bool
            requires foo(&test)
        {
            false
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion10_via_fn verus_code! {
        spec fn foo<F: Fn(u8)>(f: F) -> bool {
            call_requires(f, (0,))
        }

        fn test(x: u8)
            requires foo(test)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion11_via_fn_mut verus_code! {
        spec fn foo<F: FnMut(u8)>(f: F) -> bool {
            call_requires(f, (0,))
        }

        fn test(x: u8)
            requires foo(test)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion12_via_trait_impl_in_function_generics verus_code! {
        trait Tr {
            spec fn stuff(&self) -> bool;
        }

        trait Qr {
        }

        impl<T> Tr for T
          where T: Qr
        {
            // cyclic dependency with alpaca
            spec fn stuff(&self) -> bool {
                alpaca(*self)
            }
        }

        spec fn alpaca<T: Qr>(qr: T) -> bool {
            // depends on the bound `T: Tr`
            // which depends on the implementation `T: Qr --> T: Tr`
            // which in turn depends on `alpaca`
            call_requires(test::<T>, (0,))
        }

        // The definition of `test` itself is fine
        fn test<T: Tr>(x: u8)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "self-reference in a definition")
}

test_verify_one_file! {
    #[test] recursion13_via_trait_impl_in_function_generics verus_code! {
        trait Tr {
            spec fn stuff(&self) -> bool;
        }

        struct X { }

        impl Tr for X
        {
            // cyclic dependency with alpaca
            spec fn stuff(&self) -> bool {
                alpaca()
            }
        }

        spec fn alpaca() -> bool {
            // depends on the bound `X: Tr`
            // which depends on the above trait impl
            // which in turn depends on `alpaca`
            call_ensures(test::<X>, (0,), ())
        }

        // The definition of `test` itself is fine
        fn test<T: Tr>(x: u8)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "self-reference in a definition")
}

test_verify_one_file! {
    #[test] recursion14_via_fn_with_requires_ensures verus_code! {
        use vstd::prelude::*;

        spec fn foo<F: FnWithRequiresEnsures<(u8,), ()>>(f: F) -> bool {
            f.requires((0,))
        }

        fn test(x: u8)
            requires foo(test)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion15_via_fn_with_requires_ensures verus_code! {
        use vstd::prelude::*;

        spec fn foo<F: FnWithRequiresEnsures<(u8,), ()>>(f: F) -> bool {
            f.requires((0,))
        }

        fn test(x: u8)
            requires foo(test)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion16_via_trait_impl_in_function_generics_fn_with_requires_ensures verus_code! {
        use vstd::prelude::*;

        trait Tr {
            spec fn stuff(&self) -> bool;
        }

        struct X { }

        impl Tr for X
        {
            // cyclic dependency with alpaca
            spec fn stuff(&self) -> bool {
                alpaca()
            }
        }

        spec fn alpaca() -> bool {
            // depends on the bound `X: Tr`
            // which depends on the above trait impl
            // which in turn depends on `alpaca`
            (test::<X>).requires((0,))
        }

        // The definition of `test` itself is fine
        fn test<T: Tr>(x: u8)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "self-reference in a definition")
}

test_verify_one_file! {
    #[test] recursion17_via_const verus_code! {
        spec const x: bool = call_requires(f, (0,));

        fn f(y: u8)
            requires (y == 0) != x,
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion18_via_trait_function_with_extended_ensures verus_code! {
        trait Tr {
            fn stuff(&self) -> bool;
        }

        struct X { }

        impl Tr for X {
            fn stuff(&self) -> (res: bool)
                ensures call_ensures(X::stuff, (&self,), res)
            {
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] recursion19_via_trait_function_ensures verus_code! {
        trait Tr {
            fn stuff(&self) -> (res: bool)
                ensures call_ensures(Self::stuff, (&self,), res);
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] recursion20_via_trait_function_requires verus_code! {
        trait Tr {
            fn stuff(&self) -> (res: bool)
                requires call_requires(Self::stuff, (&self,));
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

test_verify_one_file! {
    #[test] exec_calling1 verus_code! {
        use vstd::*;
        fn a() {
            let x = b;
            x(0);
        }

        fn b(i: u8)
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] exec_calling2 verus_code! {
        use vstd::*;
        fn a() {
            let x = b;
            x();
        }

        fn b()
        {
        }
    } => Ok(())
}

// TODO this is kind of a bad error message, but we should revisit and allow this
test_verify_one_file! {
    #[test] exec_recursion_mutual verus_code! {
        use vstd::*;

        fn a() {
            let x = b;
            x();
        }

        fn b() {
            let y = a;
            y();
        }
    } => Err(err) => assert_vir_error_msg(err, "cyclic dependency in the requires/ensures of function")
}

// ignore; no-vstd flag doesn't work with test harness right now
test_verify_one_file! {
    #[ignore] #[test] exec_calling_no_vstd verus_code! {
        fn a() {
            let x = b;
            x(0);
        }

        fn b(i: u8)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "Non-static calls are not supported with --no-vstd")
}

test_verify_one_file! {
    #[test] test_function_takes_trait_bound verus_code! {
        trait Tr {
            spec fn foo(&self) -> bool;
        }

        struct X { u: u64, }

        impl Tr for X {
            spec fn foo(&self) -> bool;
        }

        fn stuff<T: Tr>(t: T)
            requires t.foo();

        proof fn test(x: X) {
            assert(call_requires(stuff::<X>, (x,)) <== x.foo());
        }

        proof fn test2<T: Tr>(t: T) {
            assert(call_requires(stuff::<T>, (t,)) <== t.foo());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_by_compute verus_code! {
        fn stuff(x: u8)
            requires x == 0,
        { }

        proof fn test2() {
            assert(call_requires(stuff, (0,)) == true) by(compute);
        }

        proof fn test() {
            // We could support this, but it probably isn't very important
            assert(call_requires(stuff, (0,)) == true) by(compute_only); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_requires_ensures_off_trait_func verus_code! {
        trait Tr {
            fn stuff(&self, x: u8) -> (b: bool)
                requires x <= 5,
                ensures (b == (x == 0));
        }

        struct X { }

        impl Tr for X {
            fn stuff(&self, x: u8) -> (b: bool)
            {
                x == 0
            }
        }

        proof fn test_req(x: X) {
            assert(call_requires(<X as Tr>::stuff, (&x, 0)));
            assert(call_requires(<X as Tr>::stuff, (&x, 20))); // FAILS
        }

        proof fn test_ens(x: X) {
            assert(!call_ensures(<X as Tr>::stuff, (&x, 0), false));
            assert(!call_ensures(<X as Tr>::stuff, (&x, 0), true)); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_requires_ensures_off_trait_func_generically verus_code! {
        trait Tr {
            fn stuff(&self, x: u8) -> (b: bool)
                requires x <= 5,
                ensures (b == (x == 0));
        }

        proof fn test_req<X: Tr>(x: X) {
            assert(call_requires(X::stuff, (&x, 0)));
            assert(call_requires(X::stuff, (&x, 20))); // FAILS
        }

        proof fn test_ens<X: Tr>(x: X) {
            assert(!call_ensures(X::stuff, (&x, 0), false));
            assert(!call_ensures(X::stuff, (&x, 0), true)); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_ensures_extension verus_code! {
        trait Tr {
            fn stuff(&self) -> (res: u8)
                ensures res % 2 == 0;
        }

        struct X { t: u8 }

        impl Tr for X {
            fn stuff(&self) -> (res: u8)
                ensures 0 <= res <= self.t
            {
                0
            }
        }

        fn test1(t: u8, res: u8) {
            let x = X { t: t };
            assert(call_ensures(X::stuff, (&x,), res) ==> res % 2 == 0 && 0 <= res <= t);
        }

        fn test2() {
            let x = X { t: 20 };
            assert(!call_ensures(X::stuff, (&x,), 10)); // FAILS
        }

        fn test3<T: Tr>(t: T, res: u8) {
            assert(call_ensures(T::stuff, (&t,), res) ==> res % 2 == 0);
        }

        fn test4<T: Tr>(t: T) {
            assert(!call_ensures(T::stuff, (&t,), 4)); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_ensures_extension_1 verus_code! {
        // Similar to test_ensures_extension
        // but there's less code here so tests pruning still works correctly

        trait Tr {
            fn stuff(&self) -> (res: u8)
                ensures res % 2 == 0;
        }

        struct X { t: u8 }

        impl Tr for X {
            fn stuff(&self) -> (res: u8)
                ensures 0 <= res <= self.t
            {
                0
            }
        }

        fn test3<T: Tr>(t: T, res: u8) {
            assert(call_ensures(T::stuff, (&t,), res) ==> res % 2 == 0);
        }

        fn test4<T: Tr>(t: T) {
            assert(!call_ensures(T::stuff, (&t,), 4)); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_ensures_extension_2 verus_code! {
        // Similar to test_ensures_extension
        // but there's less code here so tests pruning still works correctly

        trait Tr {
            fn stuff(&self) -> (res: u8)
                ensures res % 2 == 0;
        }

        struct X { t: u8 }

        impl Tr for X {
            fn stuff(&self) -> (res: u8)
                ensures 0 <= res <= self.t
            {
                0
            }
        }

        fn test1(t: u8, res: u8) {
            let x = X { t: t };
            assert(call_ensures(X::stuff, (&x,), res) ==> res % 2 == 0 && 0 <= res <= t);
        }

        fn test2() {
            let x = X { t: 20 };
            assert(!call_ensures(X::stuff, (&x,), 10)); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_ensures_extension_3 verus_code! {
        // Similar to test_ensures_extension
        // but without an 'ensures' on the original 'stuff'

        trait Tr {
            fn stuff(&self) -> (res: u8);
        }

        struct X { t: u8 }

        impl Tr for X {
            fn stuff(&self) -> (res: u8)
                ensures 0 <= res <= self.t
            {
                0
            }
        }

        fn test1(t: u8, res: u8) {
            let x = X { t: t };
            assert(call_ensures(X::stuff, (&x,), res) ==> 0 <= res <= t);
        }

        fn test2() {
            let x = X { t: 20 };
            assert(!call_ensures(X::stuff, (&x,), 10)); // FAILS
        }

        fn test4<T: Tr>(t: T) {
            assert(!call_ensures(T::stuff, (&t,), 4)); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_visibility verus_code! {
        fn stuff() { }

        pub open spec fn test() -> bool {
            call_ensures(stuff, (), ())
        }
    } => Err(err) => assert_vir_error_msg(err, "in pub open spec function, cannot refer to private function")
}

test_verify_one_file! {
    #[test] trait_method_use_emits_req_ens_axioms_for_impls verus_code! {
        trait VPartialEq {
            fn eq(&self, other: &Self) -> bool;
            fn ne(&self, other: &Self) -> bool;
        }

        trait VEq : VPartialEq {
            spec fn rel(&self, other: &Self) -> bool;

            proof fn reflexive(a: &Self)
                ensures a.rel(a);

            proof fn symmetric(a: &Self, b: &Self)
                ensures a.rel(b) ==> b.rel(a);

            proof fn transitive(a: &Self, b: &Self, c: &Self)
                requires a.rel(b), b.rel(c)
                ensures a.rel(c);

            proof fn fns_correct(a: &Self, b: &Self)
                ensures
                    // call_ensures is a verus builtin that means
                    // "this is a valid input-output pair for the function Self::eq"
                    call_ensures(Self::eq, (a, b), true) ==> a.rel(b),
                    call_ensures(Self::eq, (a, b), false) ==> !a.rel(b),

                    call_ensures(Self::ne, (a, b), true) ==> !a.rel(b),
                    call_ensures(Self::ne, (a, b), false) ==> a.rel(b);
        }

        // Example usage

        struct Mod2 { u: u64 }

        impl Mod2 {
            spec fn view(&self) -> int {
                (self.u % 2) as int
            }
        }

        impl VPartialEq for Mod2 {
            fn eq(&self, other: &Self) -> (b: bool)
                ensures b == (self@ == other@),
            {
                self.u % 2 == other.u % 2
            }

            fn ne(&self, other: &Self) -> (b: bool)
                ensures b == (self@ != other@),
            {
                self.u % 2 != other.u % 2
            }
        }

        impl VEq for Mod2 {
            spec fn rel(&self, other: &Self) -> bool {
                self@ == other@
            }

            // Proof that rel is an equivalence relation

            proof fn reflexive(a: &Self)
            { }

            proof fn symmetric(a: &Self, b: &Self)
            { }

            proof fn transitive(a: &Self, b: &Self, c: &Self)
            { }

            // Proof that `eq` and `ne` return the value of `rel`:

            proof fn fns_correct(a: &Self, b: &Self)
            {
                // Note that this requires the axioms for req and ens
                // for the Mod2::eq and Mod2::ne method impls.
                // However, we never directly reference call_ensures(Mod2::eq, ...)
                // anywhere. Instead, we only have the more general
                // call_ensures invocations from the ensures clause of fns_correct
                // in the trait declaration.
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_method_use_emits_req_ens_axioms_for_impls_fail verus_code! {
        trait VPartialEq {
            fn eq(&self, other: &Self) -> bool;
            fn ne(&self, other: &Self) -> bool;
        }

        trait VEq : VPartialEq {
            spec fn rel(&self, other: &Self) -> bool;

            proof fn reflexive(a: &Self)
                ensures a.rel(a);

            proof fn symmetric(a: &Self, b: &Self)
                ensures a.rel(b) ==> b.rel(a);

            proof fn transitive(a: &Self, b: &Self, c: &Self)
                requires a.rel(b), b.rel(c)
                ensures a.rel(c);

            proof fn fns_correct(a: &Self, b: &Self)
                ensures
                    call_ensures(Self::ne, (a, b), true) ==> !a.rel(b); // FAILS
        }

        // Example usage

        struct Mod2 { u: u64 }

        impl Mod2 {
            spec fn view(&self) -> int {
                (self.u % 2) as int
            }
        }

        impl VPartialEq for Mod2 {
            fn eq(&self, other: &Self) -> (b: bool)
                ensures b == (self@ == other@),
            {
                self.u % 2 == other.u % 2
            }

            fn ne(&self, other: &Self) -> (b: bool)
                ensures b == (self@ == other@),
            {
                self.u % 2 == other.u % 2
            }
        }

        impl VEq for Mod2 {
            spec fn rel(&self, other: &Self) -> bool {
                self@ == other@
            }

            // Proof that rel is an equivalence relation

            proof fn reflexive(a: &Self)
            { }

            proof fn symmetric(a: &Self, b: &Self)
            { }

            proof fn transitive(a: &Self, b: &Self, c: &Self)
            { }

            // Proof that `eq` and `ne` return the value of `rel`:

            proof fn fns_correct(a: &Self, b: &Self)
            {
                // Note that this requires the axioms for req and ens
                // for the Mod2::eq and Mod2::ne method impls.
                // However, we never directly reference call_ensures(Mod2::eq, ...)
                // anywhere. Instead, we only have the more general
                // call_ensures invocations from the ensures clause of fns_correct
                // in the trait declaration.
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] trait_default_method_call_ensures verus_code! {
        trait Tr {
            fn hello(i: u64, j: u64)
                ensures i == j,
            {
                assume(false);
            }
        }

        struct X<A> { a: A }

        impl<A> Tr for X<A> {
        }

        struct Y<A> { a: A }

        impl<A> Tr for Y<A> {
            fn hello(i: u64, j: u64)
                ensures i >= 5,
            {
                assume(false);
            }
        }

        fn test<T: Tr>(i: u64, j: u64) {
            assert(call_ensures(T::hello, (i, j), ()) ==> i == j);
        }

        fn test2(i: u64, j: u64) {
            assert(call_ensures(X::<bool>::hello, (i, j), ()) ==> i == j);
        }

        fn test3(i: u64, j: u64) {
            assert(call_ensures(Y::<bool>::hello, (i, j), ()) ==> i == j && i >= 5);
        }

        fn test4<T: Tr>(i: u64, j: u64) {
            assert(call_ensures(T::hello, (i, j), ()) ==> i == j);
            assert(call_ensures(X::<bool>::hello, (i, j), ()) ==> i == j);
            assert(call_ensures(Y::<bool>::hello, (i, j), ()) ==> i == j && i >= 5);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] trait_default_method_call_ensures_with_default_spec_fn verus_code! {
        trait Tr {
            spec fn stuff(i: u64, j: u64) -> bool { i == j }

            fn hello(i: u64, j: u64)
                ensures Self::stuff(i, j)
            {
                assume(false);
            }
        }

        struct X<A> { a: A }
        impl<A> Tr for X<A> {
        }

        struct Y<A> { a: A }
        impl<A> Tr for Y<A> {
            fn hello(i: u64, j: u64)
                ensures i >= 5, // and implied stuff()
            {
                assume(false);
            }
        }

        struct Z<A> { a: A }
        impl<A> Tr for Z<A> {
            spec fn stuff(i: u64, j: u64) -> bool { i == j + 1 }
        }

        struct W<A> { a: A }
        impl<A> Tr for W<A> {
            spec fn stuff(i: u64, j: u64) -> bool { i == j + 1 }

            fn hello(i: u64, j: u64)
                ensures i >= 5, // and implied stuff()
            {
                assume(false);
            }
        }

        struct U<A> { a: A }
        trait FromInt : Sized {
            spec fn from_int(i: u64) -> Self;
        }
        impl FromInt for bool {
            spec fn from_int(i: u64) -> Self { i == 4 }
        }
        impl<A: FromInt> Tr for U<A> {
            spec fn stuff(i: u64, j: u64) -> bool { A::from_int(i) == A::from_int(j) }
        }



        fn test<T: Tr>(i: u64, j: u64) {
            assert(call_ensures(T::hello, (i, j), ()) ==> T::stuff(i, j));
        }

        fn test_fail<T: Tr>(i: u64, j: u64) {
            assert(call_ensures(T::hello, (i, j), ()) ==> i == j); // FAILS
        }

        fn test2(i: u64, j: u64) {
            assert(call_ensures(X::<bool>::hello, (i, j), ()) ==> i == j);
        }

        fn test3(i: u64, j: u64) {
            assert(call_ensures(Y::<bool>::hello, (i, j), ()) ==> i == j && i >= 5);
        }

        fn test4(i: u64, j: u64) {
            assert(call_ensures(Z::<bool>::hello, (i, j), ()) ==> i == j + 1);
        }

        fn test4_fail(i: u64, j: u64) {
            assert(call_ensures(Z::<bool>::hello, (i, j), ()) ==> i == j); // FAILS
        }

        fn test5(i: u64, j: u64) {
            assert(call_ensures(W::<bool>::hello, (i, j), ()) ==> i == j + 1 && i >= 5);
        }

        fn test5_fail(i: u64, j: u64) {
            assert(call_ensures(W::<bool>::hello, (i, j), ()) ==> i == j); // FAILS
        }

        fn test6(i: u64, j: u64) {
            assert(call_ensures(U::<bool>::hello, (i, j), ()) ==> (i == 4) == (j == 4));
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] trait_default_method_call_requires_with_default_spec_fn verus_code! {
        trait Tr {
            spec fn stuff(i: u64, j: u64) -> bool { i == j }

            fn hello(i: u64, j: u64)
                requires Self::stuff(i, j)
            {
                assume(false);
            }
        }

        struct X<A> { a: A }
        impl<A> Tr for X<A> {
        }

        struct Y<A> { a: A }
        impl<A> Tr for Y<A> {
            fn hello(i: u64, j: u64)
            {
                assume(false);
            }
        }

        struct Z<A> { a: A }
        impl<A> Tr for Z<A> {
            spec fn stuff(i: u64, j: u64) -> bool { i == j + 1 }
        }

        struct W<A> { a: A }
        impl<A> Tr for W<A> {
            spec fn stuff(i: u64, j: u64) -> bool { i == j + 1 }

            fn hello(i: u64, j: u64)
            {
                assume(false);
            }
        }

        struct U<A> { a: A }
        trait FromInt : Sized {
            spec fn from_int(i: u64) -> Self;
        }
        impl FromInt for bool {
            spec fn from_int(i: u64) -> Self { i == 4 }
        }
        impl<A: FromInt> Tr for U<A> {
            spec fn stuff(i: u64, j: u64) -> bool { A::from_int(i) == A::from_int(j) }
        }



        fn test<T: Tr>(i: u64, j: u64) {
            assert(call_requires(T::hello, (i, j)) <== T::stuff(i, j));
        }

        fn test_fail<T: Tr>(i: u64, j: u64) {
            assert(call_requires(T::hello, (i, j)) <== i == j); // FAILS
        }

        fn test2(i: u64, j: u64) {
            assert(call_requires(X::<bool>::hello, (i, j)) <== i == j);
        }

        fn test3(i: u64, j: u64) {
            assert(call_requires(Y::<bool>::hello, (i, j)) <== i == j);
        }

        fn test4(i: u64, j: u64) {
            assert(call_requires(Z::<bool>::hello, (i, j)) <== i == j + 1);
        }

        fn test4_fail(i: u64, j: u64) {
            assert(call_requires(Z::<bool>::hello, (i, j)) <== i == j); // FAILS
        }

        fn test5(i: u64, j: u64) {
            assert(call_requires(W::<bool>::hello, (i, j)) <== i == j + 1);
        }

        fn test5_fail(i: u64, j: u64) {
            assert(call_requires(W::<bool>::hello, (i, j)) <== i == j); // FAILS
        }

        fn test6(i: u64, j: u64) {
            assert(call_requires(U::<bool>::hello, (i, j)) <== (i == 4) == (j == 4));
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] bound_vars_issue1005 verus_code! {
        use vstd::prelude::*;

        fn vec_map<T, U>(v: &Vec<T>, f: impl Fn(&T) -> U) -> (result: Vec<U>)
            requires
                forall |i| 0 <= i < v.len() ==> call_requires(f, (&v[i],)),
            ensures
                result.len() == v.len(),
                forall |i| 0 <= i < v.len() ==> call_ensures(f, (&v[i],), #[trigger] result[i])
        {
            assume(false);
            Vec::new()
        }

        fn double(x: &u8) -> (res: u8)
            requires 0 <= *x < 128,
            ensures res == 2 * (*x),
        {
            2 * (*x)
        }

        fn test_vec_map() {
            let mut v = Vec::new();
            v.push(0);
            v.push(10);
            v.push(20);

            let w = vec_map(&v, double);
            assert(w[2] == 40);
        }

        // Similar test, but with closures:

        struct X { }

        fn constrain<T>(t: T) -> T
            where T: for<'a> Fn(&'a X) -> &'a X
        {
            t
        }

        fn test() {
            let f = constrain(|x: &X| -> &X {
                &x
            });

            let x = X { };
            let t: &X = f(&x); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] unit_struct_as_fn_not_supported verus_code! {
        struct A();

        fn test()
        {
            let a = A;
        }
    } => Err(err) => assert_vir_error_msg(err, "using a datatype constructor as a function value")
}

test_verify_one_file! {
    #[test] unit_struct_as_fn_not_supported_self_ctor verus_code! {
        struct A();

        impl A {
            fn test()
            {
                let a = Self;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "using a datatype constructor as a function value")
}
