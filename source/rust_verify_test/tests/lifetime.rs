#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] consume_once verus_code! {
        proof fn consume<A>(tracked a: A) {
        }

        proof fn test1<A>(tracked a: A) {
            consume(a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] consume_twice verus_code! {
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked a: A) {
            consume(a);
            consume(a);
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_exp verus_code! {
        proof fn consume<A>(tracked a: A) -> int { 2 }
        proof fn test1<A>(tracked a: A) -> int {
            consume(a) + consume(a)
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_via_temp verus_code! {
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked a: A) {
            let tracked b = a;
            consume(a);
            consume(b);
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_via_assign verus_code! {
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked a: A, tracked b: A) {
            let tracked mut x = a;
            x = b;
            consume(x);
            consume(b);
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_via_return verus_code! {
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked a: A) -> (tracked b: A) {
            consume(a);
            a
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_via_return_pair verus_code! {
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked a: A) -> (tracked b: (A, A)) {
            (a, a)
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_via_return_struct verus_code! {
        struct P<A, B> { a: A, b: B }
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked x: A) -> (tracked b: P<A, A>) {
            P { a: x, b: x }
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_via_args verus_code! {
        proof fn f<A>(tracked a: A) -> (tracked b: A) { a }
        proof fn g<A>(tracked x: A, tracked y: A) { }
        proof fn h<A>(tracked a: A) {
            g(f(a), f(a))
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_via_spec_args verus_code! {
        proof fn f<A>(tracked a: A) -> (tracked b: A) { a }
        proof fn g<A>(x: A, y: A) { }
        proof fn h<A>(tracked a: A) {
            g(f(a), f(a))
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function with mode proof")
}

test_verify_one_file! {
    #[test] consume_fields_ok verus_code! {
        struct P<A, B> { a: A, b: B }
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A, B>(tracked p: P<A, B>) {
            consume(p.a);
            consume(p.b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] consume_twice_fields verus_code! {
        struct P<A, B> { a: A, b: B }
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A, B>(tracked p: P<A, B>) {
            consume(p.a);
            consume(p.a);
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_field_struct verus_code! {
        struct P<A, B> { a: A, b: B }
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A, B>(tracked p: P<A, B>) {
            consume(p.a);
            consume(p);
        }
    } => Err(err) => assert_vir_error_msg(err, "use of partially moved value")
}

test_verify_one_file! {
    #[test] consume_twice_is verus_code! {
        #[is_variant]
        pub enum Option<A> {
            None,
            Some(A)
        }
        proof fn id<A>(tracked x: A) -> (tracked y: A) {
            x
        }
        proof fn test<A>(tracked x: A) {
            // Note that builtin::is_variant is a spec function but
            // allows proof arguments
            let s = builtin::is_variant(id(Option::Some(x)), "None");
            let s = builtin::is_variant(id(Option::Some(x)), "None");
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_get verus_code! {
        #[is_variant]
        pub enum Option<A> {
            None,
            Some(A)
        }
        proof fn id<A>(tracked x: A) -> (tracked y: A) {
            x
        }
        proof fn test<A>(tracked x: A) {
            let s = builtin::get_variant_field::<_, A>(id(Option::Some(x)), "Some", "0");
            let s = builtin::get_variant_field::<_, A>(id(Option::Some(x)), "Some", "0");
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] borrow_twice verus_code! {
        proof fn f(tracked x: &mut u8, tracked y: &mut u8) {}
        proof fn g(tracked x: &mut u8, tracked y: &mut u8) {
            f(x, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot borrow `*x` as mutable more than once at a time")
}

test_verify_one_file! {
    #[test] borrow_local_ok verus_code! {
        proof fn borrow<A>(tracked a: &mut A, tracked b: &mut A) {}
        proof fn test1<A>(tracked a: A, tracked b: A) {
            let tracked mut x = a;
            let tracked mut y = b;
            borrow(&mut x, &mut y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] borrow_local_twice verus_code! {
        proof fn borrow<A>(tracked a: &mut A, tracked b: &mut A) {}
        proof fn test1<A>(tracked a: A, tracked b: A) {
            let tracked mut x = a;
            let tracked mut y = b;
            borrow(&mut x, &mut x);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot borrow `x` as mutable more than once at a time")
}

test_verify_one_file! {
    #[test] consume_tracked_twice verus_code! {
        proof fn f(tracked x: u8, tracked y: u8) {}
        fn g(x: Tracked<u8>, y: Tracked<u8>) {
            proof {
                f(x.get(), x.get())
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] borrow_tracked_twice verus_code! {
        proof fn f(tracked x: &mut u8, tracked y: &mut u8) {}
        fn g(x: Tracked<u8>, y: Tracked<u8>) {
            let mut x = x;
            proof {
                f(x.borrow_mut(), x.borrow_mut());
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot borrow `x` as mutable more than once at a time")
}

test_verify_one_file! {
    #[test] borrow_tracked_twice_ok verus_code! {
        proof fn f(tracked x: &mut u8) {}
        fn g(x: Tracked<u8>) {
            let mut x = x;
            proof {
                f(x.borrow_mut());
                f(x.borrow_mut());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] consume_twice_if verus_code! {
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked a: A, b: bool) {
            if b {
                consume(a);
                consume(a);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_else verus_code! {
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked a: A, b: bool) {
            if b {
            } else {
                consume(a);
                consume(a);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_if_return verus_code! {
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked a: A, tracked a2: A, b: bool) -> (tracked z: A) {
            consume(a);
            if b {
                return a;
            }
            a2
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_match verus_code! {
        enum E<A> { X(A), Y }
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked e: E<A>) {
            match e {
                E::X(x) => {}
                E::Y => {}
            }
            consume(e);
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] if_branch_uninit verus_code! {
        struct S {}
        proof fn test(b: bool) -> (tracked t: S) {
            let tracked mut s: S;
            if b { s = S {}; }
            s
        }
    } => Err(err) => assert_vir_error_msg(err, "used binding `s` is possibly-uninitialized")
}

test_verify_one_file! {
    #[test] match_branch_uninit verus_code! {
        struct S {}
        proof fn test(b: bool) -> (tracked t: S) {
            let tracked mut s: S;
            match b { _ if true => { s = S {}; } _ => {} }
            s
        }
    } => Err(err) => assert_vir_error_msg(err, "used binding `s` is possibly-uninitialized")
}

test_verify_one_file! {
    #[test] return_wrong_lifetime1 verus_code! {
        proof fn f<'a, 'b>(tracked x: &'a u32, tracked y: &'a u32, tracked z: &'b u32) -> tracked &'b u32 {
            y
        }
    } => Err(err) => assert_vir_error_msg(err, "lifetime may not live long enough")
}

test_verify_one_file! {
    #[test] return_wrong_lifetime2 verus_code! {
        proof fn f<'a, 'b>(tracked x: &'a u32, tracked y: &'a u32, tracked z: &'b u32) -> tracked &'b u32 {
            z
        }

        proof fn g<'a, 'b>(tracked x: &'a u32, tracked y: &'a u32, tracked z: &'b u32) -> tracked &'b u32 {
            f(z, z, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "lifetime may not live long enough")
}

test_verify_one_file! {
    #[test] lifetime_bounds_proof verus_code! {
        #[verifier(external_body)]
        pub proof fn proof_to_ref<'a, T: 'a>(tracked t: T) -> (tracked t2: &'a T)
            ensures t == *t2
        {
            unimplemented!();
        }

        pub struct Foo<'a, T: 'a> {
            pub t: &'a T,
        }

        pub proof fn mk_foo<'a, T: 'a>(tracked t: T) -> (tracked t2: Foo<'a, T>) {
            Foo { t: proof_to_ref(t) }
        }

        impl<'a, T> Foo<'a, T> {
            proof fn mk_foo2(tracked t: T) -> (tracked t2: Self) {
                mk_foo(t)
            }
        }

        impl<T> Foo<'_, T> {
            proof fn mk_foo3(tracked t: T) -> (tracked t2: Self) {
                Foo::mk_foo2(t)
            }
        }

        impl<'a, T> Foo<'a, T> {
            proof fn mk_foo4(tracked t: T) -> (tracked t2: Self) {
                Foo::<'a, T>::mk_foo3(t)
            }
        }

        pub proof fn mk_foo5<'a, 'b: 'a, T: 'a, U: 'b>(tracked t: T, tracked u: U) -> (tracked r: (Foo<'a, T>, Foo<'b, U>)) {
            (
                Foo { t: proof_to_ref(t) },
                Foo { t: proof_to_ref(u) },
            )
        }

        proof fn bar<'a>(f: FnSpec(u32) -> bool, v: u32, foo: Foo<'a, u32>) -> bool {
            f(v)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // TODO: remove vstd when ghost is moved to builtin
    #[test] lifetime_bounds_exec ["vstd"] => verus_code! {
        #[verifier(external_body)]
        pub fn exec_to_ref<'a, T: 'a>(t: T) -> (t2: &'a T)
            ensures t == *t2
        {
            // definitely panic; we wouldn't want to actually implement this
            panic!();
        }

        pub struct Foo<'a, T: 'a> {
            pub t: &'a T,
        }

        pub fn mk_foo<'a, T: 'a>(t: T) -> (t2: Foo<'a, T>) {
            Foo { t: exec_to_ref(t) }
        }

        impl<'a, T> Foo<'a, T> {
            fn mk_foo2(t: T) -> (t2: Self) {
                mk_foo(t)
            }
        }

        impl<T> Foo<'_, T> {
            fn mk_foo3(t: T) -> (t2: Self) {
                Foo::mk_foo2(t)
            }
        }

        impl<'a, T> Foo<'a, T> {
            fn mk_foo4(t: T) -> (t2: Self) {
                Foo::<'a, T>::mk_foo3(t)
            }
        }

        pub fn mk_foo5<'a, 'b: 'a, T: 'a, U: 'b>(t: T, u: U) -> (Foo<'a, T>, Foo<'b, U>) {
            (
                Foo { t: exec_to_ref(t) },
                Foo { t: exec_to_ref(u) },
            )
        }

        fn bar<'a, F: Fn(u32) -> bool>(f: F, v: u32, foo: Foo<'a, u32>) -> Ghost<bool> {
            Ghost(f.requires((v,)))
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lifetime_copy_succeed verus_code! {
        #[verifier(external_body)]
        struct S<#[verifier(maybe_negative)]A, #[verifier(maybe_negative)]B>(A, std::marker::PhantomData<B>);

        #[verifier(external)]
        impl<A, B> Clone for S<A, B> { fn clone(&self) -> Self { panic!() } }
        impl<A: Copy, B> Copy for S<A, B> {}

        struct Q {}

        proof fn f(tracked x: S<u8, Q>) -> tracked (S<u8, Q>, S<u8, Q>) {
            (x, x)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lifetime_copy_fail verus_code! {
        #[verifier(external_body)]
        struct S<#[verifier(maybe_negative)]A, #[verifier(maybe_negative)]B>(A, std::marker::PhantomData<B>);

        #[verifier(external)]
        impl<A, B> Clone for S<A, B> { fn clone(&self) -> Self { panic!() } }
        impl<A: Copy, B> Copy for S<A, B> {}

        struct Q {}

        proof fn f(tracked x: S<Q, u8>) -> tracked (S<Q, u8>, S<Q, u8>) {
            (x, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] lifetime_spec_const verus_code! {
        // from https://github.com/verus-lang/verus/issues/563
        pub spec const CONST_VALUE: u32 = 32;
        #[verifier(external_body)]
        struct Data { }
        impl Data {
            proof fn foo() {
                let value: u32 = CONST_VALUE;
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_no_lifetime_mut_check ["--no-lifetime"] => verus_code! {
        fn takesmut(x: &mut u32) { }

        fn test() {
            let x: u32 = 5;
            takesmut(&mut x);
        }
    } => Err(err) => assert_vir_error_msg(err, "variable `x` is not marked mutable")
}

test_verify_one_file! {
    #[test] test_ghost_at_assignment_mut_check_issue424 verus_code! {
        fn foo() {
            let a: Ghost<nat> = Ghost(3);
            proof {
                a@ = 4;
            }
            assert(a@ == 4);
        }
    } => Err(err) => assert_vir_error_msg(err, "variable `a` is not marked mutable")
}

// TODO Currently this causes a panic. However, it definitely needs to error,
// so we should fix the test and un-ignore it.

test_verify_one_file! {
    #[ignore] #[test] test_ghost_at_assignment_double_assignment verus_code! {
        fn foo() {
            let a: Ghost<nat>;
            proof {
                a@ = 4;
                a@ = 7;
            }
            assert(a@ == 4);
            assert(a@ == 7);
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "variable `a` is not marked mutable")
}

test_verify_one_file! {
    #[test] assign_twice verus_code! {
        fn test() {
            let x: u8;
            x = 5;
            x = 7;
            assert(false);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot assign twice to immutable variable `x`")
}

test_verify_one_file_with_options! {
    #[test] assign_twice_no_lifetime ["--no-lifetime"] => verus_code! {
        // It's fine to accept this because --no-lifetime means we don't
        // have any real guarantees. It would also be fine to error here.
        fn test() {
            let x: u8;
            x = 5;
            x = 7;
            assert(false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tracked_static_ref_checks_outlives verus_code! {
        pub struct X { }
        pub proof fn test<'a>(tracked x: &'a X) {
            // Make sure we disallow this (otherwise we would be able to upgrade
            // a reference &'a to &'static)
            let y = vstd::modes::tracked_static_ref(x);
        }
    } => Err(err) => assert_vir_error_msg(err, "borrowed data escapes outside of function")
}
