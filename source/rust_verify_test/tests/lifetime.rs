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
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_call verus_code! {
        tracked struct X { }

        proof fn take_two(tracked a: X, tracked b: X) {
        }

        proof fn foo(tracked x: X) {
            take_two(x, x);
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_exp verus_code! {
        proof fn consume<A>(tracked a: A) -> int { 2 }
        proof fn test1<A>(tracked a: A) -> int {
            consume(a) + consume(a)
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_via_temp verus_code! {
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked a: A) {
            let tracked b = a;
            consume(a);
            consume(b);
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
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
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_via_return verus_code! {
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked a: A) -> (tracked b: A) {
            consume(a);
            a
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_via_return_pair verus_code! {
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked a: A) -> (tracked b: (A, A)) {
            (a, a)
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_via_return_struct verus_code! {
        struct P<A, B> { a: A, b: B }
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A>(tracked x: A) -> (tracked b: P<A, A>) {
            P { a: x, b: x }
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_via_args verus_code! {
        proof fn f<A>(tracked a: A) -> (tracked b: A) { a }
        proof fn g<A>(tracked x: A, tracked y: A) { }
        proof fn h<A>(tracked a: A) {
            g(f(a), f(a))
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_via_spec_args verus_code! {
        proof fn f<A>(tracked a: A) -> (tracked b: A) { a }
        proof fn g<A>(x: A, y: A) { }
        proof fn h<A>(tracked a: A) {
            g(f(a), f(a))
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `crate::f` with mode proof")
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
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] consume_twice_field_struct verus_code! {
        struct P<A, B> { a: A, b: B }
        proof fn consume<A>(tracked a: A) {}
        proof fn test1<A, B>(tracked p: P<A, B>) {
            consume(p.a);
            consume(p);
        }
    } => Err(err) => assert_rust_error_msg(err, "use of partially moved value")
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
            // Note that verus_builtin::is_variant is a spec function but
            // allows proof arguments
            let s = verus_builtin::is_variant(id(Option::Some(x)), "None");
            let s = verus_builtin::is_variant(id(Option::Some(x)), "None");
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
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
            let s = verus_builtin::get_variant_field::<_, A>(id(Option::Some(x)), "Some", "0");
            let s = verus_builtin::get_variant_field::<_, A>(id(Option::Some(x)), "Some", "0");
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] borrow_twice verus_code! {
        proof fn f(tracked x: &mut u8, tracked y: &mut u8) {}
        proof fn g(tracked x: &mut u8, tracked y: &mut u8) {
            f(x, x)
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `*x` as mutable more than once at a time")
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
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `x` as mutable more than once at a time")
}

test_verify_one_file! {
    #[test] consume_tracked_twice verus_code! {
        struct X { }

        proof fn f(tracked x: X, tracked y: X) {}
        fn g(x: Tracked<X>, y: Tracked<X>) {
            proof {
                f(x.get(), x.get())
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
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
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `x` as mutable more than once at a time")
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
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
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
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
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
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
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
    } => Err(err) => assert_rust_error_msg(err, "use of partially moved value")
}

test_verify_one_file! {
    #[test] if_branch_uninit verus_code! {
        struct S {}
        proof fn test(b: bool) -> (tracked t: S) {
            let tracked mut s: S;
            if b { s = S {}; }
            s
        }
    } => Err(err) => assert_rust_error_msg(err, "used binding `s` is possibly-uninitialized")
}

test_verify_one_file! {
    #[test] match_branch_uninit verus_code! {
        struct S {}
        proof fn test(b: bool) -> (tracked t: S) {
            let tracked mut s: S;
            match b { _ if true => { s = S {}; } _ => {} }
            s
        }
    } => Err(err) => assert_rust_error_msg(err, "used binding `s` is possibly-uninitialized")
}

test_verify_one_file! {
    #[test] return_wrong_lifetime1 verus_code! {
        proof fn f<'a, 'b>(tracked x: &'a u32, tracked y: &'a u32, tracked z: &'b u32) -> tracked &'b u32 {
            y
        }
    } => Err(err) => assert_rust_error_msg(err, "lifetime may not live long enough")
}

test_verify_one_file! {
    #[test] return_wrong_lifetime2 verus_code! {
        proof fn f<'a, 'b>(tracked x: &'a u32, tracked y: &'a u32, tracked z: &'b u32) -> tracked &'b u32 {
            z
        }

        proof fn g<'a, 'b>(tracked x: &'a u32, tracked y: &'a u32, tracked z: &'b u32) -> tracked &'b u32 {
            f(z, z, x)
        }
    } => Err(err) => assert_rust_error_msg(err, "lifetime may not live long enough")
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

        proof fn bar<'a>(f: spec_fn(u32) -> bool, v: u32, foo: Foo<'a, u32>) -> bool {
            f(v)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lifetime_bounds_exec verus_code! {
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
            Ghost(call_requires(f, (v,)))
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lifetime_copy_succeed verus_code! {
        #[verifier(external_body)]
        #[verifier(reject_recursive_types(A))]
        #[verifier(reject_recursive_types(B))]
        struct S<'a, A, const N: u8, B>(A, std::marker::PhantomData<&'a B>);

        #[verifier(external)]
        impl<'a, A, const N: u8, B> Clone for S<'a, A, N, B> { fn clone(&self) -> Self { panic!() } }
        impl<'a, A: Copy, const N: u8, B> Copy for S<'a, A, N, B> {}

        struct Q {}

        proof fn f<'a>(tracked x: S<'a, u8, 3, Q>) -> tracked (S<'a, u8, 3, Q>, S<'a, u8, 3, Q>) {
            (x, x)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lifetime_copy_fail verus_code! {
        #[verifier(external_body)]
        #[verifier(reject_recursive_types(A))]
        #[verifier(reject_recursive_types(B))]
        struct S<A, B>(A, std::marker::PhantomData<B>);

        #[verifier(external)]
        impl<A, B> Clone for S<A, B> { fn clone(&self) -> Self { panic!() } }
        impl<A: Copy, B> Copy for S<A, B> {}

        struct Q {}

        proof fn f(tracked x: S<Q, u8>) -> tracked (S<Q, u8>, S<Q, u8>) {
            (x, x)
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
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
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `a` as mutable, as it is not declared as mutable")
}

test_verify_one_file! {
    #[test] test_ghost_at_assignment_double_assignment verus_code! {
        fn foo() {
            let a: Ghost<nat>;
            proof {
                a@ = 4;
                a@ = 7;
            }
            assert(a@ == 4); // FAILS
            assert(a@ == 7);
            assert(false);
        }
    } => Err(err) => assert_rust_error_msg(err, "used binding `a` isn't initialized")
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
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] tracked_static_ref_checks_outlives verus_code! {
        pub struct X { }
        pub proof fn test<'a>(tracked x: &'a X) {
            // Make sure we disallow this (otherwise we would be able to upgrade
            // a reference &'a to &'static)
            let y = vstd::modes::tracked_static_ref(x);
        }
    } => Err(err) => assert_rust_error_msg(err, "borrowed data escapes outside of function")
}

test_verify_one_file! {
    #[test] tracked_new_issue870 verus_code! {
        use vstd::simple_pptr::*;
        fn test() {
            let (pptr, Tracked(perm)) = PPtr::<u64>::empty();
            pptr.put(Tracked(&mut perm), 5);
            let x: &u64 = pptr.borrow(Tracked(&perm)); // should tie x's lifetime to the perm borrow
            assert(x == 5);
            let _ = pptr.take(Tracked(&mut perm)); // this should invalidate the &perm borrow
            let z: u64 = *x; // but x is still available here
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `perm` as mutable because it is also borrowed as immutable")
}

test_verify_one_file! {
    #[test] tracked_new2_issue870 verus_code! {
        use vstd::simple_pptr::*;
        fn test() {
            let (pptr, Tracked(perm)) = PPtr::<u64>::empty();
            pptr.put(Tracked(&mut perm), 5);
            let x: &u64 = pptr.borrow(Tracked(&perm)); // should tie x's lifetime to the perm borrow
            assert(x == 5);
            pptr.free(Tracked(perm));
            let z: u64 = *x; // but x is still available here
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of `perm` because it is borrowed")
}

test_verify_one_file! {
    #[test] rc_with_tracked_issue870 verus_code! {
        use std::rc::Rc;
        use vstd::*;

        tracked struct X { }

        fn test<'a>() -> Rc<Tracked<&'a X>> {
            let tracked x = X { };
            let y = Rc::new(Tracked(&x));
            let z = y.clone();
            z
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot return value referencing local variable `x`")
}

test_verify_one_file! {
    #[test] arc_with_tracked_issue870 verus_code! {
        use std::sync::Arc;
        use vstd::*;

        tracked struct X { }

        fn test<'a>() -> Arc<Tracked<&'a X>> {
            let tracked x = X { };
            let y = Arc::new(Tracked(&x));
            let z = y.clone();
            z
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot return value referencing local variable `x`")
}

test_verify_one_file! {
    #[test] box_with_tracked_issue870 verus_code! {
        use vstd::*;

        tracked struct X { }

        fn test<'a>() -> Box<Tracked<&'a X>> {
            let tracked x = X { };
            let y = Box::new(Tracked(&x));
            //let z = y.clone();
            y
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot return value referencing local variable `x`")
}

test_verify_one_file! {
    #[test] index_with_extra_ref_issue1009 verus_code! {
        use vstd::prelude::*;

        fn get_internal<'a>(v: &'a Vec::<u8>, i: usize) -> (r: &'a u8)
            requires
                0 <= i < v.len()
            ensures
                r == &v[i as int]
        {
            &v[i]
        }

        fn get_internal2<'a>(v: &'a Vec::<u8>, i: usize) -> (r: &'a u8)
            requires
                0 <= i < v.len()
            ensures
                r == &v[i as int]
        {
            &(*v)[i]
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tracked_is_copy_if_type_param_is_copy verus_code! {
        use vstd::*;

        #[verifier::external_body]
        tracked struct T { }

        impl Clone for T {
            #[verifier::external_body]
            fn clone(&self) -> Self {
                T { }
            }
        }

        impl Copy for T { }

        fn test(t: Tracked<T>) {
        }

        fn test2(t: Tracked<T>) {
            test(t);
            test(t);
        }

        fn test3(t: Tracked<T>) {
            test(t.clone());
            test(t.clone());

            let x = t.clone();
            assert(x == t);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tracked_is_not_copy_just_because_type_param_is_clone verus_code! {
        #[verifier::external_body]
        tracked struct T { }

        impl Clone for T {
            #[verifier::external_body]
            fn clone(&self) -> Self {
                T { }
            }
        }

        fn test(t: Tracked<T>) {
        }

        fn test2(t: Tracked<T>) {
            test(t);
            test(t);
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `t`")
}

test_verify_one_file! {
    #[test] tracked_is_not_clone_just_because_type_param_is_clone verus_code! {
        #[verifier::external_body]
        tracked struct T { }

        impl Clone for T {
            #[verifier::external_body]
            fn clone(&self) -> Self {
                T { }
            }
        }

        fn test(t: Tracked<T>) {
        }

        fn test2(t: Tracked<T>) {
            test(t.clone());
        }
    } => Err(err) => assert_rust_error_msg(err, "the method `clone` exists for struct `verus_builtin::Tracked<T>`, but its trait bounds were not satisfied")
}

test_verify_one_file! {
    #[test] moved_value_via_at_patterns verus_code! {
        enum Opt<V> {
            Some(V),
            None
        }

        tracked struct X { }

        tracked enum Foo {
            Bar(Opt<X>),
            Zaz(Opt<X>, X),
        }

        proof fn test(tracked foo: Foo) {
            match foo {
                Foo::Bar(a @ Opt::Some(b)) => { }
                _ => { }
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "use of partially moved value")
}

test_verify_one_file! {
    #[test] implicit_deref_in_reciever_issue1243 verus_code! {
        struct X {
        }

        impl Clone for X {
            fn clone(&self) -> Self {
                X { }
            }
        }
        impl Copy for X { }

        impl X {
            fn take_self(self) {
            }

            fn take_ref(&self) {
                self.take_self();
            }
        }

        fn take_ref_x(x: &X) {
            x.take_self();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tracked_in_ghost1 verus_code! {
        struct S;
        fn test(Tracked(x): Tracked<S>) -> Tracked<S> {
            let ghost g = { let z = Tracked(x); Tracked(x) };
            Tracked(x)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tracked_in_ghost2 verus_code! {
        struct S;
        fn test(Tracked(x): Tracked<S>) -> Tracked<S> {
            let ghost g = { let tracked z = Tracked(x); Tracked(x) };
            Tracked(x)
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] tracked_in_ghost3 verus_code! {
        struct S;
        fn test(Tracked(x): Tracked<S>) -> Tracked<S> {
            let ghost g = { let y = x; let tracked z = Tracked(y); Tracked(x) };
            Tracked(x)
        }
    } => Err(err) => assert_vir_error_msg(err, "has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] tracked_borrow_unit_issue1279 verus_code! {
        proof fn f() {
            Tracked(()).borrow();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tracked_borrow_mut_assignment verus_code! {
        struct X {
            ghost_stuff: Tracked<GhostStuff>,
        }

        tracked struct Foo { }
        ghost struct Bar { }

        tracked struct GhostStuff {
            tracked t: Foo,
            ghost b: Bar,
        }

        impl Foo {
            proof fn mut_foo(tracked &mut self) { }
        }

        fn test(x: &mut X) {
            proof {
                x.ghost_stuff.borrow_mut().t = Foo { };
                x.ghost_stuff.borrow_mut().b = Bar { };

                x.ghost_stuff.borrow_mut().t.mut_foo();
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tracked_borrow_mut_assignment_fail verus_code! {
        struct X {
            ghost_stuff: Tracked<GhostStuff>,
        }

        tracked struct Foo { }
        ghost struct Bar { }

        tracked struct GhostStuff {
            tracked t: Foo,
            ghost b: Bar,
        }

        impl Foo {
            proof fn mut_foo(tracked &mut self) { }

            proof fn mut_foo_long<'a>(tracked &'a mut self) -> (tracked r: &'a Foo) {
                &*self
            }

            proof fn use_shared(tracked &self) { }
        }

        fn test_fail(x: &mut X) {
            proof {
                x.ghost_stuff.borrow_mut().t = Foo { };
                x.ghost_stuff.borrow_mut().b = Bar { };

                let tracked l = x.ghost_stuff.borrow_mut().t.mut_foo_long();
                x.ghost_stuff.borrow_mut().t.mut_foo();

                l.use_shared();
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "as mutable more than once at a time")
}

test_verify_one_file! {
    #[test] tracked_empty_union_uninitialized_1 verus_code! {
        #[verifier::external]
        enum X { }

        #[verifier::external_type_specification]
        #[verifier::external_body]
        struct ExX(X);

        fn test() {
            let tracked t: X;
            let b = false;

            proof {
                match (b, t) {
                    (true, _) => {
                        assert(false);
                    }
                }
            }

            assert(false);
        }
    } => Err(err) => assert_rust_error_msg(err, "used binding `t` isn't initialized")
}

test_verify_one_file! {
    #[test] tracked_empty_union_uninitialized_2 verus_code! {
        #[verifier::external]
        enum X { }

        #[verifier::external_type_specification]
        #[verifier::external_body]
        struct ExX(X);

        fn test2(b: bool) {
            let tracked t: X;

            proof {
                if b {
                    match t {
                    }
                    assert(false);
                } else {
                }
            }

            assert(!b);
        }
    } => Err(err) => assert_rust_error_msg(err, "used binding `t` isn't initialized")
}

test_verify_one_file! {
    #[test] tracked_empty_union_uninitialized_3 verus_code! {
        use vstd::*;

        #[verifier::external]
        enum X { }

        #[verifier::external_type_specification]
        #[verifier::external_body]
        struct ExX(X);

        fn test3() {
            let tracked t: X;
            let b = false;

            let r = || ensures false {
                proof {
                    match (b, t) {
                        (true, _) => {
                            assert(false);
                        }
                    }
                }
            };

            r();

            assert(false);
        }
    } => Err(err) => assert_rust_error_msg(err, "used binding `t` isn't initialized")
}

test_verify_one_file! {
    #[test] tracked_empty_union_uninitialized_4 verus_code! {
        use vstd::*;

        #[verifier::external]
        enum X { }

        #[verifier::external_type_specification]
        #[verifier::external_body]
        struct ExX(X);

        // This is an interesting case because we need to check t is initalized;
        // however, Rust may not consider it "captured" by the closure because
        // its value is never used.
        fn test4(b: bool) {
            let tracked t: X;

            let r = || ensures !b {
                proof {
                    if b {
                        match t {
                        }
                        assert(false);
                    } else {
                    }
                }
            };

            assert(!b);
        }
    } => Err(err) => assert_rust_error_msg(err, "used binding `t` isn't initialized")
}

test_verify_one_file! {
    #[test] spec_fn_call_fn_arg_proof_code verus_code! {
        struct R { }

        pub proof fn consume(tracked r: R) {
        }

        pub proof fn y(tracked r: R) {
            let z = ({
                consume(r);
                |y: int| y + 1
            })(5);
            consume(r);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `crate::consume` with mode proof")
}

test_verify_one_file! {
    #[test] lifetime_multiple_anonymous_names verus_code! {
        trait T<A> {
            type X;
        }
        impl T<&u8> for &u8 {
            type X = u8;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] regression_issue1083 verus_code! {
        pub trait Borrowable {
            type Borrowed<'a>;
        }

        impl Borrowable for u8 {
            type Borrowed<'a> = &'a u8;
        }

        pub struct Container<T: Borrowable>(T);
    } => Ok(())
}

test_verify_one_file! {
    #[test] two_phase verus_code! {
        use vstd::seq::*;

        struct X {
            u: u64,
        }

        impl X {
            uninterp spec fn seq(&self) -> Seq<u64>;

            #[verifier::external_body]
            fn len(&self) -> (l: u64)
                ensures l == self.seq().len()
            {
                unimplemented!();
            }

            #[verifier::external_body]
            fn push(&mut self, elem: u64)
                ensures
                    self.seq() == old(self).seq().push(elem)
            {
                unimplemented!();
            }
        }

        fn test(x: X) {
            let mut x = x;
            let ghost x1 = x.seq();
            x.push(x.len());
            assert(x.seq() == x1.push(x1.len() as u64));
        }

        fn test_fail(x: X) {
            let mut x = x;
            let ghost x1 = x.seq();
            x.push(x.len());
            assert(x.seq() == x1.push(x1.len() as u64));
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] two_phase_with_overloaded_compound_assignment_operator verus_code! {
        use vstd::seq::*;

        struct X {
            u: u64,
        }

        impl X {
            uninterp spec fn seq(&self) -> Seq<u64>;

            #[verifier::external_body]
            fn len(&self) -> (l: u64)
                ensures l == self.seq().len()
            {
                unimplemented!();
            }
        }

        impl std::ops::AddAssign<u64> for X {
            #[verifier::external_body]
            fn add_assign(&mut self, rhs: u64)
                ensures self.seq() == old(self).seq().push(rhs)
            {
                unimplemented!();
            }
        }

        fn test(x: X) {
            let mut x = x;
            let ghost x1 = x.seq();
            x += x.len();
            assert(x.seq() == x1.push(x1.len() as u64));
        }

        fn test_fail(x: X) {
            let mut x = x;
            let ghost x1 = x.seq();
            x += x.len();
            assert(x.seq() == x1.push(x1.len() as u64));
            assert(false); // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: overloaded op-assignment operator")
}

test_verify_one_file! {
    #[test] regression_issue835 verus_code! {
        pub const B: u64 = 7;

        fn test(a: usize) {
            proof {
                if a <= B {
                } else {
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] regression_issue959 verus_code! {
        pub struct S<'a> {
            pub data: &'a u8,
        }

        type Res<'a, T> = Result<(S<'a>, T), Err>;

        enum Result<A, B> {
            Ok(A),
            Err(B),
        }

        pub enum Err {
            A,
        }

        fn test<'a>(s: S<'a>) -> Res<'a, u8> {
            let cls = |s: S<'a>| -> Res<'a, u8> { ok(s) };
            Result::Ok((s, 0))
        }

        fn ok<'a>(s: S<'a>) -> Res<'a, u8> {
            Result::Ok((s, 0))
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] regression_issue959_fails verus_code! {
        pub struct S<'a> {
            pub data: &'a u8,
        }

        type Res<'a, T> = Result<(S<'a>, T), Err>;

        enum Result<A, B> {
            Ok(A),
            Err(B),
        }

        pub enum Err {
            A,
        }

        fn test<'a>(s: S<'a>) -> Res<'a, u8> {
            let cls = |s: S| -> Res<'a, u8> { ok(s) };
            Result::Ok((s, 0))
        }

        fn ok<'a>(s: S<'a>) -> Res<'a, u8> {
            Result::Ok((s, 0))
        }
    } => Err(err) => assert_rust_error_msg(err, "lifetime may not live long enough")
}

test_verify_one_file! {
    #[test] regression_issue1296 verus_code! {
        use vstd::prelude::*;

        pub trait A {
            type Iter<'a>: B<'a, E = Self::E> where Self: 'a;
            type E;

            fn things<'a>(&'a mut self) -> Result<Self::Iter<'a>, Self::E>;
        }

        pub trait B<'a> {
            type E;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] dst_fields verus_code! {
        use vstd::prelude::*;

        struct Dst {
            x: u64,
            y: [u64],
        }

        fn test(dst: &Dst) {
            let ghost r = dst.x;
        }

        fn test2(slice: &[u64]) {
            let ghost r = slice[20];
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] consts_issue1791 verus_code! {
        pub fn hello() -> [u64; 2]
        {
            S::A
        }

        pub fn hello2() -> u64
        {
            S::X
        }

        pub struct S {}

        impl S {
            pub const X: u64 = 42;

            pub const A: [u64; 2] = [1, 2];
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_specification_on_external_function verus_code! {
        struct X {
            u: u64
        }

        uninterp spec fn foo(x: X) -> bool;
        uninterp spec fn bar(x: X) -> bool;

        fn exec_foo(x: X) {
        }

        // REVIEW: reconsider if this should be allowed

        #[verifier::external]
        fn test(x: X)
            requires foo(x) && bar(x),
        {
            exec_foo(x);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] exec_struct_ghost_fields verus_code! {
        struct X {
            u: u64,
        }

        // REVIEW: consider requiring structs to be marked 'tracked' or 'ghost' to have
        // tracked/ghost fields
        // (note: the reason this test works is that, even though the struct is exec,
        // it is used in a tracked-mode way)
        struct S {
            ghost x: X,
            ghost y: X,
        }

        proof fn test(tracked x: X) {
            // this is ok, both uses of x are in ghost position
            let tracked s = S { x: x, y: x };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] exec_struct_tracked_fields verus_code! {
        struct X {
            u: u64,
        }

        struct S {
            tracked x: X,
            tracked y: X,
        }

        proof fn test(tracked x: X) {
            // this is ok, both uses of x are in ghost position
            let tracked s = S { x: x, y: x };
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] exec_struct_ghost_fields_2 verus_code! {
        struct Y {
            u: u64,
        }

        struct X {
            u: u64,
            y: Y,
        }

        struct S {
            ghost x: Y,
            ghost y: Y,
        }

        proof fn test(tracked x: &X) {
            // this is ok, both uses of x are in ghost position
            let tracked s = S { x: x.y, y: x.y };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] exec_struct_tracked_fields_2 verus_code! {
        struct Y {
            u: u64,
        }

        struct X {
            u: u64,
            y: Y,
        }

        struct S {
            tracked x: Y,
            tracked y: Y,
        }

        proof fn test(tracked x: &X) {
            // this is ok, both uses of x are in ghost position
            let tracked s = S { x: x.y, y: x.y };
        }
    } => Err(err) => assert_rust_error_msgs(err, &[
        "cannot move out of `x.y` which is behind a shared reference",
        "cannot move out of `x.y` which is behind a shared reference",
    ])
}

test_verify_one_file! {
    #[test] exec_struct_ghost_fields_fn_style verus_code! {
        struct Y {
            u: u64,
        }

        struct X {
            u: u64,
            y: Y,
        }

        struct S(ghost Y, ghost Y);

        proof fn test(tracked x: &X) {
            // this is ok, both uses of x are in ghost position
            let tracked s = S(x.y, x.y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] exec_struct_tracked_fields_fn_style verus_code! {
        struct Y {
            u: u64,
        }

        struct X {
            u: u64,
            y: Y,
        }

        struct S(tracked Y, tracked Y);

        proof fn test(tracked x: &X) {
            // this is ok, both uses of x are in ghost position
            let tracked s = S(x.y, x.y);
        }
    } => Err(err) => assert_rust_error_msgs(err, &[
        "cannot move out of `x.y` which is behind a shared reference",
        "cannot move out of `x.y` which is behind a shared reference",
    ])
}

test_verify_one_file! {
    #[test] external_body_that_uses_external_structs verus_code! {
        #[verifier::external_body]
        struct X(u64, u64);

        #[verifier::external]
        struct Y(u64, u64);

        #[verifier::external_body]
        struct X1 { a: u64, b: u64 }

        #[verifier::external]
        struct Y1 { a: u64, b: u64 }

        #[verifier::external_body]
        fn test() {
            let x = X(3, 4);
            let y = Y(5, 6);
            let x1 = X1 { a: 13, b: 14 };
            let y1 = Y1 { a: 15, b: 16 };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] generic_fn_value_issue1763 verus_code! {
        pub trait Tr {
            fn trait_func(&self) -> bool;
        }

        pub trait Sr {
            fn trait_func_s(&self) -> bool;
        }

        impl<T: Tr + ?Sized> Sr for T {
            fn trait_func_s(&self) -> (r: bool)
                ensures r == true,
            {
                true
            }
        }

        fn test<T: Tr + ?Sized>(t: &T, b: bool) {
            let the_fn = T::trait_func_s;
            assert(call_ensures(the_fn, (t,), b) ==> b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] array_as_field_and_receiver_issue1604 verus_code! {
        use vstd::prelude::*;

        struct X {
            arr: [u8; 10]
        }

        pub fn test_arr(arr: &mut [u8; 10], order: usize) -> Result<u8, ()>  {
            let val = *arr.get(order).ok_or(())?;
            Ok(val)
        }

        impl X {
            pub fn test(&mut self, order: usize) -> Result<u8, ()>  {
                let val = *self.arr.get(order).ok_or(())?;
                Ok(val)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] use_arc_as_receiver_issue1311 verus_code! {
        use std::sync::Arc;
        use vstd::prelude::*;

        pub struct Foo {
        }

        impl Foo {
            pub fn get(&self, args: &u8) -> (out: u8) { 0 }
        }

        fn main() {
            let foo = Foo { };
            let shared_foo = Arc::new(foo);
            let v = shared_foo.get(&20);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_depending_on_view_issue966 verus_code! {
        use vstd::prelude::*;

        trait VerusClone: View + Sized {
            fn verus_clone(&self) -> (r: Self)
                ensures self@ == r@;
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn vec_filter<V: VerusClone>(v: Vec<V>, f: impl Fn(&V)->bool, f_spec: spec_fn(V)->bool) -> (r: Vec<V>)
            requires forall|v: V| #[trigger] f.requires((&v,)), forall |v:V,r:bool| f.ensures((&v,), r) ==> f_spec(v) == r,
        {
            let mut r = Vec::new();
            let mut i = 0;
            while i < v.len()
                invariant
                    forall|v: V| #[trigger] f.requires((&v,)),
                    i <= v.len(),
                    forall |v:V,r:bool| f.ensures((&v,), r) ==> f_spec(v) == r,
            {
                let ghost pre_r = r@.to_multiset();
                assert(
                    v@.subrange(0, i as int + 1)
                    =~=
                    v@.subrange(0, i as int).push(v@[i as int]));
                if f(&v[i]) {
                    r.push(v[i].verus_clone());
                }

                i += 1;
            }
            r
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] derefs_issue1971 verus_code! {
        use std::sync::Arc;
        use std::rc::Rc;
        use vstd::*;

        pub struct Obj{
            a : usize,
        }
        impl Obj{
            spec fn g(&self) -> usize {
                self.a
            }
        }

        fn test(x: Arc<Obj>){
            let ghost z = x.g();
        }

        fn test2(x: Rc<Obj>){
            let ghost z = x.g();
        }

        fn test3(x: Box<Obj>){
            let ghost z = x.g();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] derefs_lifetime verus_code! {
        use std::sync::Arc;
        use std::rc::Rc;
        use vstd::*;

        pub struct Obj{
            a : usize,
        }

        fn consume<T>(t: T) { }

        fn test(x: Arc<Obj>) {
            let y: &Obj = &x;

            consume(x);

            proof {
                let tracked z = y;
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of `x` because it is borrowed")
}

test_verify_one_file! {
    #[test] derefs_lifetime2 verus_code! {
        use std::sync::Arc;
        use std::rc::Rc;
        use vstd::*;

        pub struct Obj{
            a : usize,
        }

        fn consume<T>(t: T) { }

        fn test(x: Arc<Obj>) {
            let tracked y: &Obj = &x;

            consume(x);

            proof {
                let tracked z = y;
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of `x` because it is borrowed")
}

test_verify_one_file! {
    #[test] assign_to_ghost_place_of_nonghost_local verus_code! {
        struct X {
            a: Ghost<u64>,
        }

        fn consume<T>(t: T) { }

        fn test() {
            let mut x = X { a: Ghost(3u64) };
            consume(x);

            proof {
                x.a@ = 30;
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `x`")
}

test_verify_one_file! {
    #[test] assign_to_ghost_place_of_nonghost_local2 verus_code! {
        struct X {
            a: Ghost<(u64, u64)>,
        }

        fn consume<T>(t: T) { }

        fn test() {
            let mut x = X { a: Ghost((3u64, 3u64)) };
            consume(x);

            proof {
                x.a@.0 = 30;
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `x`")
}

test_verify_one_file! {
    #[test] assign_to_ghost_place_of_nonghost_local3 verus_code! {
        tracked struct Y {
            ghost a: u64,
        }

        proof fn trk_consume<T>(tracked t: T) { }

        proof fn test2() {
            let tracked mut x = Y { a: 30 };
            trk_consume(x);

            x.a = 30;
        }
    } => Err(err) => assert_rust_error_msg(err, "assign to part of moved value: `x`")
}

test_verify_one_file! {
    #[test] assign_to_ghost_place_of_nonghost_local4_issue1298 verus_code! {
        tracked struct Z {
        }

        tracked struct Y {
            tracked z: Z,
        }

        tracked struct X {
            tracked y: Y,
            ghost a: int,
        }

        proof fn borrower<'a>(tracked x: &'a mut X) -> (tracked y: &'a Y) {
            &x.y
        }

        proof fn take_z_ref(tracked z: &Z) {
        }

        fn stuff() {
            let tracked mut x = X { y: Y { z: Z { } }, a: 0 };
            let tracked y_ref = borrower(&mut x);

            proof {
                x.a = 5;
                take_z_ref(&y_ref.z);
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot assign to `x.a` because it is borrowed")
}
