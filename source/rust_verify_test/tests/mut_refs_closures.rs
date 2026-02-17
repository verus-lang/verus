#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] closure_resolve_basic_move ["new-mut-ref"] => verus_code! {
        fn consume<T>(t: T) { }

        fn test<T>(t: T) {
            let a = t;
            let x = || {
                let y = a;
            };
            consume(x);

            assert(has_resolved(a)); // FAILS
        }

        fn test2<T>(t: T) {
            let a = t;
            let x = || {
                let y = a;
                assert(has_resolved(y));
            };
            consume(x);
        }

        fn test3<T>(t: T) {
            let a = t;
            assert(has_resolved(a));

            // Here `a` is taken by reference
            let x = || {
                let y = &a;
            };
            consume(x);
        }

        fn test4<T>(t: T) {
            let a = t;
            assert(has_resolved(a));

            // Technically `a` is moved here, but we can resolve it anyway
            // (since it's only used read-only)
            let x = move || {
                let y = &a;
            };
            consume(x);
        }

        fn test5<T>(t: T) {
            let a = t;
            let x = || {
                let y = a;
                consume(y);
                assert(has_resolved(a)); // FAILS
            };
            consume(x);
        }

        fn test6<T>(t: T, u: T) {
            let a = t;
            let b = u;
            let x = || {
                assert(has_resolved(b)); // FAILS
            };
            consume(x);
            consume(b);
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] closure_resolve_basic_move2 ["new-mut-ref"] => verus_code! {
        fn consume<T>(t: T) { }

        fn test<T>(a: T) {
            let x = || {
                let y = a;
            };
            consume(x);

            assert(has_resolved(a)); // FAILS
        }

        fn test2<T>(a: T) {
            let x = || {
                let y = a;
                assert(has_resolved(y));
            };
            consume(x);
        }

        fn test3<T>(a: T) {
            assert(has_resolved(a));

            // Here `a` is taken by reference
            let x = || {
                let y = &a;
            };
            consume(x);
        }

        fn test4<T>(a: T) {
            assert(has_resolved(a));

            // Technically `a` is moved here, but we can resolve it anyway
            // (since it's only used read-only)
            let x = move || {
                let y = &a;
            };
            consume(x);
        }

        fn test5<T>(a: T) {
            let x = || {
                let y = a;
                consume(y);
                assert(has_resolved(a)); // FAILS
            };
            consume(x);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] closure_resolve_basic_move_of_closure_param ["new-mut-ref"] => verus_code! {
        fn consume<T>(t: T) { }

        fn test<T>() {
            let foo = |a: T| {
                let x = || {
                    let y = a;
                };
                consume(x);

                assert(has_resolved(a)); // FAILS
            };
        }

        fn test2<T>() {
            let foo = |a: T| {
                let x = || {
                    let y = a;
                    assert(has_resolved(y));
                };
                consume(x);
            };
        }

        fn test3<T>() {
            let foo = |a: T| {
                assert(has_resolved(a));

                // Here `a` is taken by reference
                let x = || {
                    let y = &a;
                };
                consume(x);
            };
        }

        fn test4<T>() {
            let foo = |a: T| {
                assert(has_resolved(a));

                // Technically `a` is moved here, but we can resolve it anyway
                // (since it's only used read-only)
                let x = move || {
                    let y = &a;
                };
                consume(x);
            };
        }

        fn test5<T>() {
            let foo = |a: T| {
                let x = || {
                    let y = a;
                    consume(y);
                    assert(has_resolved(a)); // FAILS
                };
                consume(x);
            };
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] proof_closure_resolve_basic_move ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        proof fn consume<T>(tracked t: T) { }

        proof fn test<T>(tracked t: T) {
            let tracked a = t;
            let tracked x = proof_fn[Once] || {
                let tracked y = a;
            };
            consume(x);

            assert(has_resolved(a)); // FAILS
        }

        proof fn test2<T>(tracked t: T) {
            let tracked a = t;
            let tracked x = proof_fn[Once] || {
                let tracked y = a;
                assert(has_resolved(y));
            };
            consume(x);
        }

        proof fn test3<T>(tracked t: T) {
            let tracked a = t;
            assert(has_resolved(a));

            // Here `a` is taken by reference
            let tracked x = proof_fn || {
                let tracked y = &a;
            };
            consume(x);
        }

        proof fn test4<T>(tracked t: T) {
            let tracked a = t;
            assert(has_resolved(a));

            // Technically `a` is moved here, but we can resolve it anyway
            // (since it's only used read-only)
            let tracked x = move proof_fn || {
                let tracked y = &a;
            };
            consume(x);
        }

        proof fn test5<T>(tracked t: T) {
            let tracked a = t;
            let tracked x = proof_fn[Once] || {
                let tracked y = a;
                consume(y);
                assert(has_resolved(a)); // FAILS
            };
            consume(x);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] closure_resolve_nested_move ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn consume<T>(t: T) { }

        fn test<T>(t: T) {
            let a = t;
            let x = || {
                let j = || {
                    let y = a;
                };
                j();
            };
            consume(x);

            assert(has_resolved(a)); // FAILS
        }

        fn test2<T>(t: T) {
            let a = t;
            let x = || {
                let j = || {
                    let y = a;
                    assert(has_resolved(y));
                };
                j();
            };
            consume(x);
        }

        fn test3<T>(t: T) {
            let a = t;
            assert(has_resolved(a));
            let x = || {
                let j = || {
                    let y = &a;
                };
                j();
            };
            consume(x);
        }

        fn test4<T>(t: T) {
            let a = t;
            assert(has_resolved(a));
            let x = move || {
                let j = || {
                    let y = &a;
                };
                j();
            };
            consume(x);
        }

        fn test5<T>(t: T) {
            let a = t;
            let x = || {
                let j = || {
                    let y = a;
                };
                consume(j);
                assert(has_resolved(a)); // FAILS
            };
            consume(x);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] closure_resolve_field_move ["new-mut-ref"] => verus_code! {
        fn consume<T>(t: T) { }

        fn test<T, U>(t: (T, U)) {
            let pair = t;
            let x = || {
                let y = pair.0;
                assert(has_resolved(y));
            };
            consume(x);

            assert(has_resolved(pair.1));
        }

        fn test2<T, U>(t: (T, U)) {
            let pair = t;
            let x = || {
                let y = pair.0;
            };
            consume(x);

            assert(has_resolved(pair.0)); // FAILS
        }

        fn test3<T, U>(t: (T, U)) {
            let pair = t;
            assert(has_resolved(pair));

            // Here `a` is taken by reference
            let x = || {
                let y = &pair.0;
            };
            consume(x);
        }

        fn test4<T, U>(t: (T, U)) {
            let pair = t;
            assert(has_resolved(pair));

            let x = move || {
                let y = &pair.0;
            };
            consume(x);
        }

        fn test5<T, U>(t: (T, U)) {
            let pair = t;
            let x = || {
                let y = pair.0;
                assert(has_resolved(pair.1)); // FAILS
            };
            consume(x);
            consume(pair.1);
        }

    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] closure_resolve_overlapping_moves ["new-mut-ref"] => verus_code! {
        fn some_bool() -> bool {
            true
        }

        fn consume<T>(t: T) { }

        fn test<T, U, V, W>(t: (T, U), v: (V, W)) {
            let pair = t;
            let qair = v;

            let x = || {
                if some_bool() {
                    consume(pair);
                    consume(qair);

                } else {
                    consume(pair.0);

                    assert(has_resolved(pair.1));
                    assert(has_resolved(qair));
                }
            };
            consume(x);
        }

        fn test1<T, U, V, W>(t: (T, U), v: (V, W)) {
            let pair = t;
            let qair = v;

            let x = || {
                if some_bool() {
                    consume(pair);
                    consume(qair);

                } else {
                    consume(pair.0);
                }
            };
            consume(x);

            assert(has_resolved(pair.1)); // FAILS
        }

        fn test2<T, U, V, W>(t: (T, U), v: (V, W)) {
            let pair = t;
            let qair = v;

            let x = || {
                if some_bool() {
                    consume(pair);
                    consume(qair);

                } else {
                    consume(pair.0);
                }
            };
            consume(x);

            assert(has_resolved(pair.0)); // FAILS
        }

        fn test3<T, U, V, W>(t: (T, U), v: (V, W)) {
            let pair = t;
            let qair = v;

            let x = || {
                if some_bool() {
                    consume(pair);
                    consume(qair);

                } else {
                    consume(pair.0);
                }
            };
            consume(x);

            assert(has_resolved(pair.1)); // FAILS
        }

        fn test4<T, U, V, W>(t: (T, U), v: (V, W)) {
            let pair = t;
            let qair = v;

            let x = || {
                if some_bool() {
                    consume(pair);
                    consume(qair);

                    assert(has_resolved(pair)); // FAILS
                } else {
                    consume(pair.0);

                }
            };
            consume(x);
        }

        fn test5<T, U, V, W>(t: (T, U), v: (V, W)) {
            let pair = t;
            let qair = v;

            let x = || {
                if some_bool() {
                    consume(pair);
                    consume(qair);

                    assert(has_resolved(pair.1)); // FAILS
                } else {
                    consume(pair.0);

                }
            };
            consume(x);
        }

        fn test6<T, U, V, W>(t: (T, U), v: (V, W)) {
            let pair = t;
            let qair = v;

            let x = || {
                if some_bool() {
                    consume(pair);
                    consume(qair);

                    assert(has_resolved(pair.0)); // FAILS
                } else {
                    consume(pair.0);

                }
            };
            consume(x);
        }

        fn test7<T, U, V, W>(t: (T, U), v: (V, W)) {
            let pair = t;
            let qair = v;

            let x = || {
                if some_bool() {
                    consume(pair);
                    consume(qair);

                    assert(has_resolved(pair)); // FAILS
                } else {
                    consume(pair.0);

                }
            };
            consume(x);
        }
    } => Err(err) => assert_fails(err, 7)
}

test_verify_one_file_with_options! {
    #[test] closure_resolve_params ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn consume<T>(t: T) { }
        proof fn trk_consume<T>(tracked t: T) { }

        fn test1<T>() {
            let x = |y: T| {
                assert(has_resolved(y));
            };
        }

        fn test2<T>() {
            let x = |y: T| {
                consume(y);
                assert(has_resolved(y)); // FAILS
            };
        }

        proof fn test_trk_gho<T, G>() {
            let tracked x = proof_fn |tracked y: T, z: G| {
                assert(has_resolved(y));
            };
        }

        proof fn test_trk_gho2<T, G>() {
            let tracked x = proof_fn |tracked y: T, z: G| {
                assert(has_resolved(z)); // FAILS
            };
        }

        proof fn test_trk_gho3<T, G>() {
            let tracked x = proof_fn |tracked y: T, z: G| {
                trk_consume(y);
                assert(has_resolved(y)); // FAILS
            };
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] mut_refs_in_closure ["new-mut-ref"] => verus_code! {
        fn test1() {
            let foo = || {
                let mut x: u64 = 0;
                let mut y: u64 = 10;

                let mut x_ref = &mut x;
                *x_ref = 20;

                assert(x == 20);

                x_ref = &mut y;
                *x_ref = 30;

                assert(y == 30);
            };
        }

        fn test1_fails() {
            let foo = || {
                let mut x: u64 = 0;
                let mut y: u64 = 10;

                let mut x_ref = &mut x;
                *x_ref = 20;

                assert(x == 20);

                x_ref = &mut y;
                *x_ref = 30;

                assert(y == 30);
                assert(false); // FAILS
            };
        }

        fn test1_fails2() {
            let foo = || {
                let mut x: u64 = 0;
                let mut y: u64 = 10;

                let mut x_ref = &mut x;
                *x_ref = 20;

                assert(x == 20);

                x_ref = &mut y;
                *x_ref = 30;

                assert(y == 30);
            };
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}
