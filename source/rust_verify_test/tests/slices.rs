#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        use vstd::{slice::*, prelude::*};

        fn foo(x: &[u64])
            requires x@.len() == 2, x[0] == 19,
        {
            let t = *slice_index_get(x, 0);
            assert(t == 19);
        }

        fn foo_index(x: &[u64])
            requires x@.len() == 2, x[0] == 19,
        {
            let t = x[0];
            assert(t == 19);
        }

        fn foo2(x: Vec<u64>)
            requires x@.len() == 2, x[0] == 19,
        {
            foo(x.as_slice());
        }

        fn foo3(x: &[u64])
        {
            let t = *slice_index_get(x, 0); // FAILS
        }

        fn foo3_index(x: &[u64])
        {
            let t = x[0]; // FAILS
        }

        // Generics

        fn foo_generic<T>(x: &[T])
            requires x@.len() === 2, x[0] === x[1],
        {
            let t = slice_index_get(x, 0);
            assert(*t === x[1]);
        }

        fn foo_generic_index<T>(x: &[T])
            requires x@.len() === 2, x[0] === x[1],
        {
            let t = &x[0];
            assert(*t === x[1]);
        }

        fn foo_generic2<T>(x: Vec<T>)
            requires x@.len() === 2, x[0] === x[1],
        {
            foo_generic(x.as_slice());
        }

        fn foo_generic3<T>(x: &[T])
        {
            let t = slice_index_get(x, 0); // FAILS
        }

        fn foo_generic3_index<T>(x: &[T])
        {
            let t = &x[0]; // FAILS
        }

        fn foo_generic4(x: &[u64])
            requires x@.len() == 2, x[0] == 19, x[1] == 19,
        {
            foo_generic(x);
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] test_recursion_checks verus_code! {
        use vstd::map::*;

        struct Foo {
            field: Box<[ Map<Foo, int> ]>,
        }

    } => Err(err) => assert_vir_error_msg(err, "non-positive position")
}
