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

        fn test_set(x: &mut [u64])
            requires old(x).len() == 3
        {
            x.set(0, 5);
            x.set(1, 20);
            assert(x[0] == 5);
            assert(x[1] == 20);
            assert(false); // FAILS
        }

        fn test_set3(x: &mut [u64])
        {
            x.set(0, 5); // FAILS
        }

        fn test_is_empty<T>(x: &[T], y: &[T])
            requires
                x@.len() == 0,
                y@.len() > 0,
        {
            assert(x.is_empty());
            assert(!y.is_empty());
            let xb = x.is_empty();
            let yb = y.is_empty();
            assert(xb);
            assert(!yb);
        }

    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file! {
    #[test] test_recursion_checks verus_code! {
        use vstd::map::*;

        struct Foo {
            field: Box<[ Map<Foo, int> ]>,
        }

    } => Err(err) => assert_vir_error_msg(err, "non-positive position")
}

test_verify_one_file! {
    #[test] test_slice_iter verus_code! {
        use vstd::std_specs::slice::*;
        use vstd::seq;

        fn test() {
            let sl = &[0u32, 2u32, 4u32];

            let mut i: usize = 0;
            let iter = sl.iter();
            for x in it: iter
                invariant
                    i == it.pos,
                    it.elements == seq![0u32, 2u32, 4u32],
            {
                assert(x < 5);
                assert(x % 2 == 0);
                i = i + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_slices_arrays_extensionality verus_code! {
        use vstd::prelude::*;

        fn test_slice() {
            let sl1: &[u64] = &[0, 2, 4];
            let sl2: &[u64] = &[0, 2, 4];

            assert(sl1 == sl2);
        }

        fn test_array() {
            let ar1: [u64; 3] = [0, 2, 4];
            let ar2: [u64; 3] = [0, 2, 4];

            assert(ar1 == ar2);
        }

        fn test_array_views(a: &[u64; 3], b: &[u64; 3])
            requires a@ == b@,
        {
            assert(a == b);
        }

        fn test_slice_views(a: &[u64], b: &[u64])
            requires a@ == b@,
        {
            assert(a == b);
        }
    } => Ok(())
}
