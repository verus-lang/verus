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
            let sl: &[u32] = &[0u32, 2u32, 4u32];

            let mut i: usize = 0;
            for x in it: sl.iter()
                invariant
                    i == it.index(),
                    it.seq().unref() == seq![0u32, 2u32, 4u32],
            {
                assert(it.seq().unref().contains(*x));
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

test_verify_one_file! {
    #[test] test_slice_index verus_code! {
        use std::ops::Index;
        use vstd::prelude::*;

        fn element(s: &[u8]) {
            assume(s.len() == 5);
            let x = s[2];
            assert(x == s[2]);
            assert(x == s[3]); // FAILS
        }

        fn element_bounds(s: &[u8]) {
            assume(s.len() == 5);
            let x = s[7]; // FAILS
        }

        fn element_index(s: &[u8]) {
            assume(s.len() == 5);
            let x = *s.index(2);
            assert(x == s[2]);
            assert(x == s[3]); // FAILS
        }

        fn element_index_bounds(s: &[u8]) {
            assume(s.len() == 5);
            let x = *s.index(7); // FAILS
        }

        fn range(s: &[u8]) {
            assume(s.len() == 5);
            let x = &s[1..3];
            assert(x@ == s@.subrange(1, 3));
            assert(x@ == s@.subrange(2, 4)); // FAILS
        }

        fn range_bounds(s: &[u8]) {
            assume(s.len() == 5);
            let x = &s[3..7]; // FAILS
        }

        fn range_index(s: &[u8]) {
            assume(s.len() == 5);
            let x = s.index(1..3);
            assert(x@ == s@.subrange(1, 3));
            assert(x@ == s@.subrange(2, 4)); // FAILS
        }

        fn range_index_bounds(s: &[u8]) {
            assume(s.len() == 5);
            let x = s.index(3..7); // FAILS
        }
    } => Err(err) => assert_fails(err, 8)
}

test_verify_one_file! {
    #[test] test_array_index verus_code! {
        use std::ops::Index;
        use vstd::prelude::*;

        fn element(a: &[u8; 5]) {
            let x = a[2];
            assert(x == a[2]);
            assert(x == a[3]); // FAILS
        }

        fn element_bounds(a: &[u8; 5]) {
            let x = a[7]; // FAILS
        }

        fn element_index(a: &[u8; 5]) {
            let x = *a.index(2);
            assert(x == a[2]);
            assert(x == a[3]); // FAILS
        }

        fn element_index_bounds(a: &[u8; 5]) {
            let x = *a.index(7); // FAILS
        }

        fn range(a: &[u8; 5]) {
            let x = &a[1..3];
            assert(x@ == a@.subrange(1, 3));
            assert(x@ == a@.subrange(2, 4)); // FAILS
        }

        fn range_bounds(a: &[u8; 5]) {
            let x = &a[3..7]; // FAILS
        }

        fn range_index(a: &[u8; 5]) {
            let x = a.index(1..3);
            assert(x@ == a@.subrange(1, 3));
            assert(x@ == a@.subrange(2, 4)); // FAILS
        }

        fn range_index_bounds(a: &[u8; 5]) {
            let x = a.index(3..7); // FAILS
        }
    } => Err(err) => assert_fails(err, 8)
}

test_verify_one_file! {
    #[test] test_vec_index verus_code! {
        use std::ops::Index;
        use vstd::prelude::*;

        fn element(v: &Vec<u8>) {
            assume(v.len() == 5);
            let x = v[2];
            assert(x == v[2]);
            assert(x == v[3]); // FAILS
        }

        fn element_bounds(v: &Vec<u8>) {
            assume(v.len() == 5);
            let x = v[7]; // FAILS
        }

        fn element_index(v: &Vec<u8>) {
            assume(v.len() == 5);
            let x = *v.index(2);
            assert(x == v[2]);
            assert(x == v[3]); // FAILS
        }

        fn element_index_bounds(v: &Vec<u8>) {
            assume(v.len() == 5);
            let x = *v.index(7); // FAILS
        }

        fn range(v: &Vec<u8>) {
            assume(v.len() == 5);
            let x = &v[1..3];
            assert(x@ == v@.subrange(1, 3));
            assert(x@ == v@.subrange(2, 4)); // FAILS
        }

        fn range_bounds(v: &Vec<u8>) {
            assume(v.len() == 5);
            let x = &v[3..7]; // FAILS
        }

        fn range_index(v: &Vec<u8>) {
            assume(v.len() == 5);
            let x = v.index(1..3);
            assert(x@ == v@.subrange(1, 3));
            assert(x@ == v@.subrange(2, 4)); // FAILS
        }

        fn range_index_bounds(v: &Vec<u8>) {
            assume(v.len() == 5);
            let x = v.index(3..7); // FAILS
        }
    } => Err(err) => assert_fails(err, 8)
}

test_verify_one_file! {
    #[test] test_other_index verus_code! {
        use std::ops::Index;
        use vstd::prelude::*;

        fn range(v: Vec<u8>) {
            assume(v.len() == 5);
            let x = &v[1..3];
            assert(x@ == v@.subrange(1, 3));
            assert(x@ == v@.subrange(2, 4)); // FAILS
        }

        fn range_arc(v: std::sync::Arc<Vec<u8>>) {
            assume(v.len() == 5);
            let x = &v[1..3];
            assert(x@ == v@.subrange(1, 3));
            assert(x@ == v@.subrange(2, 4)); // FAILS
        }

        fn range_deref<A: std::ops::Deref<Target = Vec<u8>>>(v: &A) {
            let x = &v[1..3]; // FAILS
        }

        fn element_index<I: Index<usize, Output = u8>>(v: &I) {
            let x = &v[1]; // FAILS
        }

        fn range_index<I: Index<std::ops::Range<usize>, Output = u8>>(v: &I) {
            let x = &v[1..3]; // FAILS
        }
    } => Err(err) => assert_fails(err, 5)
}
