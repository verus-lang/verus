#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] rc_arc verus_code! {
        use std::rc::Rc;
        use std::sync::Arc;
        use vstd::*;

        fn foo() {
            let x = Rc::new(5);
            assert(*x == 5) by {}

            let x1 = x.clone();
            assert(*x1 == 5) by {}

            let y = Arc::new(5);
            assert(*y == 5) by {}

            let y1 = y.clone();
            assert(*y1 == 5) by {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ref_clone verus_code! {
        struct X { }

        fn test2(x: &X) { }

        fn test(x: &X) {
            // Since X is not clone, Rust resolves this to a clone of the reference type &X
            // So this is basically the same as `let y = x;`
            let y = x.clone();
            assert(x == y);
            test2(y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] external_clone_fail verus_code! {
        // Make sure the support for &X clone doesn't mistakenly trigger in other situations

        struct X { }

        #[verifier(external)]
        impl Clone for X {
            fn clone(&self) -> Self {
                X { }
            }
        }

        fn foo(x: &X) {
            let y = x.clone();
        }
    } => Err(err) => assert_vir_error_msg(err, "`crate::X::clone` is not supported")
}

test_verify_one_file! {
    #[test] box_new verus_code! {
        use vstd::*;

        fn foo() {
            let x: Box<u32> = Box::new(5);
            assert(*x == 5);
        }
    } => Ok(())
}

// Indexing into vec

test_verify_one_file! {
    #[test] index_vec_out_of_bounds verus_code! {
        use vstd::*;

        fn stuff<T>(v: Vec<T>) {
            let x = &v[0]; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] index_vec_out_of_bounds2 verus_code! {
        use vstd::*;

        fn stuff<T>(v: &Vec<T>) {
            let x = &v[0]; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] index_vec_out_of_bounds3 verus_code! {
        use vstd::*;

        fn stuff<T>(v: &Vec<T>) {
            let x = v[0]; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] index_vec_in_bounds verus_code! {
        use vstd::*;

        fn stuff(v: &Vec<u8>)
            requires v.len() > 0,
        {
            let a = v[0] < v[0];
            assert(a == false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] index_vec_in_bounds2 verus_code! {
        use vstd::prelude::*;

        fn stuff(v: &mut Vec<u8>)
            requires old(v).len() > 0,
        {
            let a = v[0];
            assert(a == v.view().index(0));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] index_vec_in_bounds3 verus_code! {
        use vstd::prelude::*;

        fn stuff(v: &mut Vec<u8>)
            requires old(v).len() > 0,
        {
            let a = &v[0];
            assert(*a == v.view().index(0));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] index_vec_move_error verus_code! {
        use vstd::*;

        fn stuff<T>(v: Vec<T>) {
            let x = v[0];
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of index of `std::vec::Vec<T>`")
}

test_verify_one_file! {
    #[test] index_vec_move_error2 verus_code! {
        use vstd::*;

        fn stuff<T>(v: &mut Vec<T>) {
            let x = v[0];
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of index of `std::vec::Vec<T>`")
}

test_verify_one_file! {
    #[test] index_vec_mut_error verus_code! {
        use vstd::*;

        fn foo(t: &mut u8) { }

        fn stuff(v: Vec<u8>) {
            foo(&mut v[0]);
        }
    } => Err(err) => assert_vir_error_msg(err, "index for &mut not supported")
}

test_verify_one_file! {
    #[test] signed_wrapping_mul verus_code! {
        use vstd::*;

        fn test() {
            let i = (1000 as i64).wrapping_mul(2000);
            assert(i == 2000000);

            let i = (1000 as i64).wrapping_mul(-2000);
            assert(i == -2000000);

            let i = (12345678901 as i64).wrapping_mul(45678912301);
            assert(i == -7911882469911038895);

            let i = (92345678901 as i64).wrapping_mul(175678912301);
            assert(i == 8500384234389190737);

            let i = (12 as i64).wrapping_mul(2305843009213693952);
            assert(i == -9223372036854775808);

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] question_mark_option verus_code! {
        use vstd::*;

        fn test() -> (res: Option<u32>)
            ensures res.is_none()
        {
            let x: Option<u8> = None;
            let y = x?;

            assert(false);
            return None;
        }

        fn test2() -> (res: Option<u32>)
        {
            let x: Option<u8> = Some(5);
            let y = x?;

            assert(false); // FAILS
            return None;
        }

        fn test3() -> (res: Option<u32>)
            ensures res.is_some(),
        {
            let x: Option<u8> = None;
            let y = x?; // FAILS

            return Some(13);
        }

        fn test4() -> (res: Option<u32>)
            ensures false,
        {
            let x: Option<u8> = Some(12);
            let y = x?;

            assert(y == 12);

            loop { }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] question_mark_result verus_code! {
        use vstd::*;

        fn test() -> (res: Result<u32, bool>)
            ensures res === Err(false),
        {
            let x: Result<u8, bool> = Err(false);
            let y = x?;

            assert(false);
            return Err(true);
        }

        fn test2() -> (res: Result<u32, bool>)
        {
            let x: Result<u8, bool> = Ok(5);
            let y = x?;

            assert(false); // FAILS
            return Err(false);
        }

        fn test3() -> (res: Result<u32, bool>)
            ensures res.is_ok(),
        {
            let x: Result<u8, bool> = Err(false);
            let y = x?; // FAILS

            return Ok(13);
        }

        fn test4() -> (res: Result<u32, bool>)
            ensures false,
        {
            let x: Result<u8, bool> = Ok(12);
            let y = x?;

            assert(y == 12);

            loop { }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] clone_for_std_types verus_code! {
        use vstd::*;
        use vstd::prelude::*;

        fn test_bool(v: bool) {
            let w = v.clone();
            assert(w == v);
        }

        fn test_bool_vec(v: Vec<bool>) {
            let w = v.clone();
            assert(w@ =~= v@);
        }

        fn test_char(v: char) {
            let w = v.clone();
            assert(w == v);
        }

        fn test_char_vec(v: Vec<char>) {
            let w = v.clone();
            assert(w@ =~= v@);
        }

        struct Y { }

        fn test_vec_ref(v: Vec<&Y>) {
            let w = v.clone();
            assert(w@ =~= v@);
        }

        struct X { i: u64 }

        impl Clone for X {
            fn clone(&self) -> Self { X { i: 0 } }
        }

        fn test_vec_fail(v: Vec<X>)
            requires v.len() >= 1,
        {
            let w = v.clone();
            assert(v[0] == w[0]); // FAILS
        }

        fn test_vec_deep_view() {
            let mut v1: Vec<u8> = Vec::new();
            v1.push(3);
            v1.push(4);
            let c1 = v1.clone();
            let ghost g1 = c1@ == v1@;
            assert(g1);
            let mut v2: Vec<Vec<u8>> = Vec::new();
            v2.push(v1.clone());
            v2.push(v1.clone());
            let c2 = v2.clone();
            let ghost g2 = c2.deep_view() == v2.deep_view();
            assert(g2);
            assert(c2@ == v2@); // FAILS
        }

        fn test_vec_deep_view_char() {
            let mut v1: Vec<char> = Vec::new();
            v1.push('a');
            v1.push('b');
            let c1 = v1.clone();
            let ghost g1 = c1@ == v1@;
            assert(g1);
            let mut v2: Vec<Vec<char>> = Vec::new();
            v2.push(v1.clone());
            v2.push(v1.clone());
            let c2 = v2.clone();
            let ghost g2 = c2.deep_view() == v2.deep_view();
            assert(g2);
            assert(c2@ == v2@); // FAILS
        }

        fn test_slice_deep_view(a1: &[Vec<u8>], a2: &[Vec<u8>])
            requires
                a1.len() == 1,
                a2.len() == 1,
                a1[0].len() == 1,
                a2[0].len() == 1,
                a1[0][0] == 10,
                a2[0][0] == 10,
            ensures
                a1.deep_view() == a2.deep_view(),
        {
            assert(a1.deep_view() =~~= a2.deep_view()); // TODO: get rid of this?
        }

        fn test_array_deep_view(a1: &[Vec<u8>; 1], a2: &[Vec<u8>; 1])
            requires
                a1[0].len() == 1,
                a2[0].len() == 1,
                a1[0][0] == 10,
                a2[0][0] == 10,
            ensures
                a1.deep_view() == a2.deep_view(),
        {
            assert(a1.deep_view() =~~= a2.deep_view()); // TODO: get rid of this?
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] vec_macro verus_code! {
        use vstd::*;
        use vstd::prelude::*;

        fn test() {
            let v = vec![7, 8, 9];
            assert(v.len() == 3);
            assert(v[0] == 7);
            assert(v[1] == 8);
            assert(v[2] == 9);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] box_globals_no_trait_conflict verus_code! {
        use vstd::*;
        use core::alloc::Allocator;

        trait Tr {
            spec fn some_int() -> int;
        }

        spec fn some_int0<A: Allocator>() -> int;

        spec fn some_int<A: Allocator>(b: Box<u8, A>) -> int {
            some_int0::<A>()
        }

        proof fn test<A: Allocator>(b: Box<u8, A>, c: Box<u8>)
            requires b == c
        {
            assert(some_int(b) == some_int(c)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] phantom_data_is_unit verus_code! {
        use core::marker::PhantomData;
        use vstd::prelude::*;

        proof fn stuff(a: PhantomData<u64>, b: PhantomData<u64>) {
            assert(a == b);
            assert(a == PhantomData::<u64>);
        }

        fn stuff2(a: PhantomData<u64>, b: PhantomData<u64>) {
            assert(a == b);
            let z = PhantomData::<u64>;
            assert(a == z);
        }
    } => Ok(())
}
