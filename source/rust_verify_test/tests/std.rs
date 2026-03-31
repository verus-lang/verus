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
    } => Err(err) => assert_vir_error_msg(err, "cannot use function `crate::X::clone` which is ignored")
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
            v[0] = a;
            let mut v2: Vec<u8> = vec![0];
            v2[0] = a;
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
    #[test] unsigned_wrapping_mul verus_code! {
        use vstd::*;

        fn test() {
            let i = 255u16.wrapping_mul(253);
            assert(i == 64515);

            let i = 256u16.wrapping_mul(256);
            assert(i == 0);

            let i = 257u16.wrapping_mul(259);
            assert(i == 1027);
        }
    } => Ok(())
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

test_verify_one_file_with_options! {
    #[test] question_mark_option ["exec_allows_no_decreases_clause"] => verus_code! {
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

test_verify_one_file_with_options! {
    #[test] question_mark_result ["exec_allows_no_decreases_clause"] => verus_code! {
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

test_verify_one_file! {
    #[test] box_clone verus_code! {
        use vstd::*;

        fn test(a: Box<u8>) {
            let b = a.clone();
            assert(a == b);
        }

        fn test2<T: Clone>(a: Box<T>) {
            let b = a.clone();
            assert(a == b); // FAILS
        }

        fn test3<T: Clone>(a: Box<T>) {
            let b = a.clone();
            assert(call_ensures(T::clone, (&*a,), *b) || a == b);
        }

        fn test3_fails<T: Clone>(a: Box<T>) {
            let b = a.clone();
            assert(call_ensures(T::clone, (&*a,), *b)); // FAILS
        }

        pub struct X { pub i: u64 }

        impl Clone for X {
            fn clone(&self) -> (res: Self)
                ensures res == (X { i: 5 }),
            {
                X { i: 5 }
            }
        }

        fn test4(a: Box<X>) {
            let b = a.clone();
            assert(a == b); // FAILS
        }

        fn test5(a: Box<X>) {
            let b = a.clone();
            assert(b == X { i: 5 } || b == a);
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] tuple_clone_not_supported verus_code! {
        use vstd::*;

        fn stuff(a: (u8, u8)) {
            let b = a.clone();
            assert(a == b); // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: built-in instance")
}

test_verify_one_file_with_options! {
    #[test] derive_copy ["--no-external-by-default"] => verus_code! {
        use vstd::*;

        // When an auto-derived impl is produced, it doesn't get the verus_macro attribute.
        // However, this test case does not use --external-by-default, so verus will
        // process the derived impls anyway.

        #[derive(Clone, Copy)]
        struct X {
            u: u64,
        }

        fn test(x: X) {
            let a = x;
            let b = x;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] derive_copy_external_by_default verus_code! {
        use vstd::*;

        // When an auto-derived impl is produced, it doesn't get the verus_macro attribute.
        // Since this test case uses --external-by-default, these derived impls do not
        // get processed.

        #[derive(Clone, Copy)]
        struct X {
            u: u64,
        }

        fn test(x: X) {
            let a = x;
            let b = x;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] external_derive_attr ["--no-external-by-default"] => verus_code! {
        #[derive(Clone, Copy)]
        #[verifier::external_derive]
        struct X {
            u: u64,
        }

        fn test(x: X) {
            let a = x.clone();
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use function `crate::X::clone` which is ignored")
}

test_verify_one_file_with_options! {
    #[test] external_derive_attr_list ["--no-external-by-default"] => verus_code! {
        #[derive(Clone, Copy)]
        #[verifier::external_derive(Clone)]
        struct X {
            u: u64,
        }

        fn test(x: X) {
            let a = x.clone();
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use function `crate::X::clone` which is ignored")
}

test_verify_one_file! {
    #[test] vec_index_nounwind verus_code! {
        use vstd::*;

        fn test(v: Vec<u64>)
            requires v.len() > 5,
            no_unwind
        {
            let x = v[0];
            let mut v = v;
            v[1] = 4;
            let l = v.len();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] vec_from_elem verus_code! {
        use vstd::prelude::*;

        #[derive(Debug)]
        pub struct X {
            pub u: u64
        }

        impl Clone for X {
            fn clone(&self) -> (s: Self)
                ensures s.u == (if self.u < 1000 { self.u + 1 } else { 1000 })
            {
                X { u: if self.u < 1000 { self.u + 1 } else { 1000 } }
            }
        }

        fn test1() {
            let x = X { u: 0 };
            let v = vec![x; 4];
            assert(v.len() == 4);
            assert(v@[0].u == 0 || v@[0].u == 1);
            assert(v@[1].u == 0 || v@[1].u == 1);
            assert(v@[2].u == 0 || v@[2].u == 1);
            assert(v@[3].u == 0 || v@[3].u == 1);
        }

        fn test2() {
            let x = X { u: 0 };
            let v = vec![x; 4];
            assert(v.len() == 4);
            assert(v@[0].u == 0); // FAILS
        }

        fn test3() {
            let x = X { u: 0 };
            let v = vec![x; 4];
            assert(v.len() == 4);
            assert(v@[0].u == 1); // FAILS
        }

        fn test4() {
            let v = vec![12; 4];
            assert(v.len() == 4);
            assert(v@[0] == 12);
            assert(v@[1] == 12);
            assert(v@[2] == 12);
            assert(v@[3] == 12);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] manually_drop verus_code! {
        use vstd::prelude::*;
        use std::mem::ManuallyDrop;

        fn test() {
            let x = ManuallyDrop::new(20u64);
            assert(x@ == 20);

            let z: &u64 = &x;
            assert(z == 20);

            let x1 = x.clone();
            assert(x1@ == 20);

            let y = ManuallyDrop::into_inner(x);
            assert(y == 20);
        }

        #[derive(Debug)]
        pub struct X {
            pub u: u64
        }

        impl Clone for X {
            fn clone(&self) -> (s: Self)
                ensures s.u == (if self.u < 1000 { self.u + 1 } else { 1000 })
            {
                X { u: if self.u < 1000 { self.u + 1 } else { 1000 } }
            }
        }

        fn test_clone() {
            let x = ManuallyDrop::new(X { u: 20u64 });
            let y = x.clone();
            assert(y@.u == 20 || y@.u == 21);
        }

        fn test_clone2() {
            let x = ManuallyDrop::new(X { u: 20u64 });
            let y = x.clone();
            assert(y@.u == 20); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}
