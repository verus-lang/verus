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
    } => Err(err) => assert_vir_error_msg(err, "cannot use function `test_crate::X::clone` which is ignored")
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

test_verify_one_file! {
    #[test] wrapping_shift verus_code! {
        use vstd::wrapping::{u32_specs, i32_specs, u16_specs, i8_specs};
        proof fn test() by (bit_vector)
            ensures
                u16_specs::wrapping_shr(u16::MAX, 1) == 0x7fffu16,
                u16_specs::wrapping_shr(42u16, 16) == 42u16,
                u16_specs::wrapping_shr(u16_specs::wrapping_shr(42u16, 1), 15) == 0u16,
                u16_specs::wrapping_shr(10u16, 1025) == 5u16,
                i32_specs::wrapping_shr(-1i32, 5) == -1i32,
                i32_specs::wrapping_shl(1i32, 31) == i32::MIN,
                i8_specs::wrapping_shl(i8::MIN, 1) == 0i8,
                i8_specs::wrapping_shl(-1i8, 7) == i8::MIN,
                forall|x: u32, k: u32| #[trigger] u32_specs::wrapping_shl(x, k) == u32_specs::wrapping_shl(x, k % 32),
                forall|x: u32| #[trigger] u32_specs::wrapping_shl(x, 0) == x,
                forall|k: u32| #[trigger] i32_specs::wrapping_shr(-1i32, k) == -1i32,
        {}
    } => Ok(())
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
            ensures res == Err(false),
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
            requires *b == *c
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
            assert(*b == X { i: 5 } || b == a);
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
    } => Err(err) => assert_vir_error_msg(err, "cannot use function `test_crate::X::clone` which is ignored")
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
    } => Err(err) => assert_vir_error_msg(err, "cannot use function `test_crate::X::clone` which is ignored")
}

// Proc-macro crates (e.g., serde) do not emit #[automatically_derived], so
// their impls have span.from_expansion() == true but no automatically_derived attr.
// We simulate this with a macro_rules! that produces an impl without that attribute.
test_verify_one_file_with_options! {
    #[test] external_derive_proc_macro_all ["--no-external-by-default"] => verus_code! {
        macro_rules! fake_serialize {
            ($t:ty) => {
                impl FakeSerialize for $t {
                    fn serialize(&self) -> u64 { 0 }
                }
            }
        }

        trait FakeSerialize {
            fn serialize(&self) -> u64;
        }

        #[verifier::external_derive]
        struct X {
            u: u64,
        }

        fake_serialize!(X);

        fn test(x: X) {
            // calling serialize on X should work since the impl is marked external
            let _ = x.serialize();
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] external_derive_proc_macro_named ["--no-external-by-default"] => verus_code! {
        macro_rules! fake_serialize {
            ($t:ty) => {
                impl FakeSerialize for $t {
                    fn serialize(&self) -> u64 { 0 }
                }
            }
        }

        trait FakeSerialize {
            fn serialize(&self) -> u64;
        }

        // only FakeSerialize is listed -- the macro-expanded impl should be ignored
        #[verifier::external_derive(FakeSerialize)]
        struct X {
            u: u64,
        }

        fake_serialize!(X);

        fn test(x: X) {
            let _ = x.serialize();
        }
    } => Ok(())
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

test_verify_one_file! {
    #[test] vec_deref_mut verus_code! {
        use vstd::prelude::*;

        fn test_implicit_via_adjustment() {
            let mut a = vec![1, 2];
            let b: &mut [u64] = &mut a;
            b[0] = 10;
            assert(a@ == seq![10, 2]);
        }

        fn test_overloaded_star_operator() {
            let mut a = vec![1, 2];
            let b: &mut [u64] = &mut *a;
            b[0] = 10;
            assert(a@ == seq![10, 2]);
        }

        fn test_overloaded_star_operator2() {
            let mut a = vec![1, 2];
            (*a)[1] = 20;
            assert(a@ == seq![1, 20]);
        }

        fn fails_implicit_via_adjustment() {
            let mut a = vec![1, 2];
            let b: &mut [u64] = &mut a;
            b[0] = 10;
            assert(a@ == seq![10, 2]);
            assert(false); // FAILS
        }

        fn fails_overloaded_star_operator() {
            let mut a = vec![1, 2];
            let b: &mut [u64] = &mut *a;
            b[0] = 10;
            assert(a@ == seq![10, 2]);
            assert(false); // FAILS
        }

        fn fails_overloaded_star_operator2() {
            let mut a = vec![1, 2];
            (*a)[1] = 20;
            assert(a@ == seq![1, 20]);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] hash_map_entry_api verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::hash::*;
        use std::collections::hash_map::*;
        use std::hash::*;

        fn test1() {
            let mut m = HashMap::<u64, u64>::new();

            // Use entry API to insert to the map

            let entry = m.entry(5);
            assert(entry.key() == 5 && entry.value() == None);

            let value_ref = entry.or_insert(20);
            assert(*value_ref == 20);

            *value_ref = 40;

            assert(m@.dom().contains(5) && m@[5] == 40);

            // Use entry API to remove from the map

            let entry = m.entry(5);
            match entry {
                Entry::Occupied(occupied_entry) => {
                    let (k, v) = occupied_entry.remove_entry();
                    assert(k == 5);
                    assert(v == 40);
                }
                Entry::Vacant(_) => {
                    assert(false);
                }
            }

            assert(!m@.dom().contains(5));

            assert(false); // FAILS
        }

        fn test_occupied_entry() {
            let mut m = HashMap::<u64, u64>::new();
            let entry = m.entry(5);
            let mut occ_entry = entry.insert_entry(20);

            assert(occ_entry.key() == 5);
            assert(occ_entry.value() == 20);

            let x = occ_entry.get();
            assert(*x == 20);

            let x = occ_entry.get_mut();
            assert(*x == 20);
            *x = 30;

            assert(occ_entry.key() == 5);
            assert(occ_entry.value() == 30);

            let x = occ_entry.into_mut();
            assert(*x == 30);
            *x = 40;

            assert(m@.dom().contains(5));
            assert(m@[5] == 40);

            // Now let's remove it

            let entry = m.entry(5);
            let mut occ_entry = entry.insert_entry(60);

            let (removed_key, removed_value) = occ_entry.remove_entry();
            assert(removed_key == 5);
            assert(removed_value == 60);

            assert(m@ =~= Map::empty());

            assert(false); // FAILS
        }

        fn test_occupied_entry2() {
            let mut m = HashMap::<u64, u64>::new();
            let entry = m.entry(5);
            let mut occ_entry = entry.insert_entry(20);

            let old_value = occ_entry.insert(17);
            assert(old_value == 20);

            assert(m@.dom().contains(5));
            assert(m@[5] == 17);

            let entry = m.entry(5);
            let mut occ_entry = entry.insert_entry(20);
            let mut old_value = occ_entry.remove();
            assert(old_value == 20);

            assert(m@ =~= Map::empty());

            assert(false); // FAILS
        }

        fn test_vacant_entry() {
            let mut m = HashMap::<u64, u64>::new();
            let entry = m.entry(5);

            let Entry::Vacant(vac_entry) = entry else { assert(false); return; };

            let k = vac_entry.into_key();
            assert(k == 5);

            assert(m@ =~= Map::empty());

            assert(false); // FAILS
        }

        fn test_vacant_entry2() {
            let mut m = HashMap::<u64, u64>::new();
            let entry = m.entry(5);

            let Entry::Vacant(vac_entry) = entry else { assert(false); return; };

            // do nothing

            assert(m@ =~= Map::empty());

            assert(false); // FAILS
        }

        fn test_vacant_entry3() {
            let mut m = HashMap::<u64, u64>::new();
            let entry = m.entry(5);

            let Entry::Vacant(vac_entry) = entry else { assert(false); return; };

            let r = vac_entry.insert(20);
            assert(*r == 20);
            *r = 30;

            assert(m@.dom().contains(5) && m[5] == 30);

            assert(false); // FAILS
        }

        fn test_vacant_entry4() {
            let mut m = HashMap::<u64, u64>::new();
            let entry = m.entry(5);

            let Entry::Vacant(vac_entry) = entry else { assert(false); return; };

            let mut occ_entry = vac_entry.insert_entry(20);
            let r = occ_entry.get_mut();
            assert(*r == 20);
            *r = 30;

            assert(m@.dom().contains(5) && m[5] == 30);

            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 7)
}

test_verify_one_file! {
    #[test] hash_map_clone_issue1835 verus_code! {
        use vstd::prelude::*;
        use std::collections::HashMap;

        pub struct WeirdPair {
            pub x: u64,
            pub y: u64,
        }

        impl Clone for WeirdPair {
            fn clone(&self) -> (ret: Self)
                ensures ret == (Self { x: self.x, y: 0 })
            {
                Self { x: self.x, y: 0 }
            }
        }

        fn test() {
            let mut h = HashMap::<u64, WeirdPair>::new();
            h.insert(0, WeirdPair { x: 1, y: 2 });
            let h2 = h.clone();
            assert(h2@.dom() == h@.dom());
            assert(h2@[0] == WeirdPair { x: 1, y: 0 } || h@[0] == h2@[0]);
        }

        fn test_fails() {
            let mut h = HashMap::<u64, WeirdPair>::new();
            h.insert(0, WeirdPair { x: 1, y: 2 });
            let h2 = h.clone();
            assert(h2@.dom() == h@.dom());
            assert(h2@[0] == WeirdPair { x: 1, y: 2 }); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] checked_rem_div_systematic verus_code! {
        use vstd::prelude::*;

        // These are all generated from actual rustc runs

        fn test_u8_checked_div() {
            let x = u8::checked_div(0, 0); assert(x == None);
            let x = u8::checked_div(0, 5); assert(x == Some(0u8));
            let x = u8::checked_div(0, 255); assert(x == Some(0u8));
            let x = u8::checked_div(10, 0); assert(x == None);
            let x = u8::checked_div(10, 5); assert(x == Some(2u8));
            let x = u8::checked_div(10, 255); assert(x == Some(0u8));
            let x = u8::checked_div(7, 0); assert(x == None);
            let x = u8::checked_div(7, 5); assert(x == Some(1u8));
            let x = u8::checked_div(7, 255); assert(x == Some(0u8));
            let x = u8::checked_div(255, 0); assert(x == None);
            let x = u8::checked_div(255, 5); assert(x == Some(51u8));
            let x = u8::checked_div(255, 255); assert(x == Some(1u8));
        }

        fn test_u8_checked_div_euclid() {
            let x = u8::checked_div_euclid(0, 0); assert(x == None);
            let x = u8::checked_div_euclid(0, 5); assert(x == Some(0u8));
            let x = u8::checked_div_euclid(0, 255); assert(x == Some(0u8));
            let x = u8::checked_div_euclid(10, 0); assert(x == None);
            let x = u8::checked_div_euclid(10, 5); assert(x == Some(2u8));
            let x = u8::checked_div_euclid(10, 255); assert(x == Some(0u8));
            let x = u8::checked_div_euclid(7, 0); assert(x == None);
            let x = u8::checked_div_euclid(7, 5); assert(x == Some(1u8));
            let x = u8::checked_div_euclid(7, 255); assert(x == Some(0u8));
            let x = u8::checked_div_euclid(255, 0); assert(x == None);
            let x = u8::checked_div_euclid(255, 5); assert(x == Some(51u8));
            let x = u8::checked_div_euclid(255, 255); assert(x == Some(1u8));
        }

        fn test_u8_checked_rem() {
            let x = u8::checked_rem(0, 0); assert(x == None);
            let x = u8::checked_rem(0, 5); assert(x == Some(0u8));
            let x = u8::checked_rem(0, 255); assert(x == Some(0u8));
            let x = u8::checked_rem(10, 0); assert(x == None);
            let x = u8::checked_rem(10, 5); assert(x == Some(0u8));
            let x = u8::checked_rem(10, 255); assert(x == Some(10u8));
            let x = u8::checked_rem(7, 0); assert(x == None);
            let x = u8::checked_rem(7, 5); assert(x == Some(2u8));
            let x = u8::checked_rem(7, 255); assert(x == Some(7u8));
            let x = u8::checked_rem(255, 0); assert(x == None);
            let x = u8::checked_rem(255, 5); assert(x == Some(0u8));
            let x = u8::checked_rem(255, 255); assert(x == Some(0u8));
        }

        fn test_u8_checked_rem_euclid() {
            let x = u8::checked_rem_euclid(0, 0); assert(x == None);
            let x = u8::checked_rem_euclid(0, 5); assert(x == Some(0u8));
            let x = u8::checked_rem_euclid(0, 255); assert(x == Some(0u8));
            let x = u8::checked_rem_euclid(10, 0); assert(x == None);
            let x = u8::checked_rem_euclid(10, 5); assert(x == Some(0u8));
            let x = u8::checked_rem_euclid(10, 255); assert(x == Some(10u8));
            let x = u8::checked_rem_euclid(7, 0); assert(x == None);
            let x = u8::checked_rem_euclid(7, 5); assert(x == Some(2u8));
            let x = u8::checked_rem_euclid(7, 255); assert(x == Some(7u8));
            let x = u8::checked_rem_euclid(255, 0); assert(x == None);
            let x = u8::checked_rem_euclid(255, 5); assert(x == Some(0u8));
            let x = u8::checked_rem_euclid(255, 255); assert(x == Some(0u8));
        }

        fn test_i8_checked_div() {
            let x = i8::checked_div(-128, -128); assert(x == Some(1i8));
            let x = i8::checked_div(-128, -5); assert(x == Some(25i8));
            let x = i8::checked_div(-128, 0); assert(x == None);
            let x = i8::checked_div(-128, 5); assert(x == Some(-25i8));
            let x = i8::checked_div(-128, 127); assert(x == Some(-1i8));
            let x = i8::checked_div(-128, -1); assert(x == None);
            let x = i8::checked_div(-128, 1); assert(x == Some(-128i8));
            let x = i8::checked_div(-10, -128); assert(x == Some(0i8));
            let x = i8::checked_div(-10, -5); assert(x == Some(2i8));
            let x = i8::checked_div(-10, 0); assert(x == None);
            let x = i8::checked_div(-10, 5); assert(x == Some(-2i8));
            let x = i8::checked_div(-10, 127); assert(x == Some(0i8));
            let x = i8::checked_div(-10, -1); assert(x == Some(10i8));
        }

        fn test_i8_checked_div_2() {
            let x = i8::checked_div(-10, 1); assert(x == Some(-10i8));
            let x = i8::checked_div(-7, -128); assert(x == Some(0i8));
            let x = i8::checked_div(-7, -5); assert(x == Some(1i8));
            let x = i8::checked_div(-7, 0); assert(x == None);
            let x = i8::checked_div(-7, 5); assert(x == Some(-1i8));
            let x = i8::checked_div(-7, 127); assert(x == Some(0i8));
            let x = i8::checked_div(-7, -1); assert(x == Some(7i8));
            let x = i8::checked_div(-7, 1); assert(x == Some(-7i8));
            let x = i8::checked_div(0, -128); assert(x == Some(0i8));
            let x = i8::checked_div(0, -5); assert(x == Some(0i8));
            let x = i8::checked_div(0, 0); assert(x == None);
            let x = i8::checked_div(0, 5); assert(x == Some(0i8));
            let x = i8::checked_div(0, 127); assert(x == Some(0i8));
        }

        fn test_i8_checked_div_3() {
            let x = i8::checked_div(0, -1); assert(x == Some(0i8));
            let x = i8::checked_div(0, 1); assert(x == Some(0i8));
            let x = i8::checked_div(7, -128); assert(x == Some(0i8));
            let x = i8::checked_div(7, -5); assert(x == Some(-1i8));
            let x = i8::checked_div(7, 0); assert(x == None);
            let x = i8::checked_div(7, 5); assert(x == Some(1i8));
            let x = i8::checked_div(7, 127); assert(x == Some(0i8));
            let x = i8::checked_div(7, -1); assert(x == Some(-7i8));
            let x = i8::checked_div(7, 1); assert(x == Some(7i8));
            let x = i8::checked_div(10, -128); assert(x == Some(0i8));
            let x = i8::checked_div(10, -5); assert(x == Some(-2i8));
            let x = i8::checked_div(10, 0); assert(x == None);
            let x = i8::checked_div(10, 5); assert(x == Some(2i8));
        }

        fn test_i8_checked_div_4() {
            let x = i8::checked_div(10, 127); assert(x == Some(0i8));
            let x = i8::checked_div(10, -1); assert(x == Some(-10i8));
            let x = i8::checked_div(10, 1); assert(x == Some(10i8));
            let x = i8::checked_div(127, -128); assert(x == Some(0i8));
            let x = i8::checked_div(127, -5); assert(x == Some(-25i8));
            let x = i8::checked_div(127, 0); assert(x == None);
            let x = i8::checked_div(127, 5); assert(x == Some(25i8));
            let x = i8::checked_div(127, 127); assert(x == Some(1i8));
            let x = i8::checked_div(127, -1); assert(x == Some(-127i8));
            let x = i8::checked_div(127, 1); assert(x == Some(127i8));
        }

        fn test_i8_checked_div_euclid() {
            let x = i8::checked_div_euclid(-128, -128); assert(x == Some(1i8));
            let x = i8::checked_div_euclid(-128, -5); assert(x == Some(26i8));
            let x = i8::checked_div_euclid(-128, 0); assert(x == None);
            let x = i8::checked_div_euclid(-128, 5); assert(x == Some(-26i8));
            let x = i8::checked_div_euclid(-128, 127); assert(x == Some(-2i8));
            let x = i8::checked_div_euclid(-128, -1); assert(x == None);
            let x = i8::checked_div_euclid(-128, 1); assert(x == Some(-128i8));
            let x = i8::checked_div_euclid(-10, -128); assert(x == Some(1i8));
            let x = i8::checked_div_euclid(-10, -5); assert(x == Some(2i8));
            let x = i8::checked_div_euclid(-10, 0); assert(x == None);
            let x = i8::checked_div_euclid(-10, 5); assert(x == Some(-2i8));
            let x = i8::checked_div_euclid(-10, 127); assert(x == Some(-1i8));
            let x = i8::checked_div_euclid(-10, -1); assert(x == Some(10i8));
        }

        fn test_i8_checked_div_euclid_2() {
            let x = i8::checked_div_euclid(-10, 1); assert(x == Some(-10i8));
            let x = i8::checked_div_euclid(-7, -128); assert(x == Some(1i8));
            let x = i8::checked_div_euclid(-7, -5); assert(x == Some(2i8));
            let x = i8::checked_div_euclid(-7, 0); assert(x == None);
            let x = i8::checked_div_euclid(-7, 5); assert(x == Some(-2i8));
            let x = i8::checked_div_euclid(-7, 127); assert(x == Some(-1i8));
            let x = i8::checked_div_euclid(-7, -1); assert(x == Some(7i8));
            let x = i8::checked_div_euclid(-7, 1); assert(x == Some(-7i8));
            let x = i8::checked_div_euclid(0, -128); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(0, -5); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(0, 0); assert(x == None);
            let x = i8::checked_div_euclid(0, 5); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(0, 127); assert(x == Some(0i8));
        }

        fn test_i8_checked_div_euclid_3() {
            let x = i8::checked_div_euclid(0, -1); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(0, 1); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(7, -128); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(7, -5); assert(x == Some(-1i8));
            let x = i8::checked_div_euclid(7, 0); assert(x == None);
            let x = i8::checked_div_euclid(7, 5); assert(x == Some(1i8));
            let x = i8::checked_div_euclid(7, 127); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(7, -1); assert(x == Some(-7i8));
            let x = i8::checked_div_euclid(7, 1); assert(x == Some(7i8));
            let x = i8::checked_div_euclid(10, -128); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(10, -5); assert(x == Some(-2i8));
            let x = i8::checked_div_euclid(10, 0); assert(x == None);
            let x = i8::checked_div_euclid(10, 5); assert(x == Some(2i8));
        }

        fn test_i8_checked_div_euclid_4() {
            let x = i8::checked_div_euclid(10, 127); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(10, -1); assert(x == Some(-10i8));
            let x = i8::checked_div_euclid(10, 1); assert(x == Some(10i8));
            let x = i8::checked_div_euclid(127, -128); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(127, -5); assert(x == Some(-25i8));
            let x = i8::checked_div_euclid(127, 0); assert(x == None);
            let x = i8::checked_div_euclid(127, 5); assert(x == Some(25i8));
            let x = i8::checked_div_euclid(127, 127); assert(x == Some(1i8));
            let x = i8::checked_div_euclid(127, -1); assert(x == Some(-127i8));
            let x = i8::checked_div_euclid(127, 1); assert(x == Some(127i8));
        }

        fn test_i8_checked_rem() {
            let x = i8::checked_rem(-128, -128); assert(x == Some(0i8));
            let x = i8::checked_rem(-128, -5); assert(x == Some(-3i8));
            let x = i8::checked_rem(-128, 0); assert(x == None);
            let x = i8::checked_rem(-128, 5); assert(x == Some(-3i8));
            let x = i8::checked_rem(-128, 127); assert(x == Some(-1i8));
            let x = i8::checked_rem(-128, -1); assert(x == None);
            let x = i8::checked_rem(-128, 1); assert(x == Some(0i8));
            let x = i8::checked_rem(-10, -128); assert(x == Some(-10i8));
            let x = i8::checked_rem(-10, -5); assert(x == Some(0i8));
            let x = i8::checked_rem(-10, 0); assert(x == None);
            let x = i8::checked_rem(-10, 5); assert(x == Some(0i8));
            let x = i8::checked_rem(-10, 127); assert(x == Some(-10i8));
            let x = i8::checked_rem(-10, -1); assert(x == Some(0i8));
        }

        fn test_i8_checked_rem_2() {
            let x = i8::checked_rem(-10, 1); assert(x == Some(0i8));
            let x = i8::checked_rem(-7, -128); assert(x == Some(-7i8));
            let x = i8::checked_rem(-7, -5); assert(x == Some(-2i8));
            let x = i8::checked_rem(-7, 0); assert(x == None);
            let x = i8::checked_rem(-7, 5); assert(x == Some(-2i8));
            let x = i8::checked_rem(-7, 127); assert(x == Some(-7i8));
            let x = i8::checked_rem(-7, -1); assert(x == Some(0i8));
            let x = i8::checked_rem(-7, 1); assert(x == Some(0i8));
            let x = i8::checked_rem(0, -128); assert(x == Some(0i8));
            let x = i8::checked_rem(0, -5); assert(x == Some(0i8));
            let x = i8::checked_rem(0, 0); assert(x == None);
            let x = i8::checked_rem(0, 5); assert(x == Some(0i8));
            let x = i8::checked_rem(0, 127); assert(x == Some(0i8));
        }

        fn test_i8_checked_rem_3() {
            let x = i8::checked_rem(0, -1); assert(x == Some(0i8));
            let x = i8::checked_rem(0, 1); assert(x == Some(0i8));
            let x = i8::checked_rem(7, -128); assert(x == Some(7i8));
            let x = i8::checked_rem(7, -5); assert(x == Some(2i8));
            let x = i8::checked_rem(7, 0); assert(x == None);
            let x = i8::checked_rem(7, 5); assert(x == Some(2i8));
            let x = i8::checked_rem(7, 127); assert(x == Some(7i8));
            let x = i8::checked_rem(7, -1); assert(x == Some(0i8));
            let x = i8::checked_rem(7, 1); assert(x == Some(0i8));
            let x = i8::checked_rem(10, -128); assert(x == Some(10i8));
            let x = i8::checked_rem(10, -5); assert(x == Some(0i8));
            let x = i8::checked_rem(10, 0); assert(x == None);
            let x = i8::checked_rem(10, 5); assert(x == Some(0i8));
        }

        fn test_i8_checked_rem_4() {
            let x = i8::checked_rem(10, 127); assert(x == Some(10i8));
            let x = i8::checked_rem(10, -1); assert(x == Some(0i8));
            let x = i8::checked_rem(10, 1); assert(x == Some(0i8));
            let x = i8::checked_rem(127, -128); assert(x == Some(127i8));
            let x = i8::checked_rem(127, -5); assert(x == Some(2i8));
            let x = i8::checked_rem(127, 0); assert(x == None);
            let x = i8::checked_rem(127, 5); assert(x == Some(2i8));
            let x = i8::checked_rem(127, 127); assert(x == Some(0i8));
            let x = i8::checked_rem(127, -1); assert(x == Some(0i8));
            let x = i8::checked_rem(127, 1); assert(x == Some(0i8));
        }

        fn test_i8_checked_rem_euclid() {
            let x = i8::checked_rem_euclid(-128, -128); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(-128, -5); assert(x == Some(2i8));
            let x = i8::checked_rem_euclid(-128, 0); assert(x == None);
            let x = i8::checked_rem_euclid(-128, 5); assert(x == Some(2i8));
            let x = i8::checked_rem_euclid(-128, 127); assert(x == Some(126i8));
            let x = i8::checked_rem_euclid(-128, -1); assert(x == None);
            let x = i8::checked_rem_euclid(-128, 1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(-10, -128); assert(x == Some(118i8));
            let x = i8::checked_rem_euclid(-10, -5); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(-10, 0); assert(x == None);
            let x = i8::checked_rem_euclid(-10, 5); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(-10, 127); assert(x == Some(117i8));
            let x = i8::checked_rem_euclid(-10, -1); assert(x == Some(0i8));
        }

        fn test_i8_checked_rem_euclid_2() {
            let x = i8::checked_rem_euclid(-10, 1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(-7, -128); assert(x == Some(121i8));
            let x = i8::checked_rem_euclid(-7, -5); assert(x == Some(3i8));
            let x = i8::checked_rem_euclid(-7, 0); assert(x == None);
            let x = i8::checked_rem_euclid(-7, 5); assert(x == Some(3i8));
            let x = i8::checked_rem_euclid(-7, 127); assert(x == Some(120i8));
            let x = i8::checked_rem_euclid(-7, -1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(-7, 1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(0, -128); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(0, -5); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(0, 0); assert(x == None);
            let x = i8::checked_rem_euclid(0, 5); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(0, 127); assert(x == Some(0i8));
        }

        fn test_i8_checked_rem_euclid_3() {
            let x = i8::checked_rem_euclid(0, -1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(0, 1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(7, -128); assert(x == Some(7i8));
            let x = i8::checked_rem_euclid(7, -5); assert(x == Some(2i8));
            let x = i8::checked_rem_euclid(7, 0); assert(x == None);
            let x = i8::checked_rem_euclid(7, 5); assert(x == Some(2i8));
            let x = i8::checked_rem_euclid(7, 127); assert(x == Some(7i8));
            let x = i8::checked_rem_euclid(7, -1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(7, 1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(10, -128); assert(x == Some(10i8));
            let x = i8::checked_rem_euclid(10, -5); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(10, 0); assert(x == None);
            let x = i8::checked_rem_euclid(10, 5); assert(x == Some(0i8));
        }

        fn test_i8_checked_rem_euclid_4() {
            let x = i8::checked_rem_euclid(10, 127); assert(x == Some(10i8));
            let x = i8::checked_rem_euclid(10, -1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(10, 1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(127, -128); assert(x == Some(127i8));
            let x = i8::checked_rem_euclid(127, -5); assert(x == Some(2i8));
            let x = i8::checked_rem_euclid(127, 0); assert(x == None);
            let x = i8::checked_rem_euclid(127, 5); assert(x == Some(2i8));
            let x = i8::checked_rem_euclid(127, 127); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(127, -1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(127, 1); assert(x == Some(0i8));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] checked_rem_div_systematic_fails verus_code! {
        use vstd::prelude::*;

        fn fails_u8_checked_div() {
            let x = u8::checked_div(0, 0); assert(x == None);
            let x = u8::checked_div(0, 5); assert(x == Some(0u8));
            let x = u8::checked_div(0, 255); assert(x == Some(0u8));
            let x = u8::checked_div(10, 0); assert(x == None);
            let x = u8::checked_div(10, 5); assert(x == Some(2u8));
            let x = u8::checked_div(10, 255); assert(x == Some(0u8));
            let x = u8::checked_div(7, 0); assert(x == None);
            let x = u8::checked_div(7, 5); assert(x == Some(1u8));
            let x = u8::checked_div(7, 255); assert(x == Some(0u8));
            let x = u8::checked_div(255, 0); assert(x == None);
            let x = u8::checked_div(255, 5); assert(x == Some(51u8));
            let x = u8::checked_div(255, 255); assert(x == Some(1u8));
            assert(false); // FAILS
        }

        fn fails_u8_checked_div_euclid() {
            let x = u8::checked_div_euclid(0, 0); assert(x == None);
            let x = u8::checked_div_euclid(0, 5); assert(x == Some(0u8));
            let x = u8::checked_div_euclid(0, 255); assert(x == Some(0u8));
            let x = u8::checked_div_euclid(10, 0); assert(x == None);
            let x = u8::checked_div_euclid(10, 5); assert(x == Some(2u8));
            let x = u8::checked_div_euclid(10, 255); assert(x == Some(0u8));
            let x = u8::checked_div_euclid(7, 0); assert(x == None);
            let x = u8::checked_div_euclid(7, 5); assert(x == Some(1u8));
            let x = u8::checked_div_euclid(7, 255); assert(x == Some(0u8));
            let x = u8::checked_div_euclid(255, 0); assert(x == None);
            let x = u8::checked_div_euclid(255, 5); assert(x == Some(51u8));
            let x = u8::checked_div_euclid(255, 255); assert(x == Some(1u8));
            assert(false); // FAILS
        }

        fn fails_u8_checked_rem() {
            let x = u8::checked_rem(0, 0); assert(x == None);
            let x = u8::checked_rem(0, 5); assert(x == Some(0u8));
            let x = u8::checked_rem(0, 255); assert(x == Some(0u8));
            let x = u8::checked_rem(10, 0); assert(x == None);
            let x = u8::checked_rem(10, 5); assert(x == Some(0u8));
            let x = u8::checked_rem(10, 255); assert(x == Some(10u8));
            let x = u8::checked_rem(7, 0); assert(x == None);
            let x = u8::checked_rem(7, 5); assert(x == Some(2u8));
            let x = u8::checked_rem(7, 255); assert(x == Some(7u8));
            let x = u8::checked_rem(255, 0); assert(x == None);
            let x = u8::checked_rem(255, 5); assert(x == Some(0u8));
            let x = u8::checked_rem(255, 255); assert(x == Some(0u8));
            assert(false); // FAILS
        }

        fn fails_u8_checked_rem_euclid() {
            let x = u8::checked_rem_euclid(0, 0); assert(x == None);
            let x = u8::checked_rem_euclid(0, 5); assert(x == Some(0u8));
            let x = u8::checked_rem_euclid(0, 255); assert(x == Some(0u8));
            let x = u8::checked_rem_euclid(10, 0); assert(x == None);
            let x = u8::checked_rem_euclid(10, 5); assert(x == Some(0u8));
            let x = u8::checked_rem_euclid(10, 255); assert(x == Some(10u8));
            let x = u8::checked_rem_euclid(7, 0); assert(x == None);
            let x = u8::checked_rem_euclid(7, 5); assert(x == Some(2u8));
            let x = u8::checked_rem_euclid(7, 255); assert(x == Some(7u8));
            let x = u8::checked_rem_euclid(255, 0); assert(x == None);
            let x = u8::checked_rem_euclid(255, 5); assert(x == Some(0u8));
            let x = u8::checked_rem_euclid(255, 255); assert(x == Some(0u8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_div() {
            let x = i8::checked_div(-128, -128); assert(x == Some(1i8));
            let x = i8::checked_div(-128, -5); assert(x == Some(25i8));
            let x = i8::checked_div(-128, 0); assert(x == None);
            let x = i8::checked_div(-128, 5); assert(x == Some(-25i8));
            let x = i8::checked_div(-128, 127); assert(x == Some(-1i8));
            let x = i8::checked_div(-128, -1); assert(x == None);
            let x = i8::checked_div(-128, 1); assert(x == Some(-128i8));
            let x = i8::checked_div(-10, -128); assert(x == Some(0i8));
            let x = i8::checked_div(-10, -5); assert(x == Some(2i8));
            let x = i8::checked_div(-10, 0); assert(x == None);
            let x = i8::checked_div(-10, 5); assert(x == Some(-2i8));
            let x = i8::checked_div(-10, 127); assert(x == Some(0i8));
            let x = i8::checked_div(-10, -1); assert(x == Some(10i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_div_2() {
            let x = i8::checked_div(-10, 1); assert(x == Some(-10i8));
            let x = i8::checked_div(-7, -128); assert(x == Some(0i8));
            let x = i8::checked_div(-7, -5); assert(x == Some(1i8));
            let x = i8::checked_div(-7, 0); assert(x == None);
            let x = i8::checked_div(-7, 5); assert(x == Some(-1i8));
            let x = i8::checked_div(-7, 127); assert(x == Some(0i8));
            let x = i8::checked_div(-7, -1); assert(x == Some(7i8));
            let x = i8::checked_div(-7, 1); assert(x == Some(-7i8));
            let x = i8::checked_div(0, -128); assert(x == Some(0i8));
            let x = i8::checked_div(0, -5); assert(x == Some(0i8));
            let x = i8::checked_div(0, 0); assert(x == None);
            let x = i8::checked_div(0, 5); assert(x == Some(0i8));
            let x = i8::checked_div(0, 127); assert(x == Some(0i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_div_3() {
            let x = i8::checked_div(0, -1); assert(x == Some(0i8));
            let x = i8::checked_div(0, 1); assert(x == Some(0i8));
            let x = i8::checked_div(7, -128); assert(x == Some(0i8));
            let x = i8::checked_div(7, -5); assert(x == Some(-1i8));
            let x = i8::checked_div(7, 0); assert(x == None);
            let x = i8::checked_div(7, 5); assert(x == Some(1i8));
            let x = i8::checked_div(7, 127); assert(x == Some(0i8));
            let x = i8::checked_div(7, -1); assert(x == Some(-7i8));
            let x = i8::checked_div(7, 1); assert(x == Some(7i8));
            let x = i8::checked_div(10, -128); assert(x == Some(0i8));
            let x = i8::checked_div(10, -5); assert(x == Some(-2i8));
            let x = i8::checked_div(10, 0); assert(x == None);
            let x = i8::checked_div(10, 5); assert(x == Some(2i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_div_4() {
            let x = i8::checked_div(10, 127); assert(x == Some(0i8));
            let x = i8::checked_div(10, -1); assert(x == Some(-10i8));
            let x = i8::checked_div(10, 1); assert(x == Some(10i8));
            let x = i8::checked_div(127, -128); assert(x == Some(0i8));
            let x = i8::checked_div(127, -5); assert(x == Some(-25i8));
            let x = i8::checked_div(127, 0); assert(x == None);
            let x = i8::checked_div(127, 5); assert(x == Some(25i8));
            let x = i8::checked_div(127, 127); assert(x == Some(1i8));
            let x = i8::checked_div(127, -1); assert(x == Some(-127i8));
            let x = i8::checked_div(127, 1); assert(x == Some(127i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_div_euclid() {
            let x = i8::checked_div_euclid(-128, -128); assert(x == Some(1i8));
            let x = i8::checked_div_euclid(-128, -5); assert(x == Some(26i8));
            let x = i8::checked_div_euclid(-128, 0); assert(x == None);
            let x = i8::checked_div_euclid(-128, 5); assert(x == Some(-26i8));
            let x = i8::checked_div_euclid(-128, 127); assert(x == Some(-2i8));
            let x = i8::checked_div_euclid(-128, -1); assert(x == None);
            let x = i8::checked_div_euclid(-128, 1); assert(x == Some(-128i8));
            let x = i8::checked_div_euclid(-10, -128); assert(x == Some(1i8));
            let x = i8::checked_div_euclid(-10, -5); assert(x == Some(2i8));
            let x = i8::checked_div_euclid(-10, 0); assert(x == None);
            let x = i8::checked_div_euclid(-10, 5); assert(x == Some(-2i8));
            let x = i8::checked_div_euclid(-10, 127); assert(x == Some(-1i8));
            let x = i8::checked_div_euclid(-10, -1); assert(x == Some(10i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_div_euclid_2() {
            let x = i8::checked_div_euclid(-10, 1); assert(x == Some(-10i8));
            let x = i8::checked_div_euclid(-7, -128); assert(x == Some(1i8));
            let x = i8::checked_div_euclid(-7, -5); assert(x == Some(2i8));
            let x = i8::checked_div_euclid(-7, 0); assert(x == None);
            let x = i8::checked_div_euclid(-7, 5); assert(x == Some(-2i8));
            let x = i8::checked_div_euclid(-7, 127); assert(x == Some(-1i8));
            let x = i8::checked_div_euclid(-7, -1); assert(x == Some(7i8));
            let x = i8::checked_div_euclid(-7, 1); assert(x == Some(-7i8));
            let x = i8::checked_div_euclid(0, -128); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(0, -5); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(0, 0); assert(x == None);
            let x = i8::checked_div_euclid(0, 5); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(0, 127); assert(x == Some(0i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_div_euclid_3() {
            let x = i8::checked_div_euclid(0, -1); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(0, 1); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(7, -128); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(7, -5); assert(x == Some(-1i8));
            let x = i8::checked_div_euclid(7, 0); assert(x == None);
            let x = i8::checked_div_euclid(7, 5); assert(x == Some(1i8));
            let x = i8::checked_div_euclid(7, 127); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(7, -1); assert(x == Some(-7i8));
            let x = i8::checked_div_euclid(7, 1); assert(x == Some(7i8));
            let x = i8::checked_div_euclid(10, -128); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(10, -5); assert(x == Some(-2i8));
            let x = i8::checked_div_euclid(10, 0); assert(x == None);
            let x = i8::checked_div_euclid(10, 5); assert(x == Some(2i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_div_euclid_4() {
            let x = i8::checked_div_euclid(10, 127); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(10, -1); assert(x == Some(-10i8));
            let x = i8::checked_div_euclid(10, 1); assert(x == Some(10i8));
            let x = i8::checked_div_euclid(127, -128); assert(x == Some(0i8));
            let x = i8::checked_div_euclid(127, -5); assert(x == Some(-25i8));
            let x = i8::checked_div_euclid(127, 0); assert(x == None);
            let x = i8::checked_div_euclid(127, 5); assert(x == Some(25i8));
            let x = i8::checked_div_euclid(127, 127); assert(x == Some(1i8));
            let x = i8::checked_div_euclid(127, -1); assert(x == Some(-127i8));
            let x = i8::checked_div_euclid(127, 1); assert(x == Some(127i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_rem() {
            let x = i8::checked_rem(-128, -128); assert(x == Some(0i8));
            let x = i8::checked_rem(-128, -5); assert(x == Some(-3i8));
            let x = i8::checked_rem(-128, 0); assert(x == None);
            let x = i8::checked_rem(-128, 5); assert(x == Some(-3i8));
            let x = i8::checked_rem(-128, 127); assert(x == Some(-1i8));
            let x = i8::checked_rem(-128, -1); assert(x == None);
            let x = i8::checked_rem(-128, 1); assert(x == Some(0i8));
            let x = i8::checked_rem(-10, -128); assert(x == Some(-10i8));
            let x = i8::checked_rem(-10, -5); assert(x == Some(0i8));
            let x = i8::checked_rem(-10, 0); assert(x == None);
            let x = i8::checked_rem(-10, 5); assert(x == Some(0i8));
            let x = i8::checked_rem(-10, 127); assert(x == Some(-10i8));
            let x = i8::checked_rem(-10, -1); assert(x == Some(0i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_rem_2() {
            let x = i8::checked_rem(-10, 1); assert(x == Some(0i8));
            let x = i8::checked_rem(-7, -128); assert(x == Some(-7i8));
            let x = i8::checked_rem(-7, -5); assert(x == Some(-2i8));
            let x = i8::checked_rem(-7, 0); assert(x == None);
            let x = i8::checked_rem(-7, 5); assert(x == Some(-2i8));
            let x = i8::checked_rem(-7, 127); assert(x == Some(-7i8));
            let x = i8::checked_rem(-7, -1); assert(x == Some(0i8));
            let x = i8::checked_rem(-7, 1); assert(x == Some(0i8));
            let x = i8::checked_rem(0, -128); assert(x == Some(0i8));
            let x = i8::checked_rem(0, -5); assert(x == Some(0i8));
            let x = i8::checked_rem(0, 0); assert(x == None);
            let x = i8::checked_rem(0, 5); assert(x == Some(0i8));
            let x = i8::checked_rem(0, 127); assert(x == Some(0i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_rem_3() {
            let x = i8::checked_rem(0, -1); assert(x == Some(0i8));
            let x = i8::checked_rem(0, 1); assert(x == Some(0i8));
            let x = i8::checked_rem(7, -128); assert(x == Some(7i8));
            let x = i8::checked_rem(7, -5); assert(x == Some(2i8));
            let x = i8::checked_rem(7, 0); assert(x == None);
            let x = i8::checked_rem(7, 5); assert(x == Some(2i8));
            let x = i8::checked_rem(7, 127); assert(x == Some(7i8));
            let x = i8::checked_rem(7, -1); assert(x == Some(0i8));
            let x = i8::checked_rem(7, 1); assert(x == Some(0i8));
            let x = i8::checked_rem(10, -128); assert(x == Some(10i8));
            let x = i8::checked_rem(10, -5); assert(x == Some(0i8));
            let x = i8::checked_rem(10, 0); assert(x == None);
            let x = i8::checked_rem(10, 5); assert(x == Some(0i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_rem_4() {
            let x = i8::checked_rem(10, 127); assert(x == Some(10i8));
            let x = i8::checked_rem(10, -1); assert(x == Some(0i8));
            let x = i8::checked_rem(10, 1); assert(x == Some(0i8));
            let x = i8::checked_rem(127, -128); assert(x == Some(127i8));
            let x = i8::checked_rem(127, -5); assert(x == Some(2i8));
            let x = i8::checked_rem(127, 0); assert(x == None);
            let x = i8::checked_rem(127, 5); assert(x == Some(2i8));
            let x = i8::checked_rem(127, 127); assert(x == Some(0i8));
            let x = i8::checked_rem(127, -1); assert(x == Some(0i8));
            let x = i8::checked_rem(127, 1); assert(x == Some(0i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_rem_euclid() {
            let x = i8::checked_rem_euclid(-128, -128); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(-128, -5); assert(x == Some(2i8));
            let x = i8::checked_rem_euclid(-128, 0); assert(x == None);
            let x = i8::checked_rem_euclid(-128, 5); assert(x == Some(2i8));
            let x = i8::checked_rem_euclid(-128, 127); assert(x == Some(126i8));
            let x = i8::checked_rem_euclid(-128, -1); assert(x == None);
            let x = i8::checked_rem_euclid(-128, 1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(-10, -128); assert(x == Some(118i8));
            let x = i8::checked_rem_euclid(-10, -5); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(-10, 0); assert(x == None);
            let x = i8::checked_rem_euclid(-10, 5); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(-10, 127); assert(x == Some(117i8));
            let x = i8::checked_rem_euclid(-10, -1); assert(x == Some(0i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_rem_euclid_2() {
            let x = i8::checked_rem_euclid(-10, 1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(-7, -128); assert(x == Some(121i8));
            let x = i8::checked_rem_euclid(-7, -5); assert(x == Some(3i8));
            let x = i8::checked_rem_euclid(-7, 0); assert(x == None);
            let x = i8::checked_rem_euclid(-7, 5); assert(x == Some(3i8));
            let x = i8::checked_rem_euclid(-7, 127); assert(x == Some(120i8));
            let x = i8::checked_rem_euclid(-7, -1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(-7, 1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(0, -128); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(0, -5); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(0, 0); assert(x == None);
            let x = i8::checked_rem_euclid(0, 5); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(0, 127); assert(x == Some(0i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_rem_euclid_3() {
            let x = i8::checked_rem_euclid(0, -1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(0, 1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(7, -128); assert(x == Some(7i8));
            let x = i8::checked_rem_euclid(7, -5); assert(x == Some(2i8));
            let x = i8::checked_rem_euclid(7, 0); assert(x == None);
            let x = i8::checked_rem_euclid(7, 5); assert(x == Some(2i8));
            let x = i8::checked_rem_euclid(7, 127); assert(x == Some(7i8));
            let x = i8::checked_rem_euclid(7, -1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(7, 1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(10, -128); assert(x == Some(10i8));
            let x = i8::checked_rem_euclid(10, -5); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(10, 0); assert(x == None);
            let x = i8::checked_rem_euclid(10, 5); assert(x == Some(0i8));
            assert(false); // FAILS
        }

        fn fails_i8_checked_rem_euclid_4() {
            let x = i8::checked_rem_euclid(10, 127); assert(x == Some(10i8));
            let x = i8::checked_rem_euclid(10, -1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(10, 1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(127, -128); assert(x == Some(127i8));
            let x = i8::checked_rem_euclid(127, -5); assert(x == Some(2i8));
            let x = i8::checked_rem_euclid(127, 0); assert(x == None);
            let x = i8::checked_rem_euclid(127, 5); assert(x == Some(2i8));
            let x = i8::checked_rem_euclid(127, 127); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(127, -1); assert(x == Some(0i8));
            let x = i8::checked_rem_euclid(127, 1); assert(x == Some(0i8));
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 20)
}

test_verify_one_file! {
    #[test] nonzero verus_code! {

        use vstd::prelude::*;
        use vstd::std_specs::nonzero::*;
        use std::num::{NonZeroU64, NonZeroI32};

        fn test() {
            let x = NonZeroI32::new(-20).unwrap();
            assert(x@ == -20);

            let x1 = x.clone();
            assert(x1@ == -20);

            let x2 = unsafe { NonZeroI32::new_unchecked(30)};
            assert(x2@ == 30);

            // assert(x1 < x2); SpecOrd is not supported.

            let b = x1 < x2;
            assert(b);

            let x3 = x2.get();
            assert(x3 == 30);
        }

        fn test_bitor() {
            let x = NonZeroU64::new(0x1011).unwrap();
            let y = NonZeroU64::new(0x100).unwrap();
            let z = x | y;
            assert(0x1011 | 0x100 == 0x1111) by (compute_only);
            assert(z@ == 0x1111);

            let z1 = x | 0x1000;
            assert(0x1011 == 0x1011 | 0x1000) by (compute_only);
            assert(z1@ == x@);
            assert(z1 == x);
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] impl_not_issue2519 verus_code! {
        use std::ops::*;
        use vstd::prelude::*;
        use vstd::std_specs::ops::*;

        #[derive(Copy, Clone, PartialEq, Eq)]
        pub enum B {
            True,
            False,
        }

        impl Not for B {
            type Output = Self;

            fn not(self) -> (res: Self)
                ensures
                    self is True ==> res is False,
                    self is False ==> res is True,
            {
                match self {
                    B::True => B::False,
                    B::False => B::True,
                }
            }
        }

        impl NotSpecImpl for B {
            open spec fn obeys_not_spec() -> bool {
                true
            }

            open spec fn not_req(self) -> bool {
                true
            }

            open spec fn not_spec(self) -> Self::Output {
                match self {
                    B::True => B::False,
                    B::False => B::True,
                }
            }
        }

        fn main() {
            let c1 = B::True.not();
            assert(c1 == B::False);

            let c2 = !B::True;
            assert(c2 == B::False);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] impl_neg_issue2519 verus_code! {
        use std::ops::*;
        use vstd::prelude::*;
        use vstd::std_specs::ops::*;

        #[derive(Copy, Clone, PartialEq, Eq)]
        pub enum B {
            True,
            False,
        }

        impl Neg for B {
            type Output = Self;

            fn neg(self) -> (res: Self)
                ensures
                    self is True ==> res is False,
                    self is False ==> res is True,
            {
                match self {
                    B::True => B::False,
                    B::False => B::True,
                }
            }
        }

        impl NegSpecImpl for B {
            open spec fn obeys_neg_spec() -> bool {
                true
            }

            open spec fn neg_req(self) -> bool {
                true
            }

            open spec fn neg_spec(self) -> Self::Output {
                match self {
                    B::True => B::False,
                    B::False => B::True,
                }
            }
        }

        fn main() {
            let c1 = B::True.neg();
            assert(c1 == B::False);

            let c2 = -B::True;
            assert(c2 == B::False);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unary_op_of_refs verus_code! {
        fn test_not() {
            let x = false;
            let x_ref = &x;

            let y1 = !x;
            let y2 = !x_ref;
            assert(y1 == true);
            assert(y2 == true);
        }

        fn test_bitnot() {
            let x: u8 = 0;
            let x_ref = &x;

            assert(!0u8 == 255) by(compute_only);

            let y1 = !x;
            let y2 = !x_ref;
            assert(y1 == 255);
            assert(y2 == 255);
        }

        fn test_neg() {
            let x: i8 = 10;
            let x_ref = &x;

            let y1 = -x;
            let y2 = -x_ref;
            assert(y1 == -10);
            assert(y2 == -10);
        }
    } => Ok(())
}
