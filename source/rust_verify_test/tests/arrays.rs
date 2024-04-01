#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        use vstd::array::*;

        fn test(ar: [u8; 20])
            requires ar[1] == 19
        {
            let x = array_index_get(&ar, 1);
            assert(x == 19);
        }

        fn test2(ar: [u8; 20]) {
            let y = array_index_get(&ar, 20); // FAILS
        }

        fn test3(ar: [u8; 20]) {
            assert(ar@.len() == 20);
        }

        fn test4(ar: [u8; 20]) {
            assert(ar@.len() == 21); // FAILS
        }

        fn test5<const N: usize>(ar: [u8; N]) {
            assert(ar@.len() == N);
        }

        fn test6(ar: [u8; 20]) {
            let mut ar = ar;
            ar.set(7, 50);
            assert(ar[7] == 50);
        }

        fn test7(ar: [u8; 20])
            requires ar[1] == 19
        {
            let x = ar[1];
            assert(x == 19);
        }

        fn test8(ar: [u8; 20]) {
            let y = ar[20]; // FAILS
        }

        struct S {
            ar: [usize; 4],
        }

        fn test9(s: &mut S) {
            let mut ar = s.ar;
            ar.set(0, 42);
            assert(ar[0] == 42);
        }

        fn test10() {
            let mut ar = [0, 0];
            assert(ar[0] == 0);
            ar.set(0, 42);
            assert(ar[0] == 42);
            assert(ar[1] == 0);
        }

    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_recursion_checks_1 verus_code! {
        use vstd::array::*;
        use vstd::map::*;

        struct Foo {
            field: [ Map<Foo, int> ; 20 ],
        }

    } => Err(err) => assert_vir_error_msg(err, "non-positive position")
}

test_verify_one_file! {
    #[test] test_recursion_checks_2 verus_code! {
        use vstd::array::*;

        struct Foo {
            field: Box<[ Foo ; 1 ]>,
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] test_array_literals verus_code! {
        use vstd::prelude::*;

        fn test1() {
            let x: [u8; 6] = [11, 12, 13, 14, 15, 16];
            assert(x.view().len() == 6);
            assert(x.view()[0] == 11);
            assert(x.view()[1] == 12);
            assert(x.view()[2] == 13);
            assert(x.view()[3] == 14);
            assert(x.view()[4] == 15);
            assert(x.view()[5] == 16);
        }

        fn test2<T>(a: T, b: T, c: T) {
            let x: [T; 3] = [a, b, c];
            assert(x.view().len() == 3);
            assert(x.view()[0] == a);
            assert(x.view()[1] == b);
            assert(x.view()[2] == c);
        }

        fn test3() {
            let x: [u8; 6] = [11, 12, 13, 14, 15, 16];
            assert(x.view().len() == 6);
            assert(x.view()[0] == 12); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_array_literals_lifetime verus_code! {
        fn test2<T>(a: T, b: T) {
            let x: [T; 3] = [a, b, b];
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `b`")
}

test_verify_one_file! {
    #[test] test_array_literals_spec_fn_unsupported_1 verus_code! {
        spec fn test() -> [u64; 3] {
            [3, 4, 5]
        }
    } => Err(err) => assert_vir_error_msg(err, "expected pure mathematical expression")
}

test_verify_one_file! {
    #[test] test_array_literals_spec_fn_unsupported_2 verus_code! {
        use vstd::array::*;
        exec fn test() {
            let ghost a = [3u64, 4, 5];
            assert(a[1] == 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_array_to_slice verus_code! {
        use vstd::prelude::*;

        fn test1(ar: &[u8; 3]) {
            let sl: &[u8] = ar;
            assert(sl@.len() == 3);
        }

        fn test2() {
            let ar = [4, 5, 6];
            let sl: &[u8] = &ar;
            assert(sl@.len() == 3);
            assert(sl@[1] == 5);
        }

        fn test3<const N: usize>(ar: &[u8; N]) {
            let sl: &[u8] = ar;
            assert(sl@.len() == N);
        }

        spec fn len_of_slice(ar: &[u8]) -> int {
            ar@.len() as int
        }

        fn test4<const N: usize>(ar: &[u8; N]) {
            assert(len_of_slice(ar) == ar@.len());
        }
    } => Ok(())
}
