#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        use vstd::prelude::*;
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

        fn test4() {
            let a1: [u8; 3] = [10, 20, 30];
            let a2: [u8; 3] = [10, 20, 40];
            assert(a1 != a2);
            assert(a1@ != a2@);
            assert(a1@.contains(30));
            assert(a2@.contains(30)); // FAILS
        }

        proof fn test5() {
            let s1: Seq<int> = [10, 20, 30]@;
            let s2: Seq<int> = [10, 20, 40]@;
            assert(s1 != s2);
            assert(s1 == s2); // FAILS
        }

        proof fn test6() {
            let s: Seq<int> = [10, 20, 30]@;
            assert(s.contains(30));
            assert(s.contains(40)); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] test_array_literals_lifetime verus_code! {
        fn test2<T>(a: T, b: T) {
            let x: [T; 3] = [a, b, b];
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `b`")
}

test_verify_one_file! {
    #[test] test_array_literals_spec_fn_supported_1 verus_code! {
        spec fn test() -> [u64; 3] {
            [3, 4, 5]
        }
    } => Ok(())
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
    #[test] test_array_repeat verus_code! {
        use vstd::prelude::*;

        fn test1() {
            let x: [u8; 6] = [11; 6];
            assert(x.view().len() == 6);
            assert(x.view()[0] == 11);
            assert(x.view()[1] == 11);
            assert(x.view()[2] == 11);
            assert(x.view()[3] == 11);
            assert(x.view()[4] == 11);
            assert(x.view()[5] == 11);
        }

        fn test2<T: Copy>(a: T) {
            let x: [T; 3] = [a; 3];
            assert(x.view().len() == 3);
            assert(x.view()[0] == a);
            assert(x.view()[1] == a);
            assert(x.view()[2] == a);
        }

        fn test3<T: Copy, const N: usize>(a: T, i: usize) {
            let x: [T; N] = [a; N];
            assert(x.view().len() == N);

            assume(0 <= i < N);
            assert(x.view()[i as int] == a);
        }

        proof fn test4<T: Copy, const N: usize>(a: T, i: usize) {
            let x: [T; N] = [a; N];
            assert(x.view().len() == N);

            assume(0 <= i < N);
            assert(x.view()[i as int] == a);
        }

        fn test5() {
            let x: [u8; 6] = [11; 6];
            assert(x.view().len() == 7); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    // https://github.com/verus-lang/verus/issues/1236
    #[test] test_array_type_id verus_code! {
        use vstd::prelude::*;
        struct X;
        fn test2<'a>(p: &'a Option<[X; 75]>) -> (res: &'a [X; 75])
            requires
                p.is_some()
            ensures
                Some(*res) == p
        {
            p.as_ref().unwrap()
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_array_repeat_tracked verus_code! {
        tracked struct X { }

        proof fn array_repeat_tracked<const N: usize>(tracked x: X) {
            let tracked ar = [x; N];
        }
    } => Err(err) => assert_rust_error_msg(err, "the trait bound `X: std::marker::Copy` is not satisfied")
}

test_verify_one_file! {
    #[test] test_array_repeat_tracked_copy verus_code! {
        use vstd::*;
        proof fn array_repeat_tracked<T: Copy, const N: usize>(tracked x: T) {
            let tracked ar = [x; N];
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] test_array_repeat_non_copy_const verus_code! {
        use vstd::prelude::*;

        struct X { u: u8 }

        const fn some_x() -> X { X { u: 0 } }

        exec const C: X = some_x();

        fn stuff() {
            // This is currently unsupported, but if it were supported,
            // this would need to fail because X is not marked Copy.
            // (Imagine if X were a cell type or something like that, whose representation
            // is some ghost 'cell ID'. The cell ID would change every time the constant
            // is used.)
            let ar = [C; 13];
            assert(ar@[0] == ar@[1]); // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: array-fill expresion with non-copy type")
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

        fn test5<const N: usize>(ar: Box<[u8; N]>) {
            let sl: Box<[u8]> = ar;
            assert(sl@.len() == N);
        }

    } => Ok(())
}
