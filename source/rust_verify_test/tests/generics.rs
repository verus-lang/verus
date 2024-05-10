#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] const_generic verus_code! {
        #[verifier(external_body)]
        #[verifier::accept_recursive_types(A)]
        struct Array<A, const N: usize>([A; N]);

        #[verifier(external_body)]
        fn array_index<'a, A, const N: usize>(arr: &'a Array<A, N>, i: usize) -> &'a A {
            &arr.0[i]
        }

        impl<A, const N: usize> Array<A, N> {
            spec fn array_len(&self) -> usize { N }
        }

        spec fn f<const A: usize>() -> int { A as int }

        spec fn g<const A: usize>() -> int { f::<A>() }

        proof fn h() {
            let x = g::<7>();
            assert(x == 7);
        }

        proof fn h2() {
            let x = g::<7>();
            assert(x == 8); // FAILS
        }

        fn test_arr_len(arr: &Array<u8, 100>) {
            assert(arr.array_len() == 100);
        }

        fn test_arr_len2(arr: &Array<u8, 100>) {
            assert(arr.array_len() == 101); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] test_decorated_types verus_code! {
        spec fn sizeof<A>() -> nat;

        proof fn test() {
            assert(sizeof::<&u8>() == sizeof::<u8>()); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] const_generics_int_ranges verus_code! {
        proof fn test<const N : u8>() {
            assert (0 <= N);
            assert (N <= 255);
        }

        proof fn test2<const N : u8>() {
            assert (N < 255); // FAILS
        }

        proof fn test3<const N : usize>() {
            assert (0 <= N);
            assert (N <= usize::MAX);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] const_generics_broadcast verus_code! {
        pub open spec fn stuff(t: int) -> bool { true }

        // This incorrectly errors about missing triggers, but what we really want here is to
        // make sure is that the assert fails.

        #[verifier::external_body]
        pub broadcast proof fn broadcaster<const X: u8>()
            ensures #[trigger] stuff(X as int) ==> 0 <= X < 255
        {
        }

        fn moo(z: u16) {
            assert(stuff(z as int));
            assert(z < 255);
        }
    } => Err(err) => assert_vir_error_msg(err, "trigger does not cover variable X")
}
