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
