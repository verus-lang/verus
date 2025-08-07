#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] test_basic ["new-mut-ref", "--no-lifetime"] => verus_code! {
        broadcast axiom fn resolved_defn<T>(a: &mut T)
            ensures
                #[trigger] has_resolved(a) ==> mut_ref_current(a) == mut_ref_future(a);

        fn test_no_update() {
            broadcast use resolved_defn;

            let mut u: u64 = 20;
            let u_ref: &mut u64 = &mut u;

            proof { resolve(u_ref) }

            assert(u == 20);
        }

        fn test_basic_update() {
            broadcast use resolved_defn;

            let mut u: u64 = 20;
            let u_ref: &mut u64 = &mut u;

            *u_ref = 30;

            proof { resolve(u_ref) }

            assert(u == 30);
        }

        struct Pair<A, B>(A, B);

        fn test_field_update() {
            broadcast use resolved_defn;

            let mut u: Pair<u64, u64> = Pair(20, 20);
            let u_ref: &mut Pair<u64, u64> = &mut u;

            u_ref.0 = 30;

            proof { resolve(u_ref) }

            assert(u.0 == 30);
            assert(u.1 == 20);
        }

        fn test_field_update2() {
            broadcast use resolved_defn;

            let mut u: Pair<u64, u64> = Pair(20, 20);
            let u_ref: &mut u64 = &mut u.0;

            *u_ref = 30;

            proof { resolve(u_ref) }

            assert(u.0 == 30);
            assert(u.1 == 20);
        }

        fn test_mut_ref_in_pair() {
            broadcast use resolved_defn;

            let mut u: u64 = 20;
            let u_ref: Pair<&mut u64, u64> = Pair(&mut u, 70);

            *u_ref.0 = 30;

            proof { resolve(u_ref.0) }

            assert(u == 30);
        }

        fn test_reborrow() {
            broadcast use resolved_defn;

            let mut u: u64 = 20;
            let u_ref: &mut u64 = &mut u;

            *u_ref = 11;

            let u_ref2 = &mut *u_ref;

            let x = *u_ref2;
            assert(x == 11);
            *u_ref2 = 13;

            proof { resolve(u_ref2); }

            let x = *u_ref;
            assert(x == 13);

            *u_ref = 17;

            proof { resolve(u_ref); }

            assert(u == 17);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_spec_functions_ok ["new-mut-ref", "--no-lifetime"] => verus_code! {
        spec fn test<T>(x: &mut T) -> T {
            mut_ref_current(x)
        }

        #[verifier::prophetic]
        spec fn test1<T>(x: &mut T) -> T {
            mut_ref_future(x)
        }

        #[verifier::prophetic]
        spec fn test2<T>(x: &mut T) -> bool {
            has_resolved(x)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_mut_ref_future_proph ["new-mut-ref", "--no-lifetime"] => verus_code! {
        spec fn test<T>(x: &mut T) -> T {
            mut_ref_future(x)
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use prophecy-dependent function `mut_ref_future` in prophecy-independent context")
}

test_verify_one_file_with_options! {
    #[test] test_resolved_proph ["new-mut-ref", "--no-lifetime"] => verus_code! {
        spec fn test<T>(x: &mut T) -> bool {
            has_resolved(x)
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use prophecy-dependent predicate `has_resolved` in prophecy-independent context")
}
