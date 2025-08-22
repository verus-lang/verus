#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] test_basic ["new-mut-ref"] => verus_code! {
        fn test_no_update() {
            let mut u: u64 = 20;
            let u_ref: &mut u64 = &mut u;

            proof { resolve(u_ref) }

            assert(u == 20);
        }

        fn test_basic_update() {
            let mut u: u64 = 20;
            let u_ref: &mut u64 = &mut u;

            *u_ref = 30;

            proof { resolve(u_ref) }

            assert(u == 30);
        }

        struct Pair<A, B>(A, B);

        fn test_field_update() {
            let mut u: Pair<u64, u64> = Pair(20, 20);
            let u_ref: &mut Pair<u64, u64> = &mut u;

            u_ref.0 = 30;

            proof { resolve(u_ref) }

            assert(u.0 == 30);
            assert(u.1 == 20);
        }

        fn test_field_update2() {
            let mut u: Pair<u64, u64> = Pair(20, 20);
            let u_ref: &mut u64 = &mut u.0;

            *u_ref = 30;

            proof { resolve(u_ref) }

            assert(u.0 == 30);
            assert(u.1 == 20);
        }

        fn test_mut_ref_in_pair() {
            let mut u: u64 = 20;
            let u_ref: Pair<&mut u64, u64> = Pair(&mut u, 70);

            *u_ref.0 = 30;

            proof {
                resolve(u_ref);
                assert(has_resolved(u_ref));
                assert(has_resolved(u_ref.0));
            }

            assert(u == 30);
        }

        fn test_reborrow() {
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
    #[test] test_spec_functions_ok ["new-mut-ref"] => verus_code! {
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
    #[test] test_mut_ref_future_proph ["new-mut-ref"] => verus_code! {
        spec fn test<T>(x: &mut T) -> T {
            mut_ref_future(x)
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use prophecy-dependent function `mut_ref_future` in prophecy-independent context")
}

test_verify_one_file_with_options! {
    #[test] test_resolved_proph ["new-mut-ref"] => verus_code! {
        spec fn test<T>(x: &mut T) -> bool {
            has_resolved(x)
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use prophecy-dependent predicate `has_resolved` in prophecy-independent context")
}

test_verify_one_file_with_options! {
    #[test] mut_ref_not_extensional ["new-mut-ref"] => verus_code! {
        // &mut T doesn't have extensionality because that would cause (==) to be
        // a prophetic operator

        fn test1(a: &mut u64, b: &mut u64) {
            assume(mut_ref_current(a) == mut_ref_current(b)
                && mut_ref_future(a) == mut_ref_future(b));
            assert(a == b); // FAILS
        }

        fn test2(a: &mut u64, b: &mut u64) {
            assume(mut_ref_current(a) == mut_ref_current(b)
                && mut_ref_future(a) == mut_ref_future(b));
            assert(a =~= b); // FAILS
        }

        fn test3(a: &mut u64, b: &mut u64) {
            assume(mut_ref_current(a) == mut_ref_current(b)
                && mut_ref_future(a) == mut_ref_future(b));
            assert(a =~~= b); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] test_resolved_axioms ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        proof fn test_pair<A, B>(pair: (A, B)) {
            assert(has_resolved(pair) ==> has_resolved(pair.0));
            assert(has_resolved(pair) ==> has_resolved(pair.1));
        }

        proof fn test_option<A>(opt: Option<A>) {
            match opt {
                Some(o) => {
                    assert(has_resolved(opt) ==> has_resolved(o));
                }
                None => { }
            }
        }

        struct Pair<A, B> {
            x: A,
            y: B,
        }

        proof fn test_pair_struct<A, B>(pair: Pair<A, B>) {
            assert(has_resolved(pair) ==> has_resolved(pair.x));
            assert(has_resolved(pair) ==> has_resolved(pair.y));
        }

        proof fn test_box<A>(b: Box<A>) {
            assert(has_resolved(b) ==> has_resolved(*b));
        }

        proof fn test_tracked<A>(t: Tracked<A>) {
            assert(has_resolved(t) ==> has_resolved(t@));
        }

        proof fn test_ghost_fail<A>(t: Ghost<A>) {
            assert(has_resolved(t) ==> has_resolved(t@)); // FAILS
        }

        proof fn test_ref_fail<A>(t: &A) {
            assert(has_resolved(t) ==> has_resolved(*t)); // FAILS
        }

        proof fn test_rc_fail<A>(t: std::rc::Rc<A>) {
            assert(has_resolved(t) ==> has_resolved(*t)); // FAILS
        }

        proof fn test_arc_fail<A>(t: std::sync::Arc<A>) {
            assert(has_resolved(t) ==> has_resolved(*t)); // FAILS
        }

        proof fn test_mut_ref<A>(t: &mut A) {
            assert(has_resolved(t) ==> mut_ref_current(t) == mut_ref_future(t));
        }

        proof fn test_mut_ref_fail<A>(t: &mut A) {
            assert(has_resolved(t) ==> has_resolved(mut_ref_current(t))); // FAILS
        }

        proof fn test_mut_ref_fail2<A>(t: &mut A) {
            assert(has_resolved(t) ==> has_resolved(mut_ref_future(t))); // FAILS
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] test_resolve_axioms_in_context ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn box_with_mut_ref() {
            let mut x: u64 = 0;

            let x_ref = &mut x;
            let x_ref_box = Box::new(x_ref);

            **x_ref_box = 13;

            proof { resolve(x_ref_box); }

            assert(x == 13);
        }

        fn shr_ref_with_mut_ref() {
            let mut x: u64 = 0;

            let x_ref = &mut x;
            let x_ref_ref = &x_ref;

            proof { resolve(x_ref_ref); }

            assert(has_resolved(x_ref)); // FAILS

            *x_ref = 20;
            proof { resolve(x_ref); }
        }

        fn mut_ref_with_mut_ref() {
            let mut x: u64 = 0;

            let mut x_ref = &mut x;
            let x_ref_ref = &mut x_ref;

            **x_ref_ref = 20;

            proof { resolve(x_ref_ref); }

            assert(has_resolved(x_ref)); // FAILS

            *x_ref = 30;
            proof { resolve(x_ref); }
        }
    } => Err(err) => assert_fails(err, 2)
}
