#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] test_basic ["new-mut-ref"] => verus_code! {
        fn test_no_update() {
            let mut u: u64 = 20;
            let u_ref: &mut u64 = &mut u;

            assert(u == 20);
        }

        fn test_basic_update() {
            let mut u: u64 = 20;
            let u_ref: &mut u64 = &mut u;

            *u_ref = 30;

            assert(u == 30);
        }

        struct Pair<A, B>(A, B);

        fn test_field_update() {
            let mut u: Pair<u64, u64> = Pair(20, 20);
            let u_ref: &mut Pair<u64, u64> = &mut u;

            u_ref.0 = 30;

            assert(u.0 == 30);
            assert(u.1 == 20);
        }

        fn test_field_update2() {
            let mut u: Pair<u64, u64> = Pair(20, 20);
            let u_ref: &mut u64 = &mut u.0;

            *u_ref = 30;

            assert(u.0 == 30);
            assert(u.1 == 20);
        }

        fn test_mut_ref_in_pair() {
            let mut u: u64 = 20;
            let u_ref: Pair<&mut u64, u64> = Pair { 0: &mut u, 1: 70 };

            *u_ref.0 = 30;

            proof {
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

            let x = *u_ref;
            assert(x == 13);

            *u_ref = 17;

            assert(u == 17);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_paren_ctors_with_mut_refs ["new-mut-ref"] => verus_code! {
        struct Pair<A, B>(A, B);

        fn test_mut_ref_in_pair() {
            let mut u: u64 = 20;
            let u_ref: Pair<&mut u64, u64> = Pair(&mut u, 70);

            *u_ref.0 = 30;

            proof {
                assert(has_resolved(u_ref.0));
            }

            assert(u == 30);
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

        #[verifier::prophetic]
        spec fn test3<T>(x: &mut T) -> T {
            *fin(x)
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
    #[test] test_fin_proph ["new-mut-ref"] => verus_code! {
        spec fn test<T>(x: &mut T) -> T {
            *fin(x)
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use prophecy-dependent function `fin` in prophecy-independent context")
}

test_verify_one_file_with_options! {
    #[test] test_resolved_proph ["new-mut-ref"] => verus_code! {
        spec fn test<T>(x: &mut T) -> bool {
            has_resolved(x)
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use prophecy-dependent predicate `has_resolved` in prophecy-independent context")
}

test_verify_one_file_with_options! {
    #[test] test_after_borrow_proph ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 0;
            let x_ref = &mut x;

            let ghost y = after_borrow(x);

            *x_ref = 20;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use prophecy-dependent function `after_borrow` in prophecy-independent context")
}

test_verify_one_file_with_options! {
    #[test] test_after_borrow_ok ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 0;
            let x_ref = &mut x;

            assert(*fin(x_ref) == after_borrow(x));

            *x_ref = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_after_borrow_bad_expr ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 0;
            let x_ref = &mut x;

            assert(after_borrow(true) == true);

            *x_ref = 20;
        }
    } => Err(err) => assert_vir_error_msg(err, "`after_borrow` expects a local variable, possibly with dereferences or field accesses")
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
            assert(match opt {
                Some(o) => {
                    has_resolved(opt) ==> has_resolved(o)
                }
                None => true,
            });
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

        fn resolve<T>(t: T)
            ensures has_resolved(t)
        { }

        fn box_with_mut_ref() {
            let mut x: u64 = 0;

            let x_ref = &mut x;
            let x_ref_box = Box::new(x_ref);

            **x_ref_box = 13;

            resolve(x_ref_box);

            // TODO(new_mut_ref): without this line, Verus doesn't emit the axiom for
            // has_resolved::<Box<_>>
            assert(has_resolved(x_ref_box));

            assert(x == 13);
        }

        fn shr_ref_with_mut_ref() {
            let mut x: u64 = 0;

            let x_ref = &mut x;
            let x_ref_ref = &x_ref;

            resolve(x_ref_ref);

            assert(has_resolved(x_ref)); // FAILS

            *x_ref = 20;
            resolve(x_ref);
        }

        fn mut_ref_with_mut_ref() {
            let mut x: u64 = 0;

            let mut x_ref = &mut x;
            let x_ref_ref = &mut x_ref;

            **x_ref_ref = 20;

            resolve(x_ref_ref);

            assert(has_resolved(x_ref)); // FAILS

            *x_ref = 30;
            resolve(x_ref);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] test_nested_mut_refs ["new-mut-ref"] => verus_code! {
        fn test_nested() {
            let mut x: u64 = 0;
            let mut y: u64 = 10;

            let mut x_ref = &mut x;
            *x_ref = 20;

            assert(x == 20);

            x_ref = &mut y;
            *x_ref = 30;

            assert(y == 30);
        }

        fn test_nested2() {
            let mut x: u64 = 0;
            let mut y: u64 = 1;
            let mut z: u64 = 2;
            let mut w: u64 = 3;
            let mut v: u64 = 4;

            let mut ref1 = &mut x;
            let mut ref11 = &mut ref1;
            **ref11 = 10;

            let mut ref2 = &mut y;
            let mut ref22 = &mut ref2;
            **ref22 = 20;

            let mut ref3 = &mut z;
            *ref11 = ref3;
            **ref11 = 30;

            let mut ref4 = &mut w;
            ref11 = &mut ref4;
            **ref11 = 40;

            **(&mut &mut v) = 50;

            assert(x == 10);
            assert(y == 20);
            assert(z == 30);
            assert(w == 40);
            assert(v == 50);
        }

        fn test_nested_fails() {
            let mut x: u64 = 0;
            let mut y: u64 = 10;

            let mut x_ref = &mut x;
            *x_ref = 20;

            assert(x == 20);

            x_ref = &mut y;
            *x_ref = 30;

            assert(y == 30);
            assert(false); // FAILS
        }

        fn test_nested2_fails() {
            let mut x: u64 = 0;
            let mut y: u64 = 1;
            let mut z: u64 = 2;
            let mut w: u64 = 3;
            let mut v: u64 = 4;

            let mut ref1 = &mut x;
            let mut ref11 = &mut ref1;
            **ref11 = 10;

            let mut ref2 = &mut y;
            let mut ref22 = &mut ref2;
            **ref22 = 20;

            let mut ref3 = &mut z;
            *ref11 = ref3;
            **ref11 = 30;

            let mut ref4 = &mut w;
            ref11 = &mut ref4;
            **ref11 = 40;

            **(&mut &mut v) = 50;

            assert(x == 10);
            assert(y == 20);
            assert(z == 30);
            assert(w == 40);
            assert(v == 50);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] test_structs_and_boxes ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        struct X<'a> {
            a: (u64, Box<(&'a mut u64, u64)>),
        }

        fn test() {
            let mut u: u64 = 0;

            let mut x = X {
                a: (0, Box::new((&mut u, 20))),
            };

            assert(has_resolved(x.a.1.0)); // TODO(new_mut_ref): should be automatic

            assert(u == 0);
        }

        fn test2() {
            let mut u: u64 = 0;

            let mut x = X {
                a: (0, Box::new((&mut u, 20))),
            };
            *x.a.1.0 = 30;

            assert(u == 30);
        }

        fn test3() {
            let mut u: u64 = 0;
            let mut v: u64 = 0;

            let mut x = X {
                a: (0, Box::new((&mut u, 20))),
            };
            *x.a.1.0 = 30;

            x.a.1 = Box::new((&mut v, 100));
            *x.a.1.0 = 90;

            assert(u == 30);
            assert(v == 90);
        }

        fn test4() {
            let mut u: u64 = 0;
            let mut v: u64 = 0;

            let mut x = X {
                a: (0, Box::new((&mut u, 20))),
            };
            *x.a.1.0 = 30;

            x.a.1.0 = &mut v;
            *x.a.1.0 = 90;

            assert(u == 30);
            assert(v == 90);
        }

        fn test_fails() {
            let mut u: u64 = 0;

            let mut x = X {
                a: (0, Box::new((&mut u, 20))),
            };

            assert(has_resolved(x.a.1.0)); // TODO(new_mut_ref): should be automatic

            assert(u == 0);
            assert(false); // FAILS
        }

        fn test2_fails() {
            let mut u: u64 = 0;

            let mut x = X {
                a: (0, Box::new((&mut u, 20))),
            };
            *x.a.1.0 = 30;

            assert(u == 30);
            assert(false); // FAILS
        }

        fn test3_fails() {
            let mut u: u64 = 0;
            let mut v: u64 = 0;

            let mut x = X {
                a: (0, Box::new((&mut u, 20))),
            };
            *x.a.1.0 = 30;

            x.a.1 = Box::new((&mut v, 100));
            *x.a.1.0 = 90;

            assert(u == 30);
            assert(v == 90);
            assert(false); // FAILS
        }

        fn test4_fails() {
            let mut u: u64 = 0;
            let mut v: u64 = 0;

            let mut x = X {
                a: (0, Box::new((&mut u, 20))),
            };
            *x.a.1.0 = 30;

            x.a.1.0 = &mut v;
            *x.a.1.0 = 90;

            assert(u == 30);
            assert(v == 90);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] test_structs_and_boxes_double_nested ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        struct X<'a, 'b> {
            a: (u64, Box<(&'a mut (u64, &'b mut (u64, u64)), u64)>),
        }

        fn test() {
            let mut pair: (u64, u64) = (0, 1);
            let mut pair_ref_pair = (3, &mut pair);
            let mut x = X {
                a: (0, Box::new((&mut pair_ref_pair, 4))),
            };
            assert(has_resolved(x.a.1.0)); // TODO(new_mut_ref): should be automatic
            assert(has_resolved(pair_ref_pair.1));
            assert(pair === (0, 1));
        }

        fn test2() {
            let mut pair: (u64, u64) = (0, 1);
            let mut pair_ref_pair = (3, &mut pair);
            let mut x = X {
                a: (0, Box::new((&mut pair_ref_pair, 4))),
            };
            x.a.1.0.1.1 = 19;
            assert(has_resolved(x.a.1.0));
            assert(has_resolved(pair_ref_pair.1));
            assert(pair === (0, 19));
        }

        fn test3() {
            let mut pair: (u64, u64) = (0, 1);
            let mut pair_ref_pair = (3, &mut pair);

            let mut pair2: (u64, u64) = (2, 3);
            let mut pair2_ref_pair = (3, &mut pair2);

            let mut x = X {
                a: (0, Box::new((&mut pair_ref_pair, 4))),
            };

            x.a = (17, Box::new((&mut pair2_ref_pair, 5)));
            x.a.1.0.1.1 = 19;

            assert(has_resolved(x.a.1.0));
            assert(has_resolved(pair_ref_pair.1));
            assert(has_resolved(pair2_ref_pair.1));

            assert(pair === (0, 1));
            assert(pair2 === (2, 19));
        }

        fn test4() {
            let mut pair: (u64, u64) = (0, 1);
            let mut pair_ref_pair = (3, &mut pair);

            let mut pair2: (u64, u64) = (2, 3);
            let mut pair2_ref_pair = (3, &mut pair2);

            let mut x = X {
                a: (0, Box::new((&mut pair_ref_pair, 4))),
            };

            x.a = (17, Box::new((&mut pair2_ref_pair, 5)));
            x.a.1.0.0 = 19;

            assert(has_resolved(x.a.1.0));
            assert(has_resolved(pair_ref_pair.1));
            assert(has_resolved(pair2_ref_pair.1));

            assert(pair === (0, 1));
            assert(pair2 === (2, 3));
            assert(pair_ref_pair.0 === 3);
            assert(pair2_ref_pair.0 === 19);
        }

        fn test5() {
            let mut pair: (u64, u64) = (0, 1);
            let mut pair_ref_pair = (3, &mut pair);

            let mut pair2: (u64, u64) = (2, 3);
            let mut pair2_ref_pair = (3, &mut pair2);

            pair_ref_pair.1.0 = 23;
            pair2_ref_pair.1.0 = 24;

            let mut x = X {
                a: (0, Box::new((&mut pair_ref_pair, 4))),
            };

            x.a = (17, Box::new((&mut pair2_ref_pair, 5)));
            x.a.1.0.0 = 19;

            assert(has_resolved(x.a.1.0));
            assert(has_resolved(pair_ref_pair.1));
            assert(has_resolved(pair2_ref_pair.1));

            assert(pair === (23, 1));
            assert(pair2 === (24, 3));
            assert(pair_ref_pair.0 === 3);
            assert(pair2_ref_pair.0 === 19);
        }

        fn test_fails() {
            let mut pair: (u64, u64) = (0, 1);
            let mut pair_ref_pair = (3, &mut pair);
            let mut x = X {
                a: (0, Box::new((&mut pair_ref_pair, 4))),
            };
            assert(has_resolved(x.a.1.0)); // TODO(new_mut_ref): should be automatic
            assert(has_resolved(pair_ref_pair.1));
            assert(pair === (0, 1));
            assert(false); // FAILS
        }

        fn test2_fails() {
            let mut pair: (u64, u64) = (0, 1);
            let mut pair_ref_pair = (3, &mut pair);
            let mut x = X {
                a: (0, Box::new((&mut pair_ref_pair, 4))),
            };
            x.a.1.0.1.1 = 19;
            assert(has_resolved(x.a.1.0));
            assert(has_resolved(pair_ref_pair.1));
            assert(pair === (0, 19));
            assert(false); // FAILS
        }

        fn test3_fails() {
            let mut pair: (u64, u64) = (0, 1);
            let mut pair_ref_pair = (3, &mut pair);

            let mut pair2: (u64, u64) = (2, 3);
            let mut pair2_ref_pair = (3, &mut pair2);

            let mut x = X {
                a: (0, Box::new((&mut pair_ref_pair, 4))),
            };

            x.a = (17, Box::new((&mut pair2_ref_pair, 5)));
            x.a.1.0.1.1 = 19;

            assert(has_resolved(x.a.1.0));
            assert(has_resolved(pair_ref_pair.1));
            assert(has_resolved(pair2_ref_pair.1));

            assert(pair === (0, 1));
            assert(pair2 === (2, 19));
            assert(false); // FAILS
        }

        fn test4_fails() {
            let mut pair: (u64, u64) = (0, 1);
            let mut pair_ref_pair = (3, &mut pair);

            let mut pair2: (u64, u64) = (2, 3);
            let mut pair2_ref_pair = (3, &mut pair2);

            let mut x = X {
                a: (0, Box::new((&mut pair_ref_pair, 4))),
            };

            x.a = (17, Box::new((&mut pair2_ref_pair, 5)));
            x.a.1.0.0 = 19;

            assert(has_resolved(x.a.1.0));
            assert(has_resolved(pair_ref_pair.1));
            assert(has_resolved(pair2_ref_pair.1));

            assert(pair === (0, 1));
            assert(pair2 === (2, 3));
            assert(pair_ref_pair.0 === 3);
            assert(pair2_ref_pair.0 === 19);
            assert(false); // FAILS
        }

        fn test5_fails() {
            let mut pair: (u64, u64) = (0, 1);
            let mut pair_ref_pair = (3, &mut pair);

            let mut pair2: (u64, u64) = (2, 3);
            let mut pair2_ref_pair = (3, &mut pair2);

            pair_ref_pair.1.0 = 23;
            pair2_ref_pair.1.0 = 24;

            let mut x = X {
                a: (0, Box::new((&mut pair_ref_pair, 4))),
            };

            x.a = (17, Box::new((&mut pair2_ref_pair, 5)));
            x.a.1.0.0 = 19;

            assert(has_resolved(x.a.1.0));
            assert(has_resolved(pair_ref_pair.1));
            assert(has_resolved(pair2_ref_pair.1));

            assert(pair === (23, 1));
            assert(pair2 === (24, 3));
            assert(pair_ref_pair.0 === 3);
            assert(pair2_ref_pair.0 === 19);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] control_flow_conditional ["new-mut-ref"] => verus_code! {
        fn test(b: bool) {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            if b {
                *x_ref = 20;
            } else {
                *x_ref = 30;
            }

            assert(x === (if b { 20 } else { 30 }));
        }

        fn test_fails(b: bool) {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            if b {
                *x_ref = 20;
            } else {
                *x_ref = 30;
            }

            assert(false); // FAILS
        }

        fn test2(b: bool) {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            if b {
                *x_ref = 20;
            } else {
                assert(has_resolved(x_ref)); // FAILS
            }

            *x_ref = 30;
        }

        fn test3(b: bool) {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            if b {
                *x_ref = 20;
                assert(has_resolved(x_ref)); // FAILS
            } else {
            }

            *x_ref = 30;
        }

        fn test4(b: bool) {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            if b {
                *x_ref = 20;
                assert(has_resolved(x_ref));
            } else {
                assert(has_resolved(x_ref));
            }
        }

        fn test5(b: bool) {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            if b {
                assert(has_resolved(x_ref)); // FAILS
                *x_ref = 20;
            } else {
            }
        }

        fn test6(b: bool) {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            if b {
            } else {
                assert(has_resolved(x_ref)); // FAILS
                *x_ref = 20;
            }
        }

        fn test7(b: bool) {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            if b {
                assert(has_resolved(x_ref));
                return;
            } else {
            }

            *x_ref = 20;
        }

        fn test8(b: bool) {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            if b {
                return;
            } else {
                assert(has_resolved(x_ref)); // FAILS
            }

            *x_ref = 20;
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] control_flow_conditional_2 ["new-mut-ref"] => verus_code! {
        fn test(b: bool) {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            assert(has_resolved(x_ref)); // FAILS

            if b {
                *x_ref = 20;
            } else {
            }
        }

        fn test2(b: bool) {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            assert(has_resolved(x_ref)); // FAILS

            if b {
            } else {
                *x_ref = 20;
            }
        }

        fn test3(b: bool) {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            assert(has_resolved(x_ref)); // FAILS

            if b {
            } else {
            }

            *x_ref = 20;
        }

        fn test4(b: bool) {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            assert(has_resolved(x_ref));

            if b {
            } else {
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] control_flow_conditional_with_pair ["new-mut-ref"] => verus_code! {
        fn test(b: bool) {
            let mut x: u64 = 0;
            let mut y: u64 = 0;
            let mut x_ref = (&mut x, &mut y);

            if b {
                *x_ref.0 = 20;
            } else {
                *x_ref.1 = 30;
            }

            assert(x === (if b { 20 } else { 0 }));
            assert(y === (if b { 0 } else { 30 }));
        }

        fn test_fails(b: bool) {
            let mut x: u64 = 0;
            let mut y: u64 = 0;
            let mut x_ref = (&mut x, &mut y);

            if b {
                assert(has_resolved(x_ref.1));
                *x_ref.0 = 20;
                assert(has_resolved(x_ref.0));
            } else {
                assert(has_resolved(x_ref.0));
                *x_ref.1 = 30;
                assert(has_resolved(x_ref.1));
            }

            assert(x === (if b { 20 } else { 0 }));
            assert(y === (if b { 0 } else { 30 }));
            assert(b); // FAILS
        }

        fn test_fails2(b: bool) {
            let mut x: u64 = 0;
            let mut y: u64 = 0;
            let mut x_ref = (&mut x, &mut y);

            if b {
                assert(has_resolved(x_ref.1));
                *x_ref.0 = 20;
                assert(has_resolved(x_ref.0));
            } else {
                assert(has_resolved(x_ref.0));
                *x_ref.1 = 30;
                assert(has_resolved(x_ref.1));
            }

            assert(x === (if b { 20 } else { 0 }));
            assert(y === (if b { 0 } else { 30 }));
            assert(!b); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] control_flow_bin_ops_short_circuiting ["new-mut-ref"] => verus_code! {
        fn test_and_1(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            // this succeeds because `x_ref = &mut y` is reached before `*x_ref = 30`
            assert(has_resolved(x_ref));

            if ({ x_ref = &mut y; arg1 == 0 }) && arg2 == 0 {
            }

            *x_ref = 30;
        }

        fn test_and_2(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            // this fails because `x_ref = &mut y` might not be reached
            assert(has_resolved(x_ref)); // FAILS

            if arg1 == 0 && ({ x_ref = &mut y; arg2 == 0 }) {
            }

            *x_ref = 30;
        }

        fn test_and_3(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            assert(has_resolved(x_ref)); // FAILS

            if arg1 == 0 && ({ *x_ref = 30; arg2 == 0 }) {
            }
        }

        fn test_or_1(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            // this succeeds because `x_ref = &mut y` is reached before `*x_ref = 30`
            assert(has_resolved(x_ref));

            if ({ x_ref = &mut y; arg1 == 0 }) || arg2 == 0 {
            }

            *x_ref = 30;
        }

        fn test_or_2(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            // this fails because `x_ref = &mut y` might not be reached
            assert(has_resolved(x_ref)); // FAILS

            if arg1 == 0 || ({ x_ref = &mut y; arg2 == 0 }) {
            }

            *x_ref = 30;
        }

        fn test_or_3(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            assert(has_resolved(x_ref)); // FAILS

            if arg1 == 0 || ({ *x_ref = 30; arg2 == 0 }) {
            }
        }

        fn test_ineq_1(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            // this succeeds because `x_ref = &mut y` is reached before `*x_ref = 30`
            assert(has_resolved(x_ref));

            if ({ x_ref = &mut y; arg1 }) < arg2 {
            }

            *x_ref = 30;
        }

        fn test_ineq_2(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            // succeeds becasue < has no short-circuiting
            assert(has_resolved(x_ref));

            if arg1 < ({ x_ref = &mut y; arg2 }) {
            }

            *x_ref = 30;
        }

        fn test_ineq_3(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            assert(has_resolved(x_ref)); // FAILS

            if arg1 < ({ *x_ref = 30; arg2 }) {
            }
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] control_flow_bin_ops_short_circuiting2 ["new-mut-ref"] => verus_code! {
        fn test_and_1(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            if ({ x_ref = &mut y; arg1 == 0 }) && arg2 == 0 {
            }

            *x_ref = 30;

            assert(x == 0);
            assert(y == 30);
        }

        fn test_and_2(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            if arg1 == 0 && ({ x_ref = &mut y; arg2 == 0 }) {
            }

            *x_ref = 30;

            assert(arg1 == 0 ==> x == 0);
            assert(arg1 == 0 ==> y == 30);

            assert(arg1 != 0 ==> x == 30);
            assert(arg1 != 0 ==> y == 0);
        }

        fn test_and_3(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            if arg1 == 0 && ({ *x_ref = 30; arg2 == 0 }) {
            }

            assert(arg1 == 0 ==> x == 30);
            assert(arg1 == 0 ==> y == 0);

            assert(arg1 != 0 ==> x == 0);
            assert(arg1 != 0 ==> y == 0);
        }

        fn test_and_1_fails(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            if ({ x_ref = &mut y; arg1 == 0 }) && arg2 == 0 {
            }

            *x_ref = 30;

            assert(x == 0);
            assert(y == 30);
            assert(arg1 == 0); // FAILS
        }

        fn test_and_2_fails(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            if arg1 == 0 && ({ x_ref = &mut y; arg2 == 0 }) {
            }

            *x_ref = 30;

            assert(arg1 == 0 ==> x == 0);
            assert(arg1 == 0 ==> y == 30);

            assert(arg1 != 0 ==> x == 30);
            assert(arg1 != 0 ==> y == 0);

            assert(arg1 == 0); // FAILS
        }

        fn test_and_3_fails(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            if arg1 == 0 && ({ *x_ref = 30; arg2 == 0 }) {
            }

            assert(arg1 == 0 ==> x == 30);
            assert(arg1 == 0 ==> y == 0);

            assert(arg1 != 0 ==> x == 0);
            assert(arg1 != 0 ==> y == 0);

            assert(arg1 == 0); // FAILS
        }

        fn test_and_1_fails2(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            if ({ x_ref = &mut y; arg1 == 0 }) && arg2 == 0 {
            }

            *x_ref = 30;

            assert(x == 0);
            assert(y == 30);
            assert(arg1 != 0); // FAILS
        }

        fn test_and_2_fails2(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            if arg1 == 0 && ({ x_ref = &mut y; arg2 == 0 }) {
            }

            *x_ref = 30;

            assert(arg1 == 0 ==> x == 0);
            assert(arg1 == 0 ==> y == 30);

            assert(arg1 != 0 ==> x == 30);
            assert(arg1 != 0 ==> y == 0);

            assert(arg1 != 0); // FAILS
        }

        fn test_and_3_fails2(arg1: u64, arg2: u64) {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            if arg1 == 0 && ({ *x_ref = 30; arg2 == 0 }) {
            }

            assert(arg1 == 0 ==> x == 30);
            assert(arg1 == 0 ==> y == 0);

            assert(arg1 != 0 ==> x == 0);
            assert(arg1 != 0 ==> y == 0);

            assert(arg1 != 0); // FAILS
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] uninitialized ["new-mut-ref"] => verus_code! {
        fn test_uninit(b: bool) {
            let mut x = 0;
            let x_ref: &mut u64;

            if b {
                x_ref = &mut x;
                assert(has_resolved(x_ref));
            }
        }

        fn test_uninit_fails(b: bool) {
            let mut x = 0;
            let x_ref: &mut u64;

            assert(has_resolved(x_ref)); // FAILS

            if b {
                x_ref = &mut x;
            }
        }

        fn test_uninit_fails2(b: bool) {
            let mut x = 0;
            let x_ref: &mut u64;

            if b {
                x_ref = &mut x;
            }

            assert(has_resolved(x_ref)); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] control_flow_never ["new-mut-ref"] => verus_code! {
        fn some_bool() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn did_he_ever_return_no_he_never_returned() -> ! {
            loop { }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test() {
            let mut x = 0;
            let x_ref = &mut x;

            if some_bool() {
                *x_ref = 40;
            } else {
                *x_ref = 30;
                assert(has_resolved(x_ref));
                loop { }
            }

            *x_ref = 20;
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test2() {
            let mut x = 0;
            let x_ref = &mut x;

            if some_bool() {
                *x_ref = 40;
                assert(has_resolved(x_ref)); // FAILS
            } else {
                *x_ref = 30;
                loop { }
            }

            *x_ref = 20;
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test3() {
            let mut x = 0;
            let x_ref = &mut x;

            if some_bool() {
                *x_ref = 40;
            } else {
                *x_ref = 30;
                assert(has_resolved(x_ref));
                did_he_ever_return_no_he_never_returned()
            }

            *x_ref = 20;
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn test4() {
            let mut x = 0;
            let x_ref = &mut x;

            if some_bool() {
                *x_ref = 40;
                assert(has_resolved(x_ref)); // FAILS
            } else {
                *x_ref = 30;
                did_he_ever_return_no_he_never_returned()
            }

            *x_ref = 20;
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] let_decl_partial_move ["new-mut-ref"] => verus_code! {
        struct X<'a, 'b, 'c, 'd> {
            f1: (&'a mut u64, &'b mut u64),
            f2: (&'c mut u64, &'d mut u64),
        }

        fn test() {
            let mut a = 0;
            let mut b = 0;
            let mut c = 0;
            let mut d = 0;

            let x = X { f1: (&mut a, &mut b), f2: (&mut c, &mut d) };

            let X { f1: (z, _), f2: (_, w) } = x;

            *z = 13;
            *w = 14;

            *x.f1.1 = 15;
            *x.f2.0 = 16;

            assert(a == 13);
            assert(b == 15);
            assert(c == 16);
            assert(d == 14);
        }

        fn test_fails() {
            let mut a = 0;
            let mut b = 0;
            let mut c = 0;
            let mut d = 0;

            let x = X { f1: (&mut a, &mut b), f2: (&mut c, &mut d) };

            let X { f1: (z, _), f2: (_, w) } = x;

            assert(has_resolved(x.f1.0)); // FAILS

            *z = 20;
        }

        fn test2() {
            let mut a = 0;
            let mut b = 0;
            let mut c = 0;
            let mut d = 0;

            let x = X { f1: (&mut a, &mut b), f2: (&mut c, &mut d) };

            let (z, _) = x.f1;

            *z = 13;

            *x.f1.1 = 15;
            *x.f2.0 = 16;
            *x.f2.1 = 17;

            assert(a == 13);
            assert(b == 15);
            assert(c == 16);
            assert(d == 17);
        }

        fn test2_fails() {
            let mut a = 0;
            let mut b = 0;
            let mut c = 0;
            let mut d = 0;

            let x = X { f1: (&mut a, &mut b), f2: (&mut c, &mut d) };

            let (z, _) = x.f1;

            assert(has_resolved(x.f1.0)); // FAILS

            *z = 20;
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] place_behind_mut_ref_doesnt_resolve ["new-mut-ref"] => verus_code! {
        fn test1() {
            let mut x: u64 = 0;

            let mut x_ref: &mut u64 = &mut x;
            let mut x_ref_ref: &mut &mut u64 = &mut x_ref;

            **x_ref_ref = 30;

            // x_ref_ref resolves here, but not *x_ref_ref

            let mut x_ref_ref2: &mut &mut u64 = &mut x_ref;
            **x_ref_ref2 = 40;

            assert(x == 40);
        }

        fn test2() {
            let mut x: u64 = 0;

            let mut x_ref: &mut u64 = &mut x;
            let mut x_ref_ref: &mut &mut u64 = &mut x_ref;

            **x_ref_ref = 30;

            let mut x_ref_ref2: &mut &mut u64 = &mut x_ref;
            **x_ref_ref2 = 40;

            assert(x == 40);
            assert(false); // FAILS
        }

        fn test3() {
            let mut x: u64 = 0;

            let mut x_ref: &mut u64 = &mut x;
            let mut x_ref_ref: &mut &mut u64 = &mut x_ref;

            **x_ref_ref = 30;

            let mut x_ref_ref2: &mut &mut u64 = &mut x_ref;
            **x_ref_ref2 = 40;

            assert(x == 40);
            assert(has_resolved(mut_ref_current(x_ref_ref))); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] temporaries_with_semantically_trivial_ops ["new-mut-ref"] => verus_code! {
        use std::sync::Arc;
        use std::rc::Rc;
        use vstd::prelude::*;

        // the goal of this test is to make sure these are all properly temporaries
        // and that we aren't modifying the original local variable
        fn test_temp_shared_ref() {
            let mut x: u64 = 0;

            let y: u64 = 1;
            *(&mut &x) = &y;

            assert(x == 1); // FAILS
        }

        fn test_temp_box() {
            let mut x: u64 = 0;

            *(&mut Box::new(x)) = Box::new(1);

            assert(x == 1); // FAILS
        }

        fn test_temp_rc() {
            let mut x: u64 = 0;

            *(&mut Rc::new(x)) = Rc::new(1);

            assert(x == 1); // FAILS
        }

        fn test_temp_arc() {
            let mut x: u64 = 0;

            *(&mut Arc::new(x)) = Arc::new(1);

            assert(x == 1); // FAILS
        }

        #[verifier::external_body]
        fn arbitrary_const_ptr() -> *const u64 {
            unimplemented!()
        }

        #[verifier::external_body]
        fn arbitrary_mut_ptr() -> *mut u64 {
            unimplemented!()
        }

        fn test_ptr_conversion_const_to_mut() {
            let p1 = arbitrary_mut_ptr();
            let p2 = arbitrary_const_ptr();

            let mut x: *mut u64 = p1;

            *(&mut (x as *const u64)) = p2;

            assert(x == p2); // FAILS
        }

        fn test_ptr_conversion_mut_to_const() {
            let p1 = arbitrary_mut_ptr();
            let p2 = arbitrary_const_ptr();

            let mut x: *const u64 = p2;

            *(&mut (x as *mut u64)) = p1;

            assert(x == p1); // FAILS
        }

        fn test_int_casting() {
            let mut x: u32 = 0;

            *(&mut (x as u64)) = 1;

            assert(x == 1); // FAILS
        }

        fn test_int_casting_trunc() {
            let mut x: u64 = 0;

            *(&mut (x as u32)) = 1;

            assert(x == 1); // FAILS
        }
    } => Err(err) => assert_fails(err, 8)
}

test_verify_one_file_with_options! {
    #[test] test_params ["new-mut-ref"] => verus_code! {
        fn test1(x: &mut u64)
            ensures mut_ref_current(x) == mut_ref_future(x)
        {
        }

        fn test2(x: &mut u64)
            ensures mut_ref_future(x) == 20
        {
            *x = 20;
        }

        fn test2_fails(x: &mut u64)
            ensures false
        {
            *x = 20;
            return; // FAILS
        }

        fn test3_fails(x: &mut u64)
            ensures mut_ref_future(x) == 20
        {
            assert(has_resolved(x)); // FAILS
            *x = 20;
        }

        fn test3_fails2(x: &mut u64)
            ensures false,
        {
            *x = 20;
            return; // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] test_params_with_reborrow ["new-mut-ref"] => verus_code! {
        fn test4_1(x: &mut (u64, u64)) -> (ret: &mut u64)
            ensures ({
                mut_ref_future(x).1 == mut_ref_current(x).1 &&
                mut_ref_current(x).0 == mut_ref_current(ret) &&
                mut_ref_future(x).0 == mut_ref_future(ret)
            })
        {
            &mut x.0
        }

        fn test4(x: &mut (u64, u64)) -> (ret: &mut u64)
            ensures ({
                mut_ref_future(x).1 == mut_ref_current(x).1 &&
                mut_ref_current(x).0 == mut_ref_current(ret) &&
                mut_ref_future(x).0 == mut_ref_future(ret)
            })
        {
            let r = &mut x.0;
            return r;
        }

        fn test4_fails(x: &mut (u64, u64)) -> (ret: &mut u64)
            ensures false,
        {
            let ret = &mut x.0;
            return ret; // FAILS
        }

        fn test4_fails2(x: &mut (u64, u64)) -> (ret: &mut u64)
        {
            let ret = &mut x.0;
            assert(has_resolved(ret)); // FAILS
            ret
        }

        fn test4_fails3(x: &mut (u64, u64)) -> (ret: &mut u64)
        {
            let ret = &mut x.0;
            assert(has_resolved(ret)); // FAILS
            return ret;
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] test_param_nested ["new-mut-ref"] => verus_code! {
        fn test(x: &mut &mut u64) {
            assert(has_resolved(x));
        }

        fn test_fails(x: &mut &mut u64) {
            assert(has_resolved(mut_ref_current(x))); // FAILS
        }

        fn test2<'a, 'b>(x: &'b mut &'a mut u64, y: &'a mut u64) {
            assert(has_resolved(mut_ref_current(x)));
            *x = y;
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] test_param_nested_with_return_stmt ["new-mut-ref"] => verus_code! {
        fn some_bool() -> bool { true }

        fn test(x: &mut &mut u64) {
            if some_bool() {
                assert(has_resolved(x));
                return;
            }
        }

        fn test_fails(x: &mut &mut u64) {
            if some_bool() {
                assert(has_resolved(mut_ref_current(x))); // FAILS
                return;
            }
        }

        fn test2<'a, 'b>(x: &'b mut &'a mut u64, y: &'a mut u64) {
            if some_bool() {
                assert(has_resolved(mut_ref_current(x)));
                *x = y;
                return;
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] auto_coerce_to_shr_borrow ["new-mut-ref"] => verus_code! {
        fn foo(x: &u64) { }

        fn test_shr() {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(x == 20);

            let x_ref_shr: &u64 = x_ref;
            assert(x_ref_shr == 20);

            foo(x_ref_shr);
        }

        fn test_shr2() {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(x == 20);

            foo(x_ref);
        }

        fn test_shr_fails() {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(x == 20);

            let x_ref_shr: &u64 = x_ref;
            assert(x_ref_shr == 20);

            foo(x_ref_shr);
            assert(false); // FAILS
        }

        fn test_shr2_fails() {
            let mut x: u64 = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(x == 20);

            foo(x_ref);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] test_moves_via_let_decl ["new-mut-ref"] => verus_code! {
        fn test(b: bool) {
            let mut x: u64 = 0;
            let mut y: u64 = 0;
            let mut refs = (&mut x, &mut y);

            assert(has_resolved(refs.0) || has_resolved(refs.1) || has_resolved(refs)); // FAILS

            let mut refs2 = refs;

            *refs2.0 = 30;
        }

        fn test2(b: bool) {
            let mut x: u64 = 0;
            let mut y: u64 = 0;
            let mut refs = (&mut x, &mut y);

            assert(has_resolved(refs.0) || has_resolved(refs.1) || has_resolved(refs)); // FAILS

            let mut refs2 = refs;
        }

        fn test3(b: bool) {
            let mut x: u64 = 0;
            let mut y: u64 = 0;
            let mut refs = (&mut x, &mut y);

            assert(has_resolved(refs.0)); // FAILS

            let mut ref_x = refs.0;
            *ref_x = 30;
        }

        fn test4(b: bool) {
            let mut x: u64 = 0;
            let mut y: u64 = 0;
            let mut refs = (&mut x, &mut y);

            assert(has_resolved(refs.0)); // FAILS

            let mut ref_x = refs.0;
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] test_moves_via_fn_arg ["new-mut-ref"] => verus_code! {
        fn id<A>(a: A) -> A { a }

        fn test(b: bool) {
            let mut x: u64 = 0;
            let mut y: u64 = 0;
            let mut refs = (&mut x, &mut y);

            assert(has_resolved(refs.0) || has_resolved(refs.1) || has_resolved(refs)); // FAILS

            let mut refs2 = id(refs);

            *refs2.0 = 30;
        }

        fn test2(b: bool) {
            let mut x: u64 = 0;
            let mut y: u64 = 0;
            let mut refs = (&mut x, &mut y);

            assert(has_resolved(refs.0) || has_resolved(refs.1) || has_resolved(refs)); // FAILS

            let mut refs2 = id(refs);
        }

        fn test3(b: bool) {
            let mut x: u64 = 0;
            let mut y: u64 = 0;
            let mut refs = (&mut x, &mut y);

            assert(has_resolved(refs.0)); // FAILS

            let mut ref_x = id(refs.0);
            *ref_x = 30;
        }

        fn test4(b: bool) {
            let mut x: u64 = 0;
            let mut y: u64 = 0;
            let mut refs = (&mut x, &mut y);

            assert(has_resolved(refs.0)); // FAILS

            let mut ref_x = id(refs.0);
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] copy_from_behind_mut_ref_doesnt_leave_anything_uninitialized ["new-mut-ref"] => verus_code! {
        fn id<A>(a: A) -> A { a }

        fn test() {
            let mut x: u64 = 0;
            let mut x_ref: &mut u64 = &mut x;

            *x_ref = 20;

            let z = *x_ref;

            assert(has_resolved(x_ref));
        }

        fn test2() {
            let mut x: u64 = 0;
            let mut x_ref: &mut u64 = &mut x;

            *x_ref = 20;

            let z = id(*x_ref);

            assert(has_resolved(x_ref));
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] two_phase_borrow_resolving ["new-mut-ref"] => verus_code! {
        struct X<'a> {
            x: u64,
            y: &'a mut u64,
        }

        impl<'a> X<'a> {
            fn method_call_takes_mut_ref(&mut self, x: u64)
                ensures mut_ref_future(self).x == 20,
                no_unwind
            {
                self.x = 20;
            }
        }

        fn call_takes_mut_ref<T>(a: &mut T, x: u64)
            no_unwind
        {
        }

        fn call_takes_generic<T>(a: T, x: u64)
            no_unwind
        {
        }

        // When a call takes a two-phase borrow, the mutable reference doesn't get mutated
        // until *after* all arguments have been evaluated. Thus, for a two-phase borrow,
        // we won't see resolution immediately, but for a 'normal' borrow, we should resolution
        // immediately.

        fn test1() {
            let mut a = 24;
            let mut a_ref = &mut a;

            // two-phase-borrow (implicit reborrows are two-phase borrows)
            call_takes_mut_ref(a_ref, {
                *a_ref
            });

            assert(has_resolved(a_ref));
        }

        fn test1_fails() {
            let mut a = 24;
            let mut a_ref = &mut a;

            // two-phase-borrow (implicit reborrows are two-phase borrows)
            call_takes_mut_ref(a_ref, {
                assert(has_resolved(a_ref)); // FAILS
                *a_ref
            });
        }



        fn test2() {
            let mut a = 24;
            let mut a_ref = &mut a;

            call_takes_mut_ref(&mut *a_ref, 0);

            assert(has_resolved(a_ref));
        }

        fn test2_fails() {
            let mut a = 24;
            let mut a_ref = &mut a;

            // an explicit borrow is always a normal borrow, but Rust inserts an additional two-phase
            // borrow through adjustments. So what we have here is:
            //   &mut(two phase) * &mut(normal) * a_ref
            // Verus cleans this up to just:
            //   &mut(two phase) * a_ref
            // thus treats it as a two-phase borrow, which is why the has_resolved fails here.
            // However, Rust wouldn't let you read from *a_ref until the call is done (because of
            // the "normal" reborrow)
            call_takes_mut_ref(&mut *a_ref, {
                assert(has_resolved(a_ref)); // FAILS
                0
            });
        }

        fn test3() {
            let mut a = 24;
            let mut a_ref = &mut a;

            // When instantiating a generic with &mut T, there is no reborrow at all,
            // so a_ref should never be resolved
            call_takes_generic(a_ref, 0);

            assert(has_resolved(a_ref)); // FAILS
        }

        fn test4(x: X) {
            let mut thevar = x;

            // two-phase-borrow (implicit borrow for a receiver is two-phase)
            thevar.method_call_takes_mut_ref(thevar.x);

            assert(has_resolved(thevar));
        }

        fn test4_fails(x: X) {
            let mut a = x;

            // two-phase-borrow (implicit borrow for a receiver is two-phase)
            a.method_call_takes_mut_ref({
                assert(has_resolved(a)); // FAILS
                a.x
            });
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] two_phase_borrow_basic ["new-mut-ref"] => verus_code! {
        fn call_takes_mut_ref(a: &mut u64, x: u64)
            requires x < 50
            ensures mut_ref_future(a) == x + 1
        {
            *a = x + 1;
        }

        fn test1() {
            let mut a = 24;
            let mut a_ref = &mut a;

            call_takes_mut_ref(a_ref, *a_ref);

            assert(a == 25);
        }

        fn test1_fails() {
            let mut a = 24;
            let mut a_ref = &mut a;

            call_takes_mut_ref(a_ref, *a_ref);

            assert(a == 25);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] two_phase_lifetime_error ["new-mut-ref"] => verus_code! {
        fn call_takes_mut_ref(a: &mut u64, x: u64) {
            *a = x + 1;
        }

        fn test2() {
            let mut a = 24;
            let mut a_ref = &mut a;

            call_takes_mut_ref(&mut *a_ref, *a_ref);

            assert(a == 25);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot use `*a_ref` because it was mutably borrowed")
}

test_verify_one_file_with_options! {
    #[test] two_phase_lifetime_error_generic ["new-mut-ref"] => verus_code! {
        fn call_generic<T>(a: T, x: u64) {
        }

        fn test2() {
            let mut a = 24;
            let mut a_ref = &mut a;

            call_generic(a_ref, *a_ref);
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `a_ref`")
}

test_verify_one_file_with_options! {
    #[test] two_phase_receiver_struct ["new-mut-ref"] => verus_code! {
        struct X {
            a: u64,
            b: u64,
        }

        struct Y {
            x1: X,
            x2: X,
        }

        impl X {
            fn method_call(&mut self, x: u64)
                ensures mut_ref_future(self) == (X {
                    a: x,
                    b: mut_ref_current(self).a,
                })
            {
                self.b = self.a;
                self.a = x;
            }
        }

        fn test1() {
            let mut x = X { a: 0, b: 1 };
            x.method_call(x.a + 20);

            assert(x == X { a: 20, b: 0 });
        }

        fn test1_fails() {
            let mut x = X { a: 0, b: 1 };
            x.method_call(x.a + 20);

            assert(x == X { a: 20, b: 0 });
            assert(false); // FAILS
        }

        fn test2() {
            let mut x = X { a: 0, b: 1 };
            let mut x_ref = &mut x;
            x_ref.method_call(x_ref.a + 20);

            assert(x == X { a: 20, b: 0 });
        }

        fn test2_fails() {
            let mut x = X { a: 0, b: 1 };
            let mut x_ref = &mut x;
            x_ref.method_call(x_ref.a + 20);

            assert(x == X { a: 20, b: 0 });
            assert(false); // FAILS
        }

        fn test3() {
            let mut y = Y { x1: X { a: 0, b: 1 }, x2: X { a: 3, b: 4 } };
            y.x1.method_call(y.x1.a + 20);

            assert(y == Y { x1: X { a: 20, b: 0 }, x2: X { a: 3, b: 4 } });
        }

        fn test3_fails() {
            let mut y = Y { x1: X { a: 0, b: 1 }, x2: X { a: 3, b: 4 } };
            y.x1.method_call(y.x1.a + 20);

            assert(y == Y { x1: X { a: 20, b: 0 }, x2: X { a: 3, b: 4 } });
            assert(false); // FAILS
        }

        fn test4() {
            let mut y = Y { x1: X { a: 0, b: 1 }, x2: X { a: 3, b: 4 } };
            let y_ref = &mut y;
            y_ref.x1.method_call(y_ref.x1.a + y_ref.x1.b + 20);

            assert(y == Y { x1: X { a: 21, b: 0 }, x2: X { a: 3, b: 4 } });
        }

        fn test4_fails() {
            let mut y = Y { x1: X { a: 0, b: 1 }, x2: X { a: 3, b: 4 } };
            let y_ref = &mut y;
            y_ref.x1.method_call(y_ref.x1.a + y_ref.x1.b + 20);

            assert(y == Y { x1: X { a: 21, b: 0 }, x2: X { a: 3, b: 4 } });
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] two_phase_arrays_slices ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        struct X {
            a: u64,
            b: u64,
        }

        impl X {
            fn method_call(&mut self, x: u64)
                ensures mut_ref_future(self) == (X {
                    a: x,
                    b: mut_ref_current(self).a,
                })
            {
                self.b = self.a;
                self.a = x;
            }
        }

        fn test_slice(j: &mut [X])
            requires
                (*j).len() > 0,
                (*j)[0] == (X { a: 0, b: 1 }),
        {
            j[0].method_call(j[0].a + 20);
            assert((*j)[0] == (X { a: 20, b: 0 }));
        }

        fn test_slice_fail(j: &mut [X])
            requires
                (*j).len() > 0,
                (*j)[0] == (X { a: 0, b: 1 }),
        {
            j[0].method_call(j[0].a + 20);
            assert((*j)[0] == (X { a: 20, b: 0 }));
            assert(false); // FAILS
        }

        fn test_slice_boxed(j: Box<[X]>)
            requires
                j.len() > 0,
                j[0] == (X { a: 0, b: 1 }),
        {
            let mut j = j;
            j[0].method_call(j[0].a + 20);
            assert(j[0] == (X { a: 20, b: 0 }));
        }

        fn test_slice_boxed_fail(j: Box<[X]>)
            requires
                j.len() > 0,
                j[0] == (X { a: 0, b: 1 }),
        {
            let mut j = j;
            j[0].method_call(j[0].a + 20);
            assert(j[0] == (X { a: 20, b: 0 }));
            assert(false); // FAILS
        }

        fn test_slice_boxed2(j: Box<[X]>)
            requires
                j.len() > 0,
                j[0] == (X { a: 0, b: 1 }),
        {
            let mut j = j;
            let mut j_ref = &mut j;
            j_ref[0].method_call(j_ref[0].a + 20);
            assert(j[0] == (X { a: 20, b: 0 }));
        }

        fn test_slice_boxed2_fail(j: Box<[X]>)
            requires
                j.len() > 0,
                j[0] == (X { a: 0, b: 1 }),
        {
            let mut j = j;
            let mut j_ref = &mut j;
            j_ref[0].method_call(j_ref[0].a + 20);
            assert(j[0] == (X { a: 20, b: 0 }));
            assert(false); // FAILS
        }

        fn test_array(j: &mut [X; 2])
            requires
                mut_ref_current(j)[0] == (X { a: 0, b: 1 }),
        {
            j[0].method_call(j[0].a);
            assert(mut_ref_current(j)[0] == (X { a: 0, b: 0 }));
        }

        fn test_array_fail(j: &mut [X; 2])
            requires
                mut_ref_current(j)[0] == (X { a: 0, b: 1 }),
        {
            j[0].method_call(j[0].a);
            assert(mut_ref_current(j)[0] == (X { a: 0, b: 0 }));
            assert(false); // FAILS
        }

        fn test_array2() {
            let mut j: [X; 2] = [
                X { a: 0, b: 1 },
                X { a: 5, b: 10 },
            ];

            j[0].method_call(j[0].a + 20);
            assert(j[0] == (X { a: 20, b: 0 }));
        }

        fn test_array2_fail() {
            let mut j: [X; 2] = [
                X { a: 0, b: 1 },
                X { a: 5, b: 10 },
            ];

            j[0].method_call(j[0].a + 20);
            assert(j[0] == (X { a: 20, b: 0 }));
            assert(false); // FAILS
        }

        fn test_array3() {
            let mut j: [X; 2] = [
                X { a: 0, b: 1 },
                X { a: 5, b: 10 },
            ];
            let j_ref = &mut j;

            j_ref[0].method_call(j_ref[0].a + 20);
            assert(j[0] == (X { a: 20, b: 0 }));
        }

        fn test_array3_fail() {
            let mut j: [X; 2] = [
                X { a: 0, b: 1 },
                X { a: 5, b: 10 },
            ];
            let j_ref = &mut j;

            j_ref[0].method_call(j_ref[0].a + 20);
            assert(j[0] == (X { a: 20, b: 0 }));
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 6) // TODO(new_mut_ref)
}

test_verify_one_file_with_options! {
    #[test] two_phase_vec ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        struct X {
            a: u64,
            b: u64,
        }

        impl X {
            fn method_call(&mut self, x: u64)
                ensures mut_ref_future(self) == (X {
                    a: x,
                    b: mut_ref_current(self).a,
                })
            {
                self.b = self.a;
                self.a = x;
            }
        }

        fn test_vec(j: &mut Vec<X>) {
            // j[0] is actually a call to index_mut, which disrupts the possibility of a
            // two-phase borrow.
            j[0].method_call(j[0].a);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `*j` as immutable because it is also borrowed as mutable")
}

test_verify_one_file_with_options! {
    #[test] two_phase_ctor ["new-mut-ref"] => verus_code! {
        struct Pair<A, B>(A, B);

        fn test1() {
            let mut a = 24;
            let mut a_ref = &mut a;

            let x: Pair<&mut u64, u64> = Pair(a_ref, *a_ref);

            assert(*x.0 == 24);
            assert(x.1 == 24);

            *x.0 = 50;

            assert(a == 50);
        }

        fn test1_fails() {
            let mut a = 24;
            let mut a_ref = &mut a;

            let x: Pair<&mut u64, u64> = Pair(a_ref, *a_ref);

            assert(*x.0 == 24);
            assert(x.1 == 24);

            *x.0 = 50;

            assert(a == 50);

            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] two_phase_tuple ["new-mut-ref"] => verus_code! {
        fn test1() {
            let mut a = 24;
            let mut a_ref = &mut a;

            let x: (&mut u64, u64) = (a_ref, *a_ref);

            assert(*x.0 == 24);
            assert(x.1 == 24);

            *x.0 = 50;

            assert(a == 50);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot use `*a_ref` because it was mutably borrowed")
}

test_verify_one_file_with_options! {
    #[test] two_phase_struct ["new-mut-ref"] => verus_code! {
        struct Pair<'a> {
            a_ref: &'a mut u64,
            a: u64,
        }

        fn test1() {
            let mut a = 24;
            let mut a_ref = &mut a;

            let x = Pair { a_ref: a_ref, a: *a_ref };
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot use `*a_ref` because it was mutably borrowed")
}

test_verify_one_file_with_options! {
    #[test] struct_mut_ref_pair_immut_ref ["new-mut-ref"] => verus_code! {
        struct BigStruct<'a, 'b>(&'a mut (u64, &'b (u64, u64)));

        fn test1() {
            let pair = (2, 3);
            let mut big_pair = (4, &pair);
            let mut big = BigStruct(&mut big_pair);

            *big.0 = (5, &pair);

            assert(has_resolved(big.0));
            assert(mut_ref_current(big.0) == mut_ref_future(big.0));
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] calls_unwind_extra_cfg_edge ["new-mut-ref"] => verus_code! {
        fn call_might_unwind() { }
        fn call_no_unwind() no_unwind { }

        // If `*x = y` is definitely going to be reached, then we can resolve *x,
        // however, if there's an unwindable call, then `*x = y` might not be reached.

        fn test1<'a>(x: &mut &'a mut u64, y: &'a mut u64) {
            assert(has_resolved(*x));
            *x = y;
        }

        fn test2<'a>(x: &mut &'a mut u64, y: &'a mut u64) {
            assert(has_resolved(*x));
            call_no_unwind();
            *x = y;
        }

        fn test3<'a>(x: &mut &'a mut u64, y: &'a mut u64) {
            assert(has_resolved(*x)); // FAILS
            call_might_unwind();
            *x = y;
        }

        fn test4<'a>(x: &mut &'a mut u64, y: &'a mut u64) {
            call_might_unwind();
            assert(has_resolved(*x));
            *x = y;
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] has_resolved_for_struct_with_drop_impl ["new-mut-ref"] => verus_code! {
        struct XNoDrop<'a> {
            b: &'a mut u64,
        }

        struct X<'a> {
            b: &'a mut u64,
        }

        impl<'a> Drop for X<'a> {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
            {
                *self.b = 20;
            }
        }

        struct Y<'a> {
            x: X<'a>,
            u: &'a mut u64,
        }

        struct YNoDrop<'a> {
            x: XNoDrop<'a>,
            u: &'a mut u64,
        }


        fn test1<'a>(x: X<'a>) {
            // There is an implicit drop for x at the end of this function body
            // This could possibly modify *x.b (as demonstrated in the Drop impl above)
            // Thus, we make the `has_resolved` predicate of X not imply `has_resolved` of its fields.

            assert(has_resolved(x));
            assert(has_resolved(x.b)); // FAILS
        }

        fn test2<'a>(x: XNoDrop<'a>) {
            assert(has_resolved(x));
            assert(has_resolved(x.b));
        }

        fn test3<'a>(y: Y<'a>) {
            assert(has_resolved(y));
            assert(has_resolved(y.x));
            assert(has_resolved(y.x.b)); // FAILS
        }

        fn test4<'a>(y: YNoDrop<'a>) {
            assert(has_resolved(y));
            assert(has_resolved(y.x));
            assert(has_resolved(y.x.b));
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] assign_op_to_mut_ref ["new-mut-ref"] => verus_code! {
        fn test_add_assign(i: u64)
            requires i < 1000
        {
            let mut x = 20;
            let x_ref = &mut x;

            *x_ref += i;

            assert(x == 20 + i);
        }

        fn test_add_assign_fail(i: u64)
            requires i < 1000
        {
            let mut x = 20;
            let x_ref = &mut x;

            *x_ref += i;

            assert(x == 20 + i);
            assert(false); // FAILS
        }

        fn test_add_assign_fields(i: u64)
            requires i < 1000
        {
            let mut x = (20, 30);
            let x_ref = &mut x;

            x_ref.0 += i;

            assert(x.0 == 20 + i);
            assert(x.1 == 30);
        }

        fn test_add_assign_fields_fail(i: u64)
            requires i < 1000
        {
            let mut x = (20, 30);
            let x_ref = &mut x;

            x_ref.0 += i;

            assert(x.0 == 20 + i);
            assert(x.1 == 30);
            assert(false); // FAILS
        }

        fn test_add_assign_overflow(i: u64)
        {
            let mut x = (20, 30);
            let x_ref = &mut x;

            x_ref.0 += i; // FAILS
        }

        fn test_add_assign_twice(i: u64)
            requires i < 1000
        {
            let mut x = 20;
            let x_ref = &mut x;

            *x_ref += i;
            *x_ref += i;

            assert(x == 20 + 2*i);
        }

        fn test_add_assign_twice_fail(i: u64)
            requires i < 1000
        {
            let mut x = 20;
            let x_ref = &mut x;

            *x_ref += i;
            *x_ref += i;

            assert(x == 20 + 2*i);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] ctor_with_update_tail ["new-mut-ref"] => verus_code! {
        tracked struct TTPair<A, B> {
            tracked a: A,
            tracked b: B,
        }

        fn test1() {
            let mut g1: Ghost<int> = Ghost(1);
            let mut g2: Ghost<int> = Ghost(2);
            let mut g3: Ghost<int> = Ghost(3);

            let tracked p = TTPair {
                a: &mut g1,
                b: &mut g2,
            };

            proof {
                *p.a.borrow_mut() = 4;
                *p.b.borrow_mut() = 5;
            }

            let tracked p2 = TTPair {
                a: &mut g3,
                .. p
            };

            assert(has_resolved(p.b)); // FAILS

            proof {
                *p2.b.borrow_mut() = 4;
            }
        }

        fn test2() {
            let mut g1: Ghost<int> = Ghost(1);
            let mut g2: Ghost<int> = Ghost(2);
            let mut g3: Ghost<int> = Ghost(3);

            let tracked p = TTPair {
                a: &mut g1,
                b: &mut g2,
            };

            proof {
                *p.a.borrow_mut() = 4;
                *p.b.borrow_mut() = 5;
            }

            let tracked p2 = TTPair {
                a: &mut g3,
                .. p
            };

            // ok, p.a was not moved
            assert(has_resolved(p.a));

            proof {
                *p2.b.borrow_mut() = 4;
            }
        }

        fn test3() {
            let mut g1: Ghost<int> = Ghost(1);
            let mut g2: Ghost<int> = Ghost(2);
            let mut g3: Ghost<int> = Ghost(3);

            let tracked p = TTPair {
                a: &mut g1,
                b: &mut g2,
            };

            proof {
                *p.a.borrow_mut() = 4;
                *p.b.borrow_mut() = 5;
            }

            let tracked p2 = TTPair {
                a: &mut g3,
                .. p
            };

            proof {
                *p.a.borrow_mut() = 4;
                *p2.a.borrow_mut() = 5;
                *p2.b.borrow_mut() = 6;
            }

            assert(g1@ == 4);
            assert(g3@ == 5);
            assert(g2@ == 6);

            assert(false); // FAILS
        }

        spec fn id<A>(a: A) -> A { a }

        fn test4() {
            let mut g1: Ghost<int> = Ghost(1);
            let mut g2: Ghost<int> = Ghost(2);
            let mut g3: Ghost<int> = Ghost(3);

            let tracked p = TTPair {
                a: &mut g1,
                b: &mut g2,
            };

            proof {
                *p.a.borrow_mut() = 4;
                *p.b.borrow_mut() = 5;
            }

            let tracked ref_g3 = &mut g3;
            // this doesn't do any moves because it's ghost mode:
            let ghost p2 = TTPair {
                a: id(ref_g3),
                .. p
            };

            assert(has_resolved(p.b));
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] shr_bor_of_pair_of_mut_bor ["new-mut-ref"] => verus_code! {
        enum BigEnum<'a, 'b> {
            A(&'a (u64, &'b mut u64)),
        }

        fn test_fails() {
            let mut pair = 2;
            let mut big_pair = (4, &mut pair);
            let mut big = BigEnum::A(&big_pair);

            *big_pair.1 = 10;

            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] fin_keyword ["new-mut-ref"] => verus_code! {
        fn foo(x: &mut u64) {
            assert(mut_ref_future(x) == *fin(x));
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fin_keyword2 ["new-mut-ref"] => verus_code! {
        fn foo(x: &mut bool) {
            assert(mut_ref_current(fin(x)));
        }
    } => Err(err) => assert_vir_error_msg(err, "The result of `fin` must be dereferenced")
}

test_verify_one_file_with_options! {
    #[test] resolve_places_with_projection_types ["new-mut-ref"] => verus_code! {
        trait Tr {
            type AssocType;
        }

        struct P<T: Tr> {
            a: T::AssocType,
            b: u64,
        }

        struct X<'a> { a: &'a u64 }

        impl<'a> Tr for X<'a> {
            type AssocType = (&'a mut u64, &'a mut u64);
        }

        fn test<'a>(p: P<X<'a>>) {
            let mut p = p;
            assert(has_resolved(p.a.1));
            p.b = 20;
            *p.a.0 = 30;
            assert(has_resolved(p.a.0));
        }

        fn test2<'a>(p: P<X<'a>>) {
            let mut p = p;
            p.b = 20;
            assert(has_resolved(p.a.0)); // FAILS
            *p.a.0 = 30;
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] place_that_doesnt_return ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test1() {
            let mut a = 4;
            *({ loop {}; &mut a }) = 5;
            assert(false);
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test2() {
            let mut a = 4;
            *({ loop {}; &mut a }) = ({ assert(false); 5 });
            assert(false);
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test2_fails() {
            let mut a = 4;
            *({
                assert(false); // FAILS
            &mut a }) = ({ loop {} 5 });
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test3() {
            let mut a = 4;
            let mut a_ref: &mut u64 = loop { };
            assert(false);
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test4() {
            let y: [[u64; 2]; 2] = [[0,1],[2,3]];
            let x = y[({ loop{}; 0 })][({ assert(false); 1 })];
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test5() {
            let y: [[u64; 2]; 2] = [[0,1],[2,3]];
            let x = y[({
              assert(false); // FAILS
            1})][({ loop{}; 0 })];
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test6(y: [&mut (u64, u64); 2]) {
            let mut y = y;
            (*y[({ loop{} 0 })]).0 = 20;
            assert(false);
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file_with_options! {
    #[test] compound_op_that_doesnt_return ["new-mut-ref"] => verus_code! {
        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test1(y: [&mut (u64, u64); 2]) {
            let mut y = y;
            (*y[({ loop{} 0 })]).0 += 20;
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test2(y: [&mut (u64, u64); 2]) {
            let mut y = y;
            (*y[({
                assert(false); // FAILS
            0 })]).0 += ({ loop{} 20 });
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test3(y: [&mut (u64, u64); 2]) {
            let mut y = y;
            (*y[0]).0 += ({ loop{} 20 });
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test4(y: &mut [&mut (u64, u64); 2])
            ensures mut_ref_current(y) == mut_ref_future(y)
        {
            let mut y = y;
            (*y[0]).0 += ({ return; 20 });
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test4_fails(y: &mut [&mut (u64, u64); 2])
            ensures false
        {
            let mut y = y;
            (*y[0]).0 += ({
                return; // FAILS
                0
            });
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file_with_options! {
    #[test] call_with_args_that_dont_return ["new-mut-ref"] => verus_code! {
        fn call(a: &mut u64, b: &mut u64, c: &mut u64) { }

        fn call_requires_false(a: &mut u64, b: &mut u64, c: &mut u64)
            requires false
        { }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unreachable_code)]
        fn test1() {
            let mut a = 20;
            let mut b = 30;
            let mut c = 40;
            call_requires_false(&mut a, ({ loop {} &mut b }), &mut c);
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unreachable_code)]
        fn test2() {
            let mut a = 20;
            let mut b = 30;
            let mut c = 40;
            call_requires_false(&mut a, (loop {}), &mut c);
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unreachable_code)]
        fn test3(a_ref: &mut u64, c_ref: &mut u64)
            ensures
                mut_ref_future(a_ref) == mut_ref_current(a_ref),
                mut_ref_future(c_ref) == mut_ref_current(c_ref),
        {
            call_requires_false(a_ref, (return), c_ref);
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unreachable_code)]
        fn test3_fails(a_ref: &mut u64, c_ref: &mut u64)
            ensures
                false
        {
            call_requires_false(a_ref, (
                return // FAILS
            ), c_ref);
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unreachable_code)]
        fn test4() {
            let mut a = 20;
            let mut b = 30;
            let mut c = 40;
            call_requires_false(&mut a, (loop {}), ({ assert(false); &mut c }));
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unreachable_code)]
        fn test5() {
            let mut a = 20;
            let mut b = 30;
            let mut c = 40;
            call(({
              assert(false); // FAILS
            &mut a }), (loop {}), &mut c);
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file_with_options! {
    #[test] ctor_with_args_that_dont_return ["new-mut-ref"] => verus_code! {
        struct Ctor<'a, 'b, 'c>(&'a mut u64, &'b mut u64, &'c mut u64);

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unreachable_code)]
        fn test1() {
            let mut a = 20;
            let mut b = 30;
            let mut c = 40;
            let ct = Ctor(&mut a, ({ loop {} &mut b }), &mut c);
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unreachable_code)]
        fn test2() {
            let mut a = 20;
            let mut b = 30;
            let mut c = 40;
            let ct = Ctor(&mut a, (loop {}), &mut c);
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unreachable_code)]
        fn test3(a_ref: &mut u64, c_ref: &mut u64)
            ensures
                mut_ref_future(a_ref) == mut_ref_current(a_ref),
                mut_ref_future(c_ref) == mut_ref_current(c_ref),
        {
            let ct = Ctor(a_ref, (return), c_ref);
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unreachable_code)]
        fn test3_fails(a_ref: &mut u64, c_ref: &mut u64)
            ensures
                false
        {
            let ct = Ctor(a_ref, (
                return // FAILS
            ), c_ref);
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unreachable_code)]
        fn test4() {
            let mut a = 20;
            let mut b = 30;
            let mut c = 40;
            let ct = Ctor(&mut a, (loop {}), ({ assert(false); &mut c }));
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unreachable_code)]
        fn test5() {
            let mut a = 20;
            let mut b = 30;
            let mut c = 40;
            let ct = Ctor(({
              assert(false); // FAILS
            &mut a }), (loop {}), &mut c);
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file_with_options! {
    #[test] mut_ref_with_implicit_box_deref ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        enum List {
            Cons(u64, Box<List>),
            Nil,
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn build_zero_list(len: u64) -> List {
            let mut list = List::Nil;
            let mut cur = &mut list;

            let mut i = 0;
            while i < len {
                *cur = List::Cons(0, Box::new(List::Nil));

                match cur {
                    List::Cons(_, b) => {
                        // Replace `cur` with a reference to the newly-created List::Nil,
                        // the child of the previous `cur`.
                        cur = &mut *b;
                    }
                    _ => { /* clearly unreachable */ }
                }

                i += 1;
            }

            return list;
        }
    } => Ok(())
}
