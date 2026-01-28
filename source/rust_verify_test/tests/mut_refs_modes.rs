#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] mut_borrow_of_ghost_local_in_proof_fn ["new-mut-ref"] => verus_code! {
        proof fn test() {
            let ghost g: u64 = 3;
            let mut_ret = &mut g;
        }
    } => Err(err) => assert_vir_error_msg(err, "can only take mutable borrow of an exec-mode place; found spec-mode place")
}

test_verify_one_file_with_options! {
    #[test] mut_borrow_of_tracked_local_in_proof_fn ["new-mut-ref"] => verus_code! {
        struct X { }
        proof fn test() {
            let tracked x = X { };
            let mut_ret = &mut x;
        }
    } => Err(err) => assert_vir_error_msg(err, "can only take mutable borrow of an exec-mode place; found proof-mode place")
}

test_verify_one_file_with_options! {
    #[test] mut_borrow_of_ghost_local_in_exec_fn ["new-mut-ref"] => verus_code! {
        fn test() {
            let ghost g: u64 = 3;
            let mut_ret = &mut g;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot access spec-mode place in executable context")
}

test_verify_one_file_with_options! {
    #[test] mut_borrow_of_tracked_local_in_exec_fn ["new-mut-ref"] => verus_code! {
        struct X { }
        fn test() {
            let tracked x = X { };
            let mut_ret = &mut x;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot access proof-mode place in executable context")
}

test_verify_one_file_with_options! {
    #[test] mut_borrow_of_ghost_local_in_proof_block ["new-mut-ref"] => verus_code! {
        fn test() {
            let ghost g: u64 = 3;
            proof {
                let tracked mut_ret = &mut g;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "can only take mutable borrow of an exec-mode place; found spec-mode place")
}

test_verify_one_file_with_options! {
    #[test] mut_borrow_of_tracked_local_in_proof_block_to_ghost ["new-mut-ref"] => verus_code! {
        struct X { }
        fn test() {
            let tracked x = X { };
            proof {
                let tracked mut_ret = &mut x;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "can only take mutable borrow of an exec-mode place; found proof-mode place")
}

test_verify_one_file_with_options! {
    #[test] mut_borrow_of_exec_local_in_proof_block_to_tracked ["new-mut-ref"] => verus_code! {
        struct X { }
        fn test() {
            let mut x = X { };
            proof {
                let tracked mut_ret = &mut x;
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] mut_borrow_of_exec_local_in_tracked_local_decl ["new-mut-ref"] => verus_code! {
        struct X { }
        fn test() {
            let mut x = X { };
            let tracked mut_ret = &mut x;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] mut_borrow_lifetime_error ["new-mut-ref"] => verus_code! {
        struct Y { }
        struct X { y: Y }
        fn test() {
            let mut x = Tracked(X { y: Y{} });
            proof {
                let tracked mut_ref1 = &mut x;
                let tracked mut_ref2 = &mut x;
                mut_ref1.borrow_mut().y = Y { };
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `x` as mutable more than once at a time")
}

test_verify_one_file_with_options! {
    #[test] mut_borrow_lifetime_error2 ["new-mut-ref"] => verus_code! {
        struct Y { }
        struct X { y: Y }
        fn test() {
            let mut x = Tracked(X { y: Y{} });
            proof {
                let tracked mut_ref1 = &mut x;
                let ghost mut_ref2 = &mut x;
                mut_ref1.borrow_mut().y = Y { };
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `x` as mutable more than once at a time")
}

test_verify_one_file_with_options! {
    // TODO(new_mut_ref): fix
    #[ignore] #[test] mut_borrow_in_ghost_decl ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 0;
            let ghost mut_ref2 = &mut x;
            assert(x == 0);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] mut_borrow_in_spec_fn ["new-mut-ref"] => verus_code! {
        spec fn foo<'a>() -> &'a mut bool {
            &mut false
        }
    } => Err(err) => assert_vir_error_msg(err, "mutable borrow is not allowed in spec context")
}

test_verify_one_file_with_options! {
    #[test] mut_borrow_in_assert_by ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut a = 24;
            assert(true) by {
                let x = &mut a;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "mutable borrow is not allowed in 'assert ... by' statement")
}

test_verify_one_file_with_options! {
    #[test] modify_tracked_place_in_exec_code ["new-mut-ref"] => verus_code! {
        #[verifier::external_body] struct Y { }
        #[verifier::external_body] struct Z { }
        struct X { y: Tracked<(Y, Z)> }
        axiom fn new_y() -> (tracked y: Y);
        axiom fn new_z() -> (tracked z: Z);

        fn test(x0: X) {
            let mut x = x0;
            let mut_ref = &mut x;

            mut_ref.y.borrow_mut().0 = new_y();
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot access proof-mode place in executable context")
}

test_verify_one_file_with_options! {
    #[test] modify_ghost_place_in_exec_code ["new-mut-ref"] => verus_code! {
        struct X { y: Ghost<(bool, bool)> }

        fn test(x0: X) {
            let mut x = x0;
            let mut_ref = &mut x;

            mut_ref.y.borrow_mut().0 = false;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot access spec-mode place in executable context")
}

test_verify_one_file_with_options! {
    #[test] modify_ghost_place_in_assert_by ["new-mut-ref"] => verus_code! {
        struct X { y: Ghost<(bool, bool)> }

        fn test(x0: X) {
            let mut x = x0;
            let mut_ref = &mut x;

            assert(true) by {
                mut_ref.y.borrow_mut().0 = false;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "assignment is not allowed in 'assert ... by' statement")
}

test_verify_one_file_with_options! {
    #[test] modify_tracked_place_in_proof_code ["new-mut-ref"] => verus_code! {
        #[verifier::external_body] struct Y { }
        #[verifier::external_body] struct Z { }
        struct X { y: Tracked<(Y, Z)> }
        axiom fn new_y() -> (tracked y: Y);
        axiom fn new_z() -> (tracked z: Z);

        fn test(x0: X) {
            let mut x = x0;
            let mut_ref = &mut x;

            let tracked y = new_y();

            proof {
                mut_ref.y.borrow_mut().0 = y;
            }

            assert(has_resolved(mut_ref));
            assert(x.y@.0 == y);
        }

        fn test2(x0: X) {
            let mut x = x0;
            let mut_ref = &mut x;

            let tracked y = new_y();

            proof {
                let tracked mr = mut_ref;
                mr.y.borrow_mut().0 = y;
                assert(has_resolved(mr));
            }

            assert(x.y@.0 == y);
        }

        fn test3(x0: X) {
            let mut x = x0;

            let tracked y = new_y();

            proof {
                let tracked mr = &mut x;
                mr.y.borrow_mut().0 = y;
                assert(has_resolved(mr));
            }

            assert(x.y@.0 == y);
        }

        fn test4(x0: X) {
            let mut x = x0;

            let tracked y = new_y();

            proof {
                let tracked mr = &mut x;

                let z = mr.y.borrow_mut().0;
                assert(z == x0.y@.0);

                mr.y.borrow_mut().0 = y;
            }

            assert(x.y@.0 == y);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] modify_ghost_place_in_proof_code ["new-mut-ref"] => verus_code! {
        struct X { y: Ghost<(int, int)> }

        fn test(x0: X) {
            let mut x = x0;
            let mut_ref = &mut x;

            proof {
                mut_ref.y.borrow_mut().0 = 20int;
            }

            assert(has_resolved(mut_ref));
            assert(x.y@.0 == 20);
        }

        fn test2(x0: X) {
            let mut x = x0;
            let mut_ref = &mut x;

            proof {
                let tracked mr = mut_ref;
                mr.y.borrow_mut().0 = 20int;
                assert(has_resolved(mr));
            }

            assert(x.y@.0 == 20);
        }

        fn test3(x0: X) {
            let mut x = x0;
            let mut_ref = &mut x;

            proof {
                let tracked mr = &mut x;
                mr.y.borrow_mut().0 = 20int;
                assert(has_resolved(mr));
            }

            assert(x.y@.0 == 20);
        }

        fn test4(x0: X) {
            let mut x = x0;
            let mut_ref = &mut x;

            proof {
                let tracked mr = &mut x;
                let z = mr.y.borrow_mut().0;
                assert(z == x0.y@.0);
                mr.y.borrow_mut().0 = 20int;
                assert(has_resolved(mr));
            }

            assert(x.y@.0 == 20);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] modify_exec_place_in_proof_code ["new-mut-ref"] => verus_code! {
        struct X { y: Ghost<(int, int)> }

        fn test3(x0: X, x1: X) {
            let mut x = x0;
            let mut_ref = &mut x;

            proof {
                *mut_ref = x1;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot mutate exec-mode place in proof-code")
}

test_verify_one_file_with_options! {
    #[test] modify_exec_place_in_proof_code2 ["new-mut-ref"] => verus_code! {
        struct X { y: Ghost<(int, int)> }

        fn test3(x0: X, x1: X) {
            let mut x = x0;
            let mut_ref = &mut x;

            proof {
                // mut_ref.y is an exec-mode place of type Ghost
                mut_ref.y = Ghost((3, 2));
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot mutate exec-mode place in proof-code")
}

test_verify_one_file_with_options! {
    #[test] mut_ref_tracked_place_in_proof_code ["new-mut-ref"] => verus_code! {
        #[verifier::external_body] struct Y { }
        #[verifier::external_body] struct Z { }
        struct X { y: Tracked<(Y, Z)> }
        axiom fn new_y() -> (tracked y: Y);
        axiom fn new_z() -> (tracked z: Z);

        fn test(x0: X) {
            let mut x = x0;
            let mut_ref = &mut x;

            proof {
                let tracked z = &mut mut_ref.y.borrow_mut().0;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "can only take mutable borrow of an exec-mode place; found proof-mode place")
}

test_verify_one_file_with_options! {
    #[test] mut_ref_tracked_place_in_proof_code2 ["new-mut-ref"] => verus_code! {
        #[verifier::external_body] struct Y { }
        #[verifier::external_body] struct Z { }
        struct X { y: Tracked<(Y, Z)> }
        axiom fn new_y() -> (tracked y: Y);
        axiom fn new_z() -> (tracked z: Z);

        fn test(x0: X) {
            let mut x = x0;

            proof {
                let tracked z = x.y.borrow_mut();
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "can only take mutable borrow of an exec-mode place; found proof-mode place")
}

test_verify_one_file_with_options! {
    #[test] mut_ref_ghost_place_in_proof_code ["new-mut-ref"] => verus_code! {
        struct X { y: Ghost<(int, int)> }

        fn test(x0: X) {
            let mut x = x0;
            let mut_ref = &mut x;

            proof {
                let tracked z = &mut mut_ref.y.borrow_mut().0;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "can only take mutable borrow of an exec-mode place; found spec-mode place")
}

test_verify_one_file_with_options! {
    #[test] no_mutation_through_ghost_mut_ref ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 30u64;
            let mut_ref = &mut x;
            let ghost mr = mut_ref;

            proof {
                *mr = 20u64;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot mutate through a spec-mode mutable reference")
}

test_verify_one_file_with_options! {
    #[test] no_mutation_through_ghost_mut_ref2 ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 30u64;
            let mut_ref = &mut x;
            let mr = Ghost(mut_ref);

            proof {
                **mr.borrow_mut() = 20u64;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot mutate through a spec-mode mutable reference")
}

test_verify_one_file_with_options! {
    #[test] no_mutation_through_ghost_mut_ref3 ["new-mut-ref"] => verus_code! {
        struct X { }

        fn test() {
            let mut x = Tracked(X {});
            let mut_ref = &mut x;
            let mr = Ghost(mut_ref);

            proof {
                *mr.borrow_mut().borrow_mut() = X { };
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot mutate through a spec-mode mutable reference")
}

test_verify_one_file_with_options! {
    #[test] no_mut_ref_through_ghost_mut_ref ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 30u64;
            let mut_ref = &mut x;
            let ghost mr = mut_ref;

            proof {
                let tracked z = &mut *mr;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot mutate through a spec-mode mutable reference")
}

test_verify_one_file_with_options! {
    #[test] no_mut_ref_through_ghost_mut_ref2 ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 30u64;
            let mut_ref = &mut x;
            let mr = Ghost(mut_ref);

            proof {
                let tracked z = &mut **mr.borrow_mut();
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot mutate through a spec-mode mutable reference")
}

test_verify_one_file_with_options! {
    #[test] no_mut_ref_through_ghost_mut_ref3 ["new-mut-ref"] => verus_code! {
        struct X { }

        fn test() {
            let mut x = Tracked(X {});
            let mut_ref = &mut x;
            let mr = Ghost(mut_ref);

            proof {
                let tracked z = &mut *mr.borrow_mut().borrow_mut();
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot mutate through a spec-mode mutable reference")
}

test_verify_one_file_with_options! {
    #[test] read_through_ghost_mut_ref_ok ["new-mut-ref"] => verus_code! {
        struct X { }

        fn test() {
            let mut x = Tracked(X {});
            let mut_ref = &mut x;
            let mut mr = Ghost(mut_ref);

            proof {
                let z = *mr.borrow_mut().borrow_mut();
                assert(z == X { });
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] cant_move_out_of_tracked_location ["new-mut-ref"] => verus_code! {
        struct Pair<A, B>(Tracked<A>, Ghost<B>);

        fn test_trk<X>(t0: Pair<X, X>) {
            let mut t = t0;

            proof {
                // In principle this could be interpreted as a move, but the borrowchecker
                // doesn't know to do that.
                let tracked y = *t.0.borrow_mut();
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of a mutable reference")
}

test_verify_one_file_with_options! {
    #[test] ghost_places_dont_count_as_moves ["new-mut-ref"] => verus_code! {
        struct Pair<A, B>(Tracked<A>, Ghost<B>);

        enum Option<A> {
            Some(A),
            None,
        }
        use crate::Option::Some;
        use crate::Option::None;

        proof fn consume<X>(tracked x: X) { }
        proof fn use_ghost<X>(x: X) { }

        fn test_ghost<X>(t0: Pair<X, X>) {
            let mut t = t0;

            proof {
                match *t.1.borrow_mut() {
                    b => { use_ghost(b); }
                }
            }

            assert(has_resolved(t));
        }

        fn test_option_ghost<X>(t0: Pair<Option<X>, Option<X>>) {
            let mut t = t0;

            proof {
                match *t.1.borrow_mut() {
                    Some(x) => { use_ghost(x); }
                    None => { }
                }
            }

            assert(has_resolved(t));
        }

        fn test_option_trk2<X>(t0: Pair<Option<X>, Option<X>>) {
            let mut t = t0;

            proof {
                match *t.0.borrow_mut() {
                    Some(_) => { }
                    None => { }
                }
            }

            assert(has_resolved(t));
        }

        fn atbinder_test_let_ghost<X>(t0: Pair<X, X>) {
            let mut t = t0;

            proof {
                let x @ _ = *t.1.borrow_mut();
                use_ghost(x);
            }

            assert(has_resolved(t));
        }

        fn atbinder_test_ghost<X>(t0: Pair<X, X>) {
            let mut t = t0;

            proof {
                match *t.1.borrow_mut() {
                    b @ _ => { use_ghost(b); }
                }
            }

            assert(has_resolved(t));
        }

        fn atbinder_test_option_ghost<X>(t0: Pair<Option<X>, Option<X>>) {
            let mut t = t0;

            proof {
                match *t.1.borrow_mut() {
                    Some(x @ _) => { use_ghost(x); }
                    None => { }
                }
            }

            assert(has_resolved(t));
        }

    } => Ok(())
}

test_verify_one_file_with_options! {
    // TODO(new_mut_ref): need to elide implicit reborrow in this test case
    #[ignore] #[test] ghost_places_dont_resolve ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x: u64 = 0;

            let mut_ref = &mut x;
            let ghost snapshot = mut_ref;

            *mut_ref = 20;

            assert(x == 20);
            assert(has_resolved(mut_ref));
            assert(has_resolved(snapshot)); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] ghost_places_dont_resolve2 ["new-mut-ref"] => verus_code! {
        spec fn id<A>(a: A) -> A { a }

        fn test() {
            let mut x: u64 = 0;

            let mut_ref = &mut x;
            let ghost snapshot = id(mut_ref);

            *mut_ref = 20;

            assert(x == 20);
            assert(has_resolved(mut_ref));
            assert(has_resolved(snapshot)); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] tracked_places_lifetime_error ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x: u64 = 0;

            let mut_ref = &mut x;
            let tracked snapshot = mut_ref;

            *mut_ref = 20;
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `mut_ref`")
}

test_verify_one_file_with_options! {
    #[test] tracked_places_lifetime_error2 ["new-mut-ref", "--no-lifetime"] => verus_code! {
        proof fn id<A>(tracked a: A) -> (tracked ret: A)
            ensures ret === a
        { a }

        fn test() {
            let mut x: u64 = 0;

            let mut_ref = &mut x;
            let tracked snapshot = id(mut_ref);

            *mut_ref = 20;

            // Even with lifetime-checking disabled, our resolution analysis sees tha
            // mut_ref was moved so it doesn't resolve it.
            assert(has_resolved(mut_ref)); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] tracked_places_lifetime_error3 ["new-mut-ref", "--no-lifetime"] => verus_code! {
        proof fn id<A>(tracked a: A) -> (tracked ret: A)
            ensures ret === a
        { a }

        fn test() {
            let mut x: Ghost<u64> = Ghost(0u64);

            let mut_ref = &mut x;
            let tracked snapshot = id(mut_ref);
            let tracked snapshot2 = id(mut_ref);

            proof {
                *snapshot.borrow_mut() = 20u64;
                *snapshot2.borrow_mut() = 30u64;
            }

            // Without lifetime checking, we can get a contradiction since both snapshot
            // and snapshot2 use the same prophecy variable.
            assert(has_resolved(snapshot));
            assert(has_resolved(snapshot2));
            assert(false);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] struct_with_ghost_and_tracked_fields ["new-mut-ref"] => verus_code! {
        tracked struct A<B, C> {
            tracked b: B,
            ghost c: C,
        }

        tracked struct X<'a, 'b, Y, Z> {
            tracked y: &'a mut Y,
            ghost z: &'b mut Z,
        }

        proof fn test1<B, C>(a: A<B, C>) {
            assert(has_resolved(a) ==> has_resolved(a.b));
        }

        proof fn test2<B, C>(a: A<B, C>) {
            assert(has_resolved(a) ==> has_resolved(a.c)); // FAILS
        }

        proof fn test3<'a, 'b, Y, Z>(tracked x: X<'a, 'b, Y, Z>) {
            assert(has_resolved(x.y));
            assert(has_resolved(x.z)); // FAILS

        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] reading_ghost_field_is_not_move ["new-mut-ref", "--no-lifetime"] => verus_code! {
        #[verifier::external_body]
        struct X { }
        axiom fn new_x() -> (tracked x: X);
        axiom fn new_x_gho() -> (x: X);

        fn test<X>(tracked x1: X, tracked x2: X) {
            let mut j = (Tracked(new_x()), Ghost(new_x_gho()));

            proof { let y = *j.1.borrow_mut(); }

            assert(has_resolved(j));
        }

        fn test2<X>(tracked x1: X, tracked x2: X) {
            let mut j = (Tracked(new_x()), Ghost(new_x_gho()));

            // This is an ownership error ("cannot move out of a mutable reference"),
            // but I used --no-lifetime for this test because
            // I want to check the below assert fails. (Our resolution_analysis treats
            // this as a move.)
            proof { let tracked y = *j.0.borrow_mut(); }

            assert(has_resolved(j)); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] modify_ghost_fields_through_mut_refs ["new-mut-ref"] => verus_code! {
        fn test1() {
            let mut t: Ghost<(int, int)> = Ghost((4, 6));
            let mut_ref = &mut t;
            proof { *mut_ref.borrow_mut() = (5, 10); }
            assert(t@ === (5, 10));
        }

        fn test1_fails() {
            let mut t: Ghost<(int, int)> = Ghost((4, 6));
            let mut_ref = &mut t;
            proof { *mut_ref.borrow_mut() = (5, 10); }
            assert(t@ === (5, 10));
            assert(false); // FAILS
        }

        fn test2() {
            let mut t: Ghost<(int, int)> = Ghost((4, 6));
            let mut_ref = &mut t;
            proof { mut_ref.borrow_mut().0 = 5; }
            assert(t@ === (5, 6));
        }

        fn test2_fails() {
            let mut t: Ghost<(int, int)> = Ghost((4, 6));
            let mut_ref = &mut t;
            proof { mut_ref.borrow_mut().0 = 5; }
            assert(t@ === (5, 6));
            assert(false); // FAILS
        }

        tracked struct Tr {
            ghost ints: (int, int),
        }

        fn test3() {
            let mut t: Tracked<Tr> = Tracked(Tr { ints: (4, 6) });
            let mut_ref = &mut t;
            proof { mut_ref.borrow_mut().ints = (5, 10); }
            assert(t@.ints === (5, 10));
        }

        fn test3_fails() {
            let mut t: Tracked<Tr> = Tracked(Tr { ints: (4, 6) });
            let mut_ref = &mut t;
            proof { mut_ref.borrow_mut().ints = (5, 10); }
            assert(t@.ints === (5, 10));
            assert(false); // FAILS
        }

        fn test4() {
            let mut t: Tracked<Tr> = Tracked(Tr { ints: (4, 6) });
            let mut_ref = &mut t;
            proof { mut_ref.borrow_mut().ints.0 = 5; }
            assert(t@.ints === (5, 6));
        }

        fn test4_fails() {
            let mut t: Tracked<Tr> = Tracked(Tr { ints: (4, 6) });
            let mut_ref = &mut t;
            proof { mut_ref.borrow_mut().ints.0 = 5; }
            assert(t@.ints === (5, 6));
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] modify_ghost_fields_doesnt_reinitialize1 ["new-mut-ref"] => verus_code! {
        fn consume<A>(a: A) { }

        fn test<X>(x: X) {
            let y = (x, Ghost(0int));
            consume(y.0);
            proof { *y.1.borrow_mut() = 5int; }

            assert(has_resolved(y.0)); // FAILS
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `y.1` as mutable, as `y` is not declared as mutable")
}

test_verify_one_file_with_options! {
    #[test] modify_ghost_fields_doesnt_reinitialize2 ["new-mut-ref"] => verus_code! {
        fn consume<A>(a: A) { }

        fn test<X>(x: X) {
            let mut y = (x, Ghost(0int));
            consume(y.0);
            proof { *y.1.borrow_mut() = 5int; }

            assert(has_resolved(y.0)); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] dont_resolve_ghost_field ["new-mut-ref"] => verus_code! {
        broadcast proof fn stronger_resolver_axiom<A, B>(pair: TGPair<A, B>)
            ensures #[trigger] has_resolved(pair) ==> has_resolved(pair.t)
        {
        }

        spec fn id<A>(a: A) -> A { a }

        tracked struct TGPair<A, B> {
            tracked t: A,
            ghost g: B,
        }

        fn test1() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let a_ref = &mut a;
            let b_ref = &mut b;

            // We have to be careful here that resolving tmp.t
            // does not also resolve tmp.g (which is a ghost place)

            proof {
                let tracked tg = TGPair { g: id(a_ref), t: b_ref };
                match tg {
                    TGPair { g: _, t } => {
                    }
                }
            }

            broadcast use stronger_resolver_axiom;

            assert(has_resolved(a_ref)); // FAILS

            *a_ref = 20;
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] dont_resolve_ghost_field2 ["new-mut-ref"] => verus_code! {
        broadcast proof fn stronger_resolver_axiom<A, B>(pair: TGPair<A, B>)
            ensures #[trigger] has_resolved(pair) ==> has_resolved(pair.t)
        {
        }

        spec fn id<A>(a: A) -> A { a }

        tracked struct TGPair<A, B> {
            ghost g: B,
            tracked t: A,
        }

        fn test1() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;

            let a_ref = &mut a;
            let b_ref = &mut b;

            // We have to be careful here that resolving tmp.t
            // does not also resolve tmp.g (which is a ghost place)

            proof {
                let tracked tg = TGPair { g: id(a_ref), t: b_ref };
                match tg {
                    TGPair { g: _, t } => {
                    }
                }
            }

            broadcast use stronger_resolver_axiom;

            assert(has_resolved(a_ref)); // FAILS

            *a_ref = 20;
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] resolve_tracked_param_but_not_ghost_param ["new-mut-ref"] => verus_code! {
        proof fn test_tr<T>(tracked m: &mut T) {
            assert(has_resolved(m));
        }

        proof fn test_gho<T>(m: &mut T) {
            assert(has_resolved(m)); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// TODO(new_mut_ref): un-ignore this
test_verify_one_file_with_options! {
    #[ignore] #[test] read_from_borrowed_ghost_location_and_then_assign_to_mut_ref ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x: Ghost<bool> = Ghost(false);

            let r = &mut x;

            let ghost updated_value = x@;

            proof {
                r@ = !updated_value;
            }

            assert(false);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot use `x` because it was mutably borrowed")
}
