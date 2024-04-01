#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] union_basic verus_code! {
        union U { x: u8, y: bool }

        fn test_ok() {
            let u = U { x: 3 };

            assert(is_variant(u, "x"));
            assert(!is_variant(u, "y"));
            assert(get_union_field::<_, u8>(u, "x") == 3);

            unsafe {
                let j = u.x;
                assert(j == 3);
            }
        }

        fn test_fail() {
            let u = U { x: 3 };

            unsafe {
                let j = u.y; // FAILS
            }
        }

        fn test_fail2() {
            let u = U { x: 3 };

            unsafe {
                proof {
                    let tracked j = &u.y; // FAILS
                }
            }
        }

        fn test_fail3() {
            let u = U { x: 3 };

            unsafe {
                proof {
                    let j = &u.y; // FAILS
                }
            }
        }

        impl U {
            fn test_self_ctor() {
                let u = Self { x: 3 };
                assert(is_variant(u, "x"));
            }
        }

        type U2 = U;

        fn test_type_alias() {
            let u = U2 { x: 3 };
            assert(is_variant(u, "x"));
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] union_pattern verus_code! {
        union U { x: u8, y: bool }

        fn test_fail() {
            let u = U { x: 3 };
            unsafe {
                let U { x } = u;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: using a union here")
}

test_verify_one_file! {
    #[test] union_mut_assign verus_code! {
        union U { x: u8, y: bool }

        fn test_fail() {
            let mut u = U { x: 3 };
            unsafe {
                u.x = 7;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: assigning to or taking &mut of a union field")
}

test_verify_one_file! {
    #[test] union_mut_ref verus_code! {
        union U { x: u8, y: bool }

        fn take_mut_ref(x: &mut u8) { }

        fn test_fail() {
            let mut u = U { x: 3 };
            unsafe {
                take_mut_ref(&mut u.x);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: assigning to or taking &mut of a union field")
}

test_verify_one_file! {
    #[test] get_union_field_non_union verus_code! {
        enum X {
            Foo(u8),
            Stuff(bool),
        }

        fn test_fail(x: X) {
            assert(get_union_field::<_, u8>(x, "Foo") == 5);
        }
    } => Err(err) => assert_vir_error_msg(err, "get_union_field expects a union type")
}

test_verify_one_file! {
    #[test] get_union_field_bad_field_name verus_code! {
        union U { x: u8, y: bool }

        fn test_fail(u: U) {
            assert(get_union_field::<_, u8>(u, "z") == 5);
        }
    } => Err(err) => assert_vir_error_msg(err, "no field `z` for this union")
}

test_verify_one_file! {
    #[test] get_union_field_bad_field_type verus_code! {
        union U { x: u8, y: bool }

        fn test_fail(u: U) {
            assert(get_union_field::<_, u16>(u, "x") == 5);
        }
    } => Err(err) => assert_vir_error_msg(err, "field has the wrong type")
}

test_verify_one_file! {
    #[test] get_union_field_exec_mode_fail verus_code! {
        union U { x: u8, y: bool }

        fn test_fail(u: U) {
            let j = get_union_field::<_, u8>(u, "x");
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot get variant in exec mode")
}

test_verify_one_file! {
    #[test] get_union_field_tracked_mode_fail verus_code! {
        union U { x: u8, y: bool }

        proof fn test_fail(u: U) {
            let tracked j = get_union_field::<_, u8>(u, "x");
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] get_union_field_tracked_mode_fail2 verus_code! {
        union U { x: u8, y: bool }

        proof fn test_fail(tracked u: U) {
            let tracked j = get_union_field::<_, u8>(u, "x");
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] union_generics verus_code! {
        union U<A: Copy, B: Copy> { x: A, y: B }

        fn test_ok() {
            let u = U::<u8, bool> { x: 3 };

            assert(is_variant(u, "x"));
            assert(!is_variant(u, "y"));
            assert(get_union_field::<_, u8>(u, "x") == 3);

            unsafe {
                let j = u.x;
                assert(j == 3);
            }
        }

        fn test_fail() {
            let u = U::<u8, bool> { x: 3 };

            unsafe {
                let j = u.y; // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] tracked_union_not_supported verus_code! {
        tracked union U<A: Copy, B: Copy> { x: A, y: B }
    } => Err(err) => assert_vir_error_msg(err, "a 'union' can only be exec-mode")
}

test_verify_one_file! {
    #[test] ghost_union_not_supported verus_code! {
        tracked union U<A: Copy, B: Copy> { x: A, y: B }
    } => Err(err) => assert_vir_error_msg(err, "a 'union' can only be exec-mode")
}

test_verify_one_file! {
    #[test] tracked_union_field_not_supported verus_code! {
        union U<A: Copy, B: Copy> { tracked x: A, y: B }
    } => Err(err) => assert_vir_error_msg(err, "a union field can only be exec-mode")
}

test_verify_one_file! {
    #[test] ghost_union_field_not_supported verus_code! {
        union U<A: Copy, B: Copy> { ghost x: A, y: B }
    } => Err(err) => assert_vir_error_msg(err, "a union field can only be exec-mode")
}

test_verify_one_file! {
    #[test] tracked_union_not_supported_attr verus_code! {
        #[verifier::spec] union U<A: Copy, B: Copy> { x: A, y: B }
    } => Err(err) => assert_vir_error_msg(err, "a 'union' can only be exec-mode")
}

test_verify_one_file! {
    #[test] ghost_union_not_supported_attr verus_code! {
        #[verifier::proof] union U<A: Copy, B: Copy> { x: A, y: B }
    } => Err(err) => assert_vir_error_msg(err, "a 'union' can only be exec-mode")
}

test_verify_one_file! {
    #[test] tracked_union_field_not_supported_attr verus_code! {
        union U<A: Copy, B: Copy> { #[verifier::proof] x: A, y: B }
    } => Err(err) => assert_vir_error_msg(err, "a union field can only be exec-mode")
}

test_verify_one_file! {
    #[test] ghost_union_field_not_supported_attr verus_code! {
        union U<A: Copy, B: Copy> { #[verifier::spec] x: A, y: B }
    } => Err(err) => assert_vir_error_msg(err, "a union field can only be exec-mode")
}

test_verify_one_file! {
    #[test] lifetime_union verus_code! {
        use vstd::*;
        use core::mem::ManuallyDrop;
        struct X { }
        struct Y { }

        union U {
            x: ManuallyDrop<X>,
            y: ManuallyDrop<Y>,
        }

        fn test(u: U) {
            unsafe {
                let t = u.x;
                let s = u.x;
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `u`")
}

test_verify_one_file! {
    #[test] lifetime_union2 verus_code! {
        use vstd::*;
        use core::mem::ManuallyDrop;
        struct X { }
        struct Y { }

        union U {
            x: ManuallyDrop<X>,
            y: ManuallyDrop<Y>,
        }

        fn test(u: U) {
            unsafe {
                let t = u.x;

                proof {
                    let tracked z = &u.x;
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "borrow of moved value: `u`")
}

test_verify_one_file! {
    #[test] union_proof_mode verus_code! {
        union U { x: u8, y: bool }

        proof fn test_ok() {
            let u = U { x: 3 };

            assert(is_variant(u, "x"));
            assert(!is_variant(u, "y"));
            assert(get_union_field::<_, u8>(u, "x") == 3);

            unsafe {
                let j = u.x;
                assert(j == 3);
            }
        }

        proof fn test_fail(u: U) {
            unsafe {
                let j = u.y; // FAILS
            }
        }

        proof fn test_fail2(tracked u: U) {
            unsafe {
                let tracked j = &u.y; // FAILS
            }
        }

        proof fn test_fail3(u: U) {
            unsafe {
                let j = &u.y; // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] union_mode_error verus_code! {
        union U { x: u8, y: bool }

        proof fn test(u: U) {
            let tracked x = &u.x;
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] union_field_access_in_spec_func verus_code! {
        union U { x: u8, y: bool }

        spec fn test(u: U) -> u8 {
            u.x
        }
    // This error messages could be more specific
    } => Err(err) => assert_vir_error_msg(err, "expected pure mathematical expression")
}

test_verify_one_file! {
    #[ignore] #[test] is_variant verus_code! {
        // TODO support is_variant for unions

        #[is_variant]
        union U { x: u8, y: bool }

        fn test_ok() {
            let u = U { x: 3 };

            assert(u.is_x());
            assert(!u.is_y());
            assert(u.get_x() == 3);

            unsafe {
                let j = u.x;
                assert(j == 3);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] rec_types verus_code! {
        use vstd::*;
        use core::mem::ManuallyDrop;

        #[verifier::reject_recursive_types(T)]
        struct X<T> {
            r: u64,
            g: Ghost<spec_fn(T) -> bool>,
        }

        union U {
            x: u8,
            y: ManuallyDrop<X<U>>,
        }
    } => Err(err) => assert_vir_error_msg(err, "non-positive position")
}

test_verify_one_file! {
    #[test] visibility verus_code! {
        pub union U { x: u8, y: bool }

        pub open spec fn f(u: U) {
            get_union_field::<_, u8>(u, "x");
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot access any field of a datatype where one or more fields are private")
}

test_verify_one_file! {
    #[test] visibility2 verus_code! {
        pub union U { x: u8, pub y: bool }

        pub open spec fn f(b: bool) -> U {
            U { y: b }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use constructor of private datatype or datatype whose fields are private")
}
