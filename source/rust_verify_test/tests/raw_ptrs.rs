#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] basics verus_code! {
        use vstd::prelude::*;
        use vstd::raw_ptr::*;

        fn test_mut_const_casts(x: *mut u8) {
            let y = x as *const u8;
            let z = y as *const u8;
            assert(z == x);
            assert(z == y);
        }

        fn test_addr_doesnt_imply_eq(x: *mut u8, y: *mut u8) {
            assume(x@.addr == y@.addr);
            assert(x == y); // FAILS
        }

        fn test_view_does_imply_eq(x: *mut u8, y: *mut u8) {
            assume(x@ == y@);
            assert(x == y);
        }

        fn test_view_does_imply_eq_const(x: *const u8, y: *const u8) {
            assume(x@ == y@);
            assert(x == y);
        }

        fn test_null() {
            let x: *const u8 = core::ptr::null();
            let y: *mut u8 = core::ptr::null_mut();
            assert(x == y);
            assert(x@.addr == 0);
        }

        fn test_manipulating(x: *mut u8, Tracked(pt): Tracked<PointsTo<u8>>) {
            let tracked mut pt = pt;

            assume(x == pt.ptr());
            assume(pt.is_uninit());

            ptr_mut_write(x, Tracked(&mut pt), 20);

            assert(x == pt.ptr());
            assert(pt.is_init());
            assert(pt.value() == 20);

            let val = ptr_ref(x, Tracked(&pt));

            assert(val == 20);

            let val = ptr_mut_read(x, Tracked(&mut pt));

            assert(val == 20);
            assert(x == pt.ptr());
            assert(pt.is_uninit());
        }

        fn test_manipulating2(x: *mut u8, Tracked(pt): Tracked<PointsTo<u8>>) {
            let tracked mut pt = pt;

            assume(x == pt.ptr());
            assume(pt.is_uninit());

            ptr_mut_write(x, Tracked(&mut pt), 20);

            assert(x == pt.ptr());
            assert(pt.is_init());
            assert(pt.value() == 20);

            let val = ptr_ref(x, Tracked(&pt));

            assert(val == 20);

            let val = ptr_mut_read(x, Tracked(&mut pt));

            assert(val == 20);
            assert(x == pt.ptr());
            assert(pt.is_uninit());

            assert(false); // FAILS
        }

        fn test_ptr_mut_write_different(x: *mut u8, Tracked(pt): Tracked<PointsTo<u8>>) {
            let tracked mut pt = pt;
            assume(pt.is_uninit());
            ptr_mut_write(x, Tracked(&mut pt), 20); // FAILS
        }

        fn test_ptr_mut_read_different(x: *mut u8, Tracked(pt): Tracked<PointsTo<u8>>) {
            let tracked mut pt = pt;
            assume(pt.is_init());
            let _ = ptr_mut_read(x, Tracked(&mut pt)); // FAILS
        }

        fn test_ptr_ref_different(x: *mut u8, Tracked(pt): Tracked<PointsTo<u8>>) {
            assume(pt.is_init());
            let _ = ptr_ref(x, Tracked(&pt)); // FAILS
        }

        fn test_ptr_mut_read_uninit(x: *mut u8, Tracked(pt): Tracked<PointsTo<u8>>) {
            let tracked mut pt = pt;
            assume(pt.ptr() == x);
            let _ = ptr_mut_read(x, Tracked(&mut pt)); // FAILS
        }

        fn test_ptr_ref_uninit(x: *mut u8, Tracked(pt): Tracked<PointsTo<u8>>) {
            assume(pt.ptr() == x);
            let _ = ptr_ref(x, Tracked(&pt)); // FAILS
        }

        fn cast_test(x: *mut u8) {
            let y = x as *mut u16;
            assert(y@.addr == x@.addr);
            assert(y@.provenance == x@.provenance);
            assert(y@.metadata == vstd::raw_ptr::Metadata::Thin);
        }

        fn cast_test2(x: *mut [u8]) {
            let y = x as *mut u16;
            assert(y@.addr == x@.addr);
            assert(y@.provenance == x@.provenance);
            assert(y@.metadata == vstd::raw_ptr::Metadata::Thin);
        }

        fn cast_test3(x: *mut [u64; 16]) {
            let y = x as *mut [u64];
            assert(y@.addr == x@.addr);
            assert(y@.provenance == x@.provenance);
            assert(y@.metadata == vstd::raw_ptr::Metadata::Length(16));
        }

        proof fn cast_proof_test(x: *mut u8) {
            let y = x as *mut u16;
            assert(y@.addr == x@.addr);
            assert(y@.provenance == x@.provenance);
            assert(y@.metadata == vstd::raw_ptr::Metadata::Thin);
        }

        proof fn cast_proof_test2(x: *mut [u8]) {
            let y = x as *mut u16;
            assert(y@.addr == x@.addr);
            assert(y@.provenance == x@.provenance);
            assert(y@.metadata == vstd::raw_ptr::Metadata::Thin);
        }

        proof fn cast_proof_test3(x: *mut [u64; 16]) {
            let y = x as *mut [u64];
            assert(y@.addr == x@.addr);
            assert(y@.provenance == x@.provenance);
            assert(y@.metadata == vstd::raw_ptr::Metadata::Length(16));
        }

        fn test_strict_provenance(a: *mut u64) {
            let ad = a.addr();
            assert(ad == a@.addr);

            let b = a.with_addr(7);
            assert(b@.addr == 7);
            assert(b@.provenance == a@.provenance);
            assert(b@.metadata == a@.metadata);

            assert(a == b); // FAILS
        }

        fn test_strict_provenance_const(a: *const u64) {
            let ad = a.addr();
            assert(ad == a@.addr);

            let b = a.with_addr(7);
            assert(b@.addr == 7);
            assert(b@.provenance == a@.provenance);
            assert(b@.metadata == a@.metadata);
        }

    } => Err(err) => assert_fails(err, 8)
}

test_verify_one_file! {
    #[test] pointer_cast_to_ints verus_code! {
        use vstd::prelude::*;
        use vstd::raw_ptr::*;

        proof fn test<T>(x: *mut T) {
            assert(x@.addr == x as int);
            assert(x@.addr == x as nat);
            assert(x@.addr == x as usize);
            assert(x@.addr as u16 == x as u16);
        }

        proof fn test_fails<T>(x: *mut T) {
            assert(x@.addr == x as u16); // FAILS
        }

        proof fn test_fails2<T>(x: *mut T) {
            assert(x@.addr == x as isize); // FAILS
        }

        fn exec_test<T>(x: *mut T) {
            let x1 = x as usize;
            assert(x@.addr == x1);

            let x2 = x as u16;
            assert(x@.addr as u16 == x2);
        }

        fn exec_test_fails<T>(x: *mut T) {
            let x1 = x as u16;
            assert(x@.addr == x1); // FAILS
        }

        fn exec_test_fails2<T>(x: *mut T) {
            let x1 = x as isize;
            assert(x@.addr == x1); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] pointer_exec_eq_is_not_spec_eq verus_code! {
        fn test_const_eq(x: *const u8, y: *const u8) {
            if x == y {
                assert(x == y); // FAILS
            }
        }

        fn test_mut_eq(x: *mut u8, y: *mut u8) {
            if x == y {
                assert(x == y); // FAILS
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: ==/!= for non smt equality types")
}

test_verify_one_file! {
    #[test] points_to_move_error verus_code! {
        use vstd::prelude::*;
        use vstd::raw_ptr::*;

        fn test(Tracked(pt): Tracked<PointsTo<u8>>) {
        }

        fn test2(Tracked(pt): Tracked<PointsTo<u8>>) {
            test(Tracked(pt));
            test(Tracked(pt));
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value: `pt`")
}

test_verify_one_file! {
    #[test] ptr_ref_lifetime_error verus_code! {
        use vstd::prelude::*;
        use vstd::raw_ptr::*;

        fn test(Tracked(pt): Tracked<PointsTo<u8>>) {
        }

        fn test2(x: *mut u8, Tracked(pt): Tracked<PointsTo<u8>>) {
            assume(pt.is_init());
            assume(pt.ptr() == x);
            let y = ptr_ref(x, Tracked(&pt));

            test(Tracked(pt));

            let z = *y;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot move out of `pt` because it is borrowed")
}

test_verify_one_file! {
    #[test] not_supported_int_to_ptr_cast verus_code! {
        fn test(x: usize) {
            let y = x as *mut u8;
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not support this cast")
}

test_verify_one_file! {
    #[test] not_supported_deref_ptr verus_code! {
        pub fn run(x: *mut u8) {
            unsafe { let y = *x; }
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: dereferencing a raw pointer")
}
