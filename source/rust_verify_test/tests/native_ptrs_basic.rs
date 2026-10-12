#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const PRELUDE: &str = verus_code_str! {
    use vstd::prelude::*;
    use vstd::raw_ptr::PointsTo;

    struct X {
        u: u64,
    }

    struct Node {
        next: *mut u64,
        v: u64,
    }

    struct Node2 {
        next: *mut Node,
    }

    struct Pair {
        a: u64,
        b: u64,
    }
};

fn code(s: &str) -> String {
    PRELUDE.to_string() + s
}

// Basic tests

test_verify_one_file! {
    #[test] test_basic code(verus_code_str! {
        fn test(a: *mut u8, Tracked(m): Tracked<PointsTo<u8>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                *a = 20;
                let r = *a;
                assert(r == 20);
            }
        }

        fn test_copy(a: *mut u8, Tracked(m): Tracked<PointsTo<u8>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                let r = *a;
                let q = *a;
            }
        }

        fn test_copy_shared_perm(a: *mut u8, Tracked(m): Tracked<&PointsTo<u8>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked m = m;

            unsafe {
                let r = *a;
                let q = *a;
            }
        }

        fn test_mut_ref(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                let r = &mut *a;
                r.u = 30;
            }
        }

        fn test_mut_ref_perm_mut_ref(a: *mut X, Tracked(m): Tracked<&mut PointsTo<X>>)
            requires old(m).is_init(), old(m).ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked m = m;

            unsafe {
                let r = &mut *a;
                r.u = 30;
                (*a).u = 31;
            }
        }

        fn test_shr_ref_while_borrowed_shr(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            let tracked m2 = &m;

            unsafe {
                let r = &*a; // this is fine, multiple shared refs are allowed
                let r2 = &(*a).u;
                let x = r.u;
            }

            let tracked z = m2;
        }

        fn test_array(a: [*mut u8; 20], Tracked(m): Tracked<PointsTo<u8>>)
            requires m.is_init(), m.ptr() == a[2],
        {
            #[verifier::permission("a[?]")]
            let tracked mut m = m;

            unsafe {
                *(a[2]) = 20;
                let r = *(a[2]);
                assert(r == 20);
            }
        }

        fn test_option(a: *mut u8, Tracked(m): Tracked<PointsTo<u8>>)
            requires m.is_init(), m.ptr() == a,
        {
            // Here, the permission "place" is a field accessor of m, `m->Some_0`
            #[verifier::permission("a")]
            let tracked mut m = Some(m);

            unsafe {
                *a = 20;
                let r = *a;
                assert(r == 20);
            }
        }

        fn test_field_assign(a: *mut Pair, Tracked(m): Tracked<PointsTo<Pair>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                (*a).a = 1;
                (*a).b = 2;
                (*a).a += 1;
                let x = (*a).a;
                assert(x == 2);
            }
        }
    }) => Ok(())
}

test_verify_one_file! {
    #[test] mode_local verus_code!{
        use vstd::prelude::*;
        use vstd::raw_ptr::*;
        struct X { }

        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let ghost mut m = m;

            unsafe {
                let r = *a;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "the permission (`m`) used for this raw ptr operation must be a tracked place (local variable `m` is ghost mode)")
}

test_verify_one_file! {
    #[test] mode_local2 verus_code!{
        use vstd::prelude::*;
        use vstd::raw_ptr::*;
        struct X { }

        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let ghost mut m = Some(m);

            unsafe {
                let r = *a;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "the permission (`m.0`) used for this raw ptr operation must be a tracked place (local variable `m` is ghost mode)")
}

test_verify_one_file! {
    #[test] mode_exec_points_to_ok verus_code!{
        use vstd::prelude::*;
        use vstd::raw_ptr::*;
        struct X { }

        fn test(a: *mut u64, m: Tracked<PointsTo<u64>>)
            requires m.is_init(), m.ptr() == a, m.value() == 1,
        {
            #[verifier::permission("a")]
            let mut m = m;

            unsafe {
                let r = *a;
                assert(r == 1);

                *a = 2;
                let q = *a;
                assert(q == 2);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mode_exec_points_to_with_ghost_fail verus_code!{
        use vstd::prelude::*;
        use vstd::raw_ptr::*;
        struct X { }

        fn test(a: *mut u64, m: Ghost<PointsTo<u64>>)
            requires m.is_init(), m.ptr() == a, m.value() == 1,
        {
            #[verifier::permission("a")]
            let mut m = m;

            unsafe {
                let r = *a;
                assert(r == 1);

                *a = 2;
                let q = *a;
                assert(q == 1);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "place of type `Ghost<vstd::raw_ptr::PointsTo<u64>>` is not accepted for the `verifier::permission` annotation")
}

test_verify_one_file! {
    #[test] type_match_fail verus_code!{
        use vstd::prelude::*;
        use vstd::raw_ptr::*;
        struct X { }

        fn test(a: *mut u32, m: Tracked<PointsTo<u64>>)
            requires m.is_init(), m.value() == 1,
        {
            #[verifier::permission("a")]
            let mut m = m;

            unsafe {
                let r = *a;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "permission is for type u64, expected u32")
}

test_verify_one_file! {
    #[test] read_init_fail verus_code!{
        use vstd::prelude::*;
        use vstd::raw_ptr::*;

        fn test(a: *mut u64, m: Tracked<PointsTo<u64>>)
            requires m.ptr() == a,
        {
            #[verifier::permission("a")]
            let mut m = m;

            unsafe {
                let r = *a;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "unable to prove the `PointsTo` is initialized")
}

test_verify_one_file! {
    #[test] write_init_fail verus_code!{
        use vstd::prelude::*;
        use vstd::raw_ptr::*;

        fn test(a: *mut u64, m: Tracked<PointsTo<u64>>)
            requires m.ptr() == a,
        {
            #[verifier::permission("a")]
            let mut m = m;

            unsafe {
                // TODO: I guess this would actually be ok since the type is Copy
                // which means there's no Drop
                *a = 1;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "unable to prove the `PointsTo` is initialized")
}

test_verify_one_file! {
    #[test] mut_ref_init_fail verus_code!{
        use vstd::prelude::*;
        use vstd::raw_ptr::*;

        fn test(a: *mut u64, m: Tracked<PointsTo<u64>>)
            requires m.ptr() == a,
        {
            #[verifier::permission("a")]
            let mut m = m;

            unsafe {
                let j = &mut *a;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "unable to prove the `PointsTo` is initialized")
}

test_verify_one_file! {
    #[test] shr_ref_init_fail verus_code!{
        use vstd::prelude::*;
        use vstd::raw_ptr::*;

        fn test(a: *mut u64, m: Tracked<PointsTo<u64>>)
            requires m.ptr() == a,
        {
            #[verifier::permission("a")]
            let mut m = m;

            unsafe {
                let j = &*a;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "unable to prove the `PointsTo` is initialized")
}

test_verify_one_file! {
    #[test] read_ptr_fail verus_code!{
        use vstd::prelude::*;
        use vstd::raw_ptr::*;

        fn test(a: *mut u64, m: Tracked<PointsTo<u64>>)
            requires m.is_init()
        {
            #[verifier::permission("a")]
            let mut m = m;

            unsafe {
                let r = *a;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "unable to prove the pointer agrees with the given `PointsTo`")
}

test_verify_one_file! {
    #[test] write_ptr_fail verus_code!{
        use vstd::prelude::*;
        use vstd::raw_ptr::*;

        fn test(a: *mut u64, m: Tracked<PointsTo<u64>>)
            requires m.is_init()
        {
            #[verifier::permission("a")]
            let mut m = m;

            unsafe {
                // TODO: I guess this would actually be ok since the type is Copy
                // which means there's no Drop
                *a = 1;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "unable to prove the pointer agrees with the given `PointsTo`")
}

test_verify_one_file! {
    #[test] mut_ref_ptr_fail verus_code!{
        use vstd::prelude::*;
        use vstd::raw_ptr::*;

        fn test(a: *mut u64, m: Tracked<PointsTo<u64>>)
            requires m.is_init()
        {
            #[verifier::permission("a")]
            let mut m = m;

            unsafe {
                let j = &mut *a;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "unable to prove the pointer agrees with the given `PointsTo`")
}

test_verify_one_file! {
    #[test] shr_ref_ptr_fail verus_code!{
        use vstd::prelude::*;
        use vstd::raw_ptr::*;

        fn test(a: *mut u64, m: Tracked<PointsTo<u64>>)
            requires m.is_init()
        {
            #[verifier::permission("a")]
            let mut m = m;

            unsafe {
                let j = &*a;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "unable to prove the pointer agrees with the given `PointsTo`")
}
