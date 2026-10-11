use vstd::prelude::*;
use vstd::raw_ptr::PointsTo;

verus!{

    // Basic example
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

    // A non-copy type
    struct X {
        u: u64,
    }

/*
    fn test_move(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
        requires m.is_init(), m.ptr() == a,
    {
        #[verifier::permission("a")]
        let tracked mut m = m;

        unsafe {
            let r = *a; // cannot move out of `*a` which is behind a raw pointer
        }
    }
*/

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

    fn test_mut_bor_from_shr_ref(a: *mut X, Tracked(m): Tracked<&PointsTo<X>>)
        requires m.is_init(), m.ptr() == a,
    {
        #[verifier::permission("a")]
        let tracked mut m = m;

        unsafe {
            let r = &mut *a; // this should fail: trying to mutable borrow when the permission is behind a shared borrow
            r.u = 30;
        }
    }

    fn test_assign_from_shr_ref(a: *mut X, Tracked(m): Tracked<&PointsTo<X>>)
        requires m.is_init(), m.ptr() == a,
    {
        #[verifier::permission("a")]
        let tracked mut m = m;

        unsafe {
            (*a).u = 30; // this should fail: trying to assign when the permission is behind a shared borrow
        }
    }

    fn test_mut_ref_while_borrowed(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
        requires m.is_init(), m.ptr() == a,
    {
        #[verifier::permission("a")]
        let tracked mut m = m;

        let tracked m2 = &mut m;

        unsafe {
            let r = &mut *a; // should not be allowed because `m` is borrowed
            r.u = 30;
        }

        let tracked z = m2;
    }

    fn test_shr_ref_while_borrowed_mut(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
        requires m.is_init(), m.ptr() == a,
    {
        #[verifier::permission("a")]
        let tracked mut m = m;

        let tracked m2 = &mut m;

        unsafe {
            let r = &*a; // should not be allowed because `m` is borrowed
        }

        let tracked z = m2;
    }

    fn test_shr_ref_while_borrowed_shr(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
        requires m.is_init(), m.ptr() == a,
    {
        #[verifier::permission("a")]
        let tracked mut m = m;

        let tracked m2 = &m;

        unsafe {
            let r = &*a; // this is fine, multiple shared refs are allowed
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
            let r = *(a[2]); // all ok
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
            let r = *a; // all ok
            assert(r == 20);
        }
    }


}
