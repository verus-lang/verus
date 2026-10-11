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

fn assert_borrowed_as_mut(err: TestErr, var: &str) {
    assert_rust_error_msg(
        err,
        &format!("cannot borrow `{var}` as immutable because it is also borrowed as mutable"),
    )
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
    #[test] test_mut_bor_from_shr_ref code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<&PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                let r = &mut *a; // trying to mutable borrow when the permission is behind a shared borrow
                r.u = 30;
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "cannot borrow `*m` as mutable, as it is behind a `&` reference")
}

test_verify_one_file! {
    #[test] test_assign_from_shr_ref code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<&PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                (*a).u = 30; // trying to assign when the permission is behind a shared borrow
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "cannot borrow `*m` as mutable, as it is behind a `&` reference")
}

test_verify_one_file! {
    #[test] test_assign_op_from_shr_ref code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<&PointsTo<X>>)
            requires m.is_init(), m.ptr() == a, m.value().u < 100,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                (*a).u += 1;
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "cannot borrow `*m` as mutable, as it is behind a `&` reference")
}

test_verify_one_file! {
    #[test] test_mut_ref_while_borrowed code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
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
    }) => Err(err) => assert_rust_error_msg_skip_spec_msgs(err, "cannot borrow `m` as mutable more than once at a time")
}

test_verify_one_file! {
    #[test] test_shr_ref_while_borrowed_mut code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
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
    }) => Err(err) => assert_borrowed_as_mut(err, "m")
}

test_verify_one_file! {
    #[test] test_copy_while_borrowed_mut code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            let tracked m2 = &mut m;

            unsafe {
                let r = (*a).u; // should not be allowed because `m` is borrowed
            }

            let tracked z = m2;
        }
    }) => Err(err) => assert_borrowed_as_mut(err, "m")
}

test_verify_one_file! {
    #[test] test_copy_after_move code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            let tracked m2 = m;

            unsafe {
                let r = (*a).u; // should not be allowed because `m` is moved
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `m`")
}

// Lifetimes of references tied to the permission

test_verify_one_file! {
    #[test] test_mut_ref_extends_perm_borrow code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                let r = &mut *a;
                let tracked m2 = &m; // m is still mutably borrowed via r
                r.u = 30;
            }
        }
    }) => Err(err) => assert_borrowed_as_mut(err, "m")
}

test_verify_one_file! {
    #[test] test_mut_ref_then_copy code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                let r = &mut *a;
                let x = (*a).u; // m is still mutably borrowed via r
                r.u = 30;
            }
        }
    }) => Err(err) => assert_borrowed_as_mut(err, "m")
}

test_verify_one_file! {
    #[test] test_two_mut_refs code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                let r = &mut *a;
                let r2 = &mut (*a).u;
                r.u = 30;
            }
        }
    }) => Err(err) => assert_rust_error_msg_skip_spec_msgs(err, "cannot borrow `m` as mutable more than once at a time")
}

test_verify_one_file! {
    #[test] test_shr_ref_then_assign code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                let r = &*a;
                (*a).u = 20;
                let x = r.u;
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "cannot borrow `m` as mutable because it is also borrowed as immutable")
}

test_verify_one_file! {
    #[test] test_shr_ref_then_move_perm code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                let r = &*a;
                let tracked m2 = m;
                let x = r.u;
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "cannot move out of `m` because it is borrowed")
}

test_verify_one_file! {
    #[test] test_shr_ref_then_copy_ok code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                let r = &*a;
                let y = (*a).u;
                let x = r.u;
                assert(x == y);
            }
        }
    }) => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_scoped_ok code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                let r = &mut *a;
                r.u = 30;
                // r is dead now
                (*a).u = 31;
                let r = &mut *a;
                r.u = 32;
                let x = (*a).u;
                assert(x == 32);
            }
        }
    }) => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_time_travel code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                let r = &mut *a;
                assert(m.value().u == 0); // snapshot of m while it's mutably borrowed
                r.u = 30;
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "cannot borrow `(Verus spec m)` as immutable because it is also borrowed as mutable")
}

test_verify_one_file! {
    #[test] test_shr_ref_time_travel_ok code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                let r = &*a;
                assert(m.value().u == r.u);
                let x = r.u;
            }
        }
    }) => Ok(())
}

test_verify_one_file! {
    #[test] test_two_phase_borrow_unsupported code(verus_code_str! {
        impl X {
            fn set(&mut self, u: u64) {
                self.u = u;
            }
        }

        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                (*a).set(5);
            }
        }
    }) => Err(err) => assert_vir_error_msg(err, "Verus does not yet support two-phase borrows from a raw pointer dereference; consider assigning the mutable reference to a variable first")
}

test_verify_one_file! {
    #[test] test_method_call_explicit_borrow_ok code(verus_code_str! {
        impl X {
            fn set(&mut self, u: u64)
                ensures final(self).u == u,
            {
                self.u = u;
            }

            fn get(&self) -> (res: u64)
                ensures res == self.u,
            {
                self.u
            }
        }

        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            unsafe {
                let r = &mut *a;
                r.set(5);
                let x = (*a).get();
                assert(x == 5);
            }
        }
    }) => Ok(())
}

// Nested pointers: the inner pointers only need to be read

test_verify_one_file! {
    #[test] test_nested_ok code(verus_code_str! {
        fn test(a: *mut Node, Tracked(ma): Tracked<&PointsTo<Node>>, Tracked(mn): Tracked<PointsTo<u64>>)
            requires ma.is_init(), ma.ptr() == a, mn.ptr() == ma.value().next, mn.is_init(),
        {
            #[verifier::permission("a")]
            let tracked ma = ma;
            #[verifier::permission("a.next")]
            let tracked mut mn = mn;
            unsafe {
                *(*a).next = 5;
                let r = *(*a).next;
                assert(r == 5);
                let rf = &mut *(*a).next;
                *rf = 6;
                let rf = &*(*a).next;
                let rf2 = &*(*a).next;
                assert(*rf == 6);
            }
        }

        fn test3(a: *mut Node2,
            Tracked(ma): Tracked<&PointsTo<Node2>>,
            Tracked(mb): Tracked<&PointsTo<Node>>,
            Tracked(mc): Tracked<PointsTo<u64>>,
        )
            requires
                ma.is_init(), ma.ptr() == a,
                mb.is_init(), mb.ptr() == ma.value().next,
                mc.is_init(), mc.ptr() == mb.value().next,
        {
            #[verifier::permission("a")]
            let tracked ma = ma;
            #[verifier::permission("a.next")]
            let tracked mb = mb;
            #[verifier::permission("a.next.next")]
            let tracked mut mc = mc;
            unsafe {
                *(*(*a).next).next = 5;
                let r = *(*(*a).next).next;
                assert(r == 5);
            }
        }
    }) => Ok(())
}

test_verify_one_file! {
    #[test] test_nested_inner_borrowed_mut code(verus_code_str! {
        fn test(a: *mut Node, Tracked(ma): Tracked<PointsTo<Node>>, Tracked(mn): Tracked<PointsTo<u64>>)
            requires ma.is_init(), ma.ptr() == a, mn.ptr() == ma.value().next, mn.is_init(),
        {
            #[verifier::permission("a")]
            let tracked mut ma = ma;
            #[verifier::permission("a.next")]
            let tracked mut mn = mn;
            let tracked r = &mut ma;
            unsafe {
                *(*a).next = 5; // ma is mutably borrowed
            }
            let tracked z = r;
        }
    }) => Err(err) => assert_borrowed_as_mut(err, "ma")
}

test_verify_one_file! {
    #[test] test_nested_inner_moved code(verus_code_str! {
        fn test(a: *mut Node, Tracked(ma): Tracked<PointsTo<Node>>, Tracked(mn): Tracked<PointsTo<u64>>)
            requires ma.is_init(), ma.ptr() == a, mn.ptr() == ma.value().next, mn.is_init(),
        {
            #[verifier::permission("a")]
            let tracked mut ma = ma;
            #[verifier::permission("a.next")]
            let tracked mut mn = mn;
            let tracked z = ma;
            unsafe {
                let r = &*(*a).next; // ma is moved
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `ma`")
}

test_verify_one_file! {
    #[test] test_nested_outer_shr_for_mut_ref code(verus_code_str! {
        fn test(a: *mut Node, Tracked(ma): Tracked<PointsTo<Node>>, Tracked(mn): Tracked<&PointsTo<u64>>)
            requires ma.is_init(), ma.ptr() == a, mn.ptr() == ma.value().next, mn.is_init(),
        {
            #[verifier::permission("a")]
            let tracked mut ma = ma;
            #[verifier::permission("a.next")]
            let tracked mn = mn;
            unsafe {
                let r = &mut *(*a).next; // mn is a shared reference
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "cannot borrow `*mn` as mutable, as it is behind a `&` reference")
}

test_verify_one_file! {
    #[test] test_nested_mut_ref_holds_only_outer code(verus_code_str! {
        fn test(a: *mut Node, Tracked(ma): Tracked<PointsTo<Node>>, Tracked(mn): Tracked<PointsTo<u64>>)
            requires ma.is_init(), ma.ptr() == a, mn.ptr() == ma.value().next, mn.is_init(),
        {
            #[verifier::permission("a")]
            let tracked mut ma = ma;
            #[verifier::permission("a.next")]
            let tracked mut mn = mn;
            unsafe {
                let r = &mut *(*a).next;
                // The inner permission `ma` is only borrowed momentarily
                let tracked ma_ref = &mut ma;
                *r = 5;
            }
        }
    }) => Ok(())
}

test_verify_one_file! {
    #[test] test_nested_mut_ref_holds_outer code(verus_code_str! {
        fn test(a: *mut Node, Tracked(ma): Tracked<PointsTo<Node>>, Tracked(mn): Tracked<PointsTo<u64>>)
            requires ma.is_init(), ma.ptr() == a, mn.ptr() == ma.value().next, mn.is_init(),
        {
            #[verifier::permission("a")]
            let tracked mut ma = ma;
            #[verifier::permission("a.next")]
            let tracked mut mn = mn;
            unsafe {
                let r = &mut *(*a).next;
                let tracked mn_ref = &mn;
                *r = 5;
            }
        }
    }) => Err(err) => assert_borrowed_as_mut(err, "mn")
}

test_verify_one_file! {
    #[test] test_assign_through_ref_in_raw_ptr code(verus_code_str! {
        struct R<'a> {
            r: &'a mut u64,
        }

        fn test<'a>(a: *mut R<'a>, Tracked(m): Tracked<&PointsTo<R<'a>>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked m = m;
            unsafe {
                // Writing through the &mut stored behind the pointer requires unique access
                *(*a).r = 5;
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "cannot borrow `*m` as mutable, as it is behind a `&` reference")
}

// Index expressions

test_verify_one_file! {
    #[test] test_ptr_to_array_ok code(verus_code_str! {
        fn test(a: *mut [u64; 4], Tracked(m): Tracked<PointsTo<[u64; 4]>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;
            unsafe {
                (*a)[1] = 5;
                let x = (*a)[1];
                assert(x == 5);
                let i = 2;
                (*a)[i] = 7;
                let r = &mut (*a)[i];
                *r = 8;
            }
        }
    }) => Ok(())
}

test_verify_one_file! {
    #[test] test_index_moves_perm code(verus_code_str! {
        fn test(a: *mut [u64; 4], Tracked(m): Tracked<PointsTo<[u64; 4]>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;
            unsafe {
                (*a)[{ let tracked t = m; 0 }] = 5;
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `m`")
}

test_verify_one_file! {
    #[test] test_index_moves_perm_copy code(verus_code_str! {
        fn test(a: *mut [u64; 4], Tracked(m): Tracked<PointsTo<[u64; 4]>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;
            unsafe {
                let x = (*a)[{ let tracked t = m; 0 }];
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `m`")
}

test_verify_one_file! {
    #[test] test_index_moves_and_restores_perm code(verus_code_str! {
        fn test(a: *mut [u64; 4], Tracked(m): Tracked<PointsTo<[u64; 4]>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;
            unsafe {
                (*a)[{ let tracked t = m; proof { m = t; } 0 }] = 5;
                let x = (*a)[{ let tracked t = m; proof { m = t; } 1 }];
            }
        }
    }) => Ok(())
}

test_verify_one_file! {
    #[test] test_index_borrows_perm_mut code(verus_code_str! {
        fn test(a: *mut [u64; 4], Tracked(m): Tracked<PointsTo<[u64; 4]>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;
            let tracked mut r: &mut PointsTo<[u64; 4]>;
            unsafe {
                let x = (*a)[{ proof { r = &mut m; } 0 }];
            }
            let tracked z = r;
        }
    }) => Err(err) => assert_borrowed_as_mut(err, "m")
}

test_verify_one_file! {
    #[test] test_mut_ref_into_array_then_index_reads code(verus_code_str! {
        fn test(a: *mut [u64; 4], Tracked(m): Tracked<PointsTo<[u64; 4]>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;
            unsafe {
                let r = &mut (*a)[0];
                let x = (*a)[1];
                *r = 5;
            }
        }
    }) => Err(err) => assert_borrowed_as_mut(err, "m")
}

test_verify_one_file! {
    #[test] test_array_of_ptrs_ok code(verus_code_str! {
        fn test(a: [*mut u64; 4], Tracked(m): Tracked<PointsTo<u64>>)
            requires m.is_init(), m.ptr() == a[1],
        {
            #[verifier::permission("a[?]")]
            let tracked mut m = m;
            unsafe {
                *a[1] = 5;
                let x = *a[1];
                assert(x == 5);
            }
        }
    }) => Ok(())
}

test_verify_one_file! {
    #[test] test_array_of_ptrs_index_moves_perm code(verus_code_str! {
        fn test(a: [*mut u64; 4], Tracked(m): Tracked<PointsTo<u64>>)
            requires m.is_init(), m.ptr() == a[1],
        {
            #[verifier::permission("a[?]")]
            let tracked mut m = m;
            unsafe {
                *a[{ let tracked t = m; 1 }] = 5;
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `m`")
}

test_verify_one_file! {
    #[test] test_ptr_to_array_of_ptrs_ok code(verus_code_str! {
        fn test(a: *mut [*mut u64; 4],
            Tracked(ma): Tracked<&PointsTo<[*mut u64; 4]>>,
            Tracked(m): Tracked<PointsTo<u64>>,
        )
            requires ma.is_init(), ma.ptr() == a, m.is_init(), m.ptr() == ma.value()[1],
        {
            #[verifier::permission("a")]
            let tracked ma = ma;
            #[verifier::permission("a[?]")]
            let tracked mut m = m;
            unsafe {
                *(*a)[1] = 5;
                let x = *(*a)[1];
                assert(x == 5);
            }
        }
    }) => Ok(())
}

test_verify_one_file! {
    #[test] test_ptr_to_array_of_ptrs_index_moves_inner_perm code(verus_code_str! {
        fn test(a: *mut [*mut u64; 4],
            Tracked(ma): Tracked<PointsTo<[*mut u64; 4]>>,
            Tracked(m): Tracked<PointsTo<u64>>,
        )
            requires ma.is_init(), ma.ptr() == a, m.is_init(), m.ptr() == ma.value()[1],
        {
            #[verifier::permission("a")]
            let tracked ma = ma;
            #[verifier::permission("a[?]")]
            let tracked mut m = m;
            unsafe {
                *(*a)[{ let tracked t = ma; 1 }] = 5;
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `ma`")
}

test_verify_one_file! {
    #[test] test_ptr_to_array_of_ptrs_index_borrows_outer_perm code(verus_code_str! {
        fn test(a: *mut [*mut u64; 4],
            Tracked(ma): Tracked<&PointsTo<[*mut u64; 4]>>,
            Tracked(m): Tracked<PointsTo<u64>>,
        )
            requires ma.is_init(), ma.ptr() == a, m.is_init(), m.ptr() == ma.value()[1],
        {
            #[verifier::permission("a")]
            let tracked ma = ma;
            #[verifier::permission("a[?]")]
            let tracked mut m = m;
            let tracked mut r: &mut PointsTo<u64>;
            unsafe {
                *(*a)[{ proof { r = &mut m; } 1 }] = 5;
            }
            let tracked z = r;
        }
    }) => Err(err) => assert_rust_error_msg(err, "cannot borrow `m` as mutable more than once at a time")
}

// Slices. (Verus can't fully verify these yet, so we use `assume(false)` to only test
// lifetime checking.)

test_verify_one_file! {
    #[test] test_slice_ok code(verus_code_str! {
        fn test(a: *mut [u64], Tracked(m): Tracked<PointsTo<[u64]>>) {
            assume(false);
            #[verifier::permission("a")]
            let tracked mut m = m;
            unsafe {
                (*a)[1] = 5;
                let x = (*a)[1];
                let r = &mut (*a)[2];
                *r = 6;
                let i = 3;
                let r = &(*a)[i];
            }
        }

        fn test_shr(a: *mut [u64], Tracked(m): Tracked<&PointsTo<[u64]>>) {
            assume(false);
            #[verifier::permission("a")]
            let tracked m = m;
            unsafe {
                let r = &(*a)[0];
                let x = (*a)[1];
                let y = *r;
            }
        }
    }) => Ok(())
}

test_verify_one_file! {
    #[test] test_slice_index_moves_perm code(verus_code_str! {
        fn test(a: *mut [u64], Tracked(m): Tracked<PointsTo<[u64]>>) {
            assume(false);
            #[verifier::permission("a")]
            let tracked mut m = m;
            unsafe {
                (*a)[{ let tracked t = m; 1 }] = 5;
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `m`")
}

test_verify_one_file! {
    #[test] test_slice_mut_ref_then_read code(verus_code_str! {
        fn test(a: *mut [u64], Tracked(m): Tracked<PointsTo<[u64]>>) {
            assume(false);
            #[verifier::permission("a")]
            let tracked mut m = m;
            unsafe {
                let r = &mut (*a)[0];
                let x = (*a)[1];
                *r = 5;
            }
        }
    }) => Err(err) => assert_borrowed_as_mut(err, "m")
}

test_verify_one_file! {
    #[test] test_slice_assign_from_shr code(verus_code_str! {
        fn test(a: *mut [u64], Tracked(m): Tracked<&PointsTo<[u64]>>) {
            assume(false);
            #[verifier::permission("a")]
            let tracked m = m;
            unsafe {
                (*a)[0] = 5;
            }
        }
    }) => Err(err) => assert_rust_error_msg(err, "cannot borrow `*m` as mutable, as it is behind a `&` reference")
}

// The example from mir-place-notes.md:
// The place `*(*(*a)[i])[j]` gets bounds checks for both `(*a)[i]` (an array) and
// `(*(*a)[i])[j]` (a slice).

const NESTED_SLICES_HEADER: &str = r#"
    fn test(a: *mut [*mut [*mut u64]; 20],
        Tracked(m1): Tracked<PointsTo<[*mut [*mut u64]; 20]>>,
        Tracked(m2): Tracked<PointsTo<[*mut u64]>>,
        Tracked(m3): Tracked<PointsTo<u64>>,
    ) {
        assume(false);
        #[verifier::permission("a")]
        let tracked m1 = m1;
        #[verifier::permission("a[?]")]
        let tracked m2 = m2;
        #[verifier::permission("a[?][?]")]
        let tracked mut m3 = m3;
"#;

fn nested_slices(body: &str) -> String {
    code(&format!("::verus_builtin_macros::verus!{{\n{NESTED_SLICES_HEADER}\n{body}\n}}\n}}\n"))
}

test_verify_one_file! {
    #[test] test_nested_slices_ok nested_slices(code_str! {
            unsafe {
                let x = *(*(*a)[{ let y = 13u64; 0 }])[11];
                *(*(*a)[0])[11] = 7;
                let r = &mut *(*(*a)[0])[11];
                *r = 8;
            }
    }) => Ok(())
}

test_verify_one_file! {
    #[test] test_nested_slices_move_innermost_in_inner_index nested_slices(code_str! {
            unsafe {
                let x = *(*(*a)[{ let tracked t = m1; 0 }])[11];
            }
    }) => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `m1`")
}

test_verify_one_file! {
    #[test] test_nested_slices_move_innermost_in_outer_index nested_slices(code_str! {
            unsafe {
                let x = *(*(*a)[0])[{ let tracked t = m1; 11 }];
            }
    }) => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `m1`")
}

test_verify_one_file! {
    #[test] test_nested_slices_move_middle_in_outer_index nested_slices(code_str! {
            unsafe {
                let x = *(*(*a)[0])[{ let tracked t = m2; 11 }];
            }
    }) => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `m2`")
}

test_verify_one_file! {
    #[test] test_nested_slices_move_outermost_in_outer_index nested_slices(code_str! {
            unsafe {
                *(*(*a)[0])[{ let tracked t = m3; 11 }] = 5;
            }
    }) => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `m3`")
}

test_verify_one_file! {
    #[test] test_nested_slices_borrow_outermost_in_outer_index nested_slices(code_str! {
            let tracked mut r: &PointsTo<u64>;
            unsafe {
                *(*(*a)[0])[{ proof { r = &m3; } 11 }] = 5;
            }
            let tracked z = r;
    }) => Err(err) => assert_rust_error_msg(err, "cannot borrow `m3` as mutable because it is also borrowed as immutable")
}

test_verify_one_file! {
    #[test] test_nested_slices_borrow_outermost_in_outer_index_read_ok nested_slices(code_str! {
            let tracked mut r: &PointsTo<u64>;
            unsafe {
                let x = *(*(*a)[0])[{ proof { r = &m3; } 11 }];
            }
            let tracked z = r;
    }) => Ok(())
}

test_verify_one_file! {
    #[test] test_nested_slices_restore_middle_in_outer_index code(&format!("::verus_builtin_macros::verus!{{\n{}\n}}\n", code_str! {
        fn test(a: *mut [*mut [*mut u64]; 20],
            Tracked(m1): Tracked<PointsTo<[*mut [*mut u64]; 20]>>,
            Tracked(m2): Tracked<PointsTo<[*mut u64]>>,
        ) {
            assume(false);
            #[verifier::permission("a")]
            let tracked m1 = m1;
            #[verifier::permission("a[?]")]
            let tracked mut m2 = m2;
            let tracked t = m2;
            unsafe {
                // m2 is restored by the index expression, which is evaluated before
                // the bounds check and the final read.
                let x = (*(*a)[0])[{ proof { m2 = t; } 11 }];
            }
        }
    })) => Ok(())
}

test_verify_one_file! {
    #[test] test_nested_array_restore_in_index code(&format!("::verus_builtin_macros::verus!{{\n{}\n}}\n", code_str! {
        fn test(a: *mut [*mut [u64; 20]; 20],
            Tracked(m1): Tracked<PointsTo<[*mut [u64; 20]; 20]>>,
            Tracked(m2): Tracked<PointsTo<[u64; 20]>>,
        ) {
            assume(false);
            #[verifier::permission("a")]
            let tracked m1 = m1;
            #[verifier::permission("a[?]")]
            let tracked mut m2 = m2;
            let tracked t = m2;
            unsafe {
                // Same as above, but for an array, where the bounds check does a
                // FakeRead of the array (which requires m2)
                let x = (*(*a)[0])[{ proof { m2 = t; } 11 }];
            }
        }
    })) => Ok(())
}

// Other uses of places

test_verify_one_file! {
    #[test] test_match_scrutinee code(verus_code_str! {
        fn test(a: *mut Option<u64>, Tracked(m): Tracked<PointsTo<Option<u64>>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;
            let tracked r = &mut m;
            unsafe {
                match *a {
                    Some(x) => { }
                    None => { }
                }
            }
            let tracked z = r;
        }
    }) => Err(err) => assert_borrowed_as_mut(err, "m")
}

test_verify_one_file! {
    #[test] test_perm_in_option_borrowed code(verus_code_str! {
        fn test(a: *mut u8, Tracked(m): Tracked<PointsTo<u8>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = Some(m);
            unsafe {
                let r = &mut *a;
                let tracked z = &m;
                *r = 5;
            }
        }
    }) => Err(err) => assert_borrowed_as_mut(err, "m")
}

// Closures

test_verify_one_file! {
    #[test] test_closure_unsupported code(verus_code_str! {
        fn test(a: *mut X, Tracked(m): Tracked<PointsTo<X>>)
            requires m.is_init(), m.ptr() == a,
        {
            #[verifier::permission("a")]
            let tracked mut m = m;

            let f = || {
                unsafe {
                    let x = (*a).u;
                }
            };
        }
    }) => Err(err) => assert_vir_error_msg(err, "Verus does not yet support dereferencing a raw pointer inside a closure using a permission declared outside the closure")
}
