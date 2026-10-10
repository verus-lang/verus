#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] match_slice_shr_ref verus_code! {
        use vstd::prelude::*;

        fn test(a: &[u64]) {
            match a {
                [] => {
                    assert(a.len() == 0);
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                }
                _ => {
                    assert(a.len() > 3);
                }
            }
        }

        fn test_fail1(a: &[u64]) {
            match a {
                [] => {
                    assert(a.len() == 0);
                    assert(false); // FAILS
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                }
                _ => {
                    assert(a.len() > 3);
                }
            }
        }

        fn test_fail2(a: &[u64]) {
            match a {
                [] => {
                    assert(a.len() == 0);
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                    assert(false); // FAILS
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                }
                _ => {
                    assert(a.len() > 3);
                }
            }
        }

        fn test_fail3(a: &[u64]) {
            match a {
                [] => {
                    assert(a.len() == 0);
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                    assert(false); // FAILS
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                }
                _ => {
                    assert(a.len() > 3);
                }
            }
        }

        fn test_fail4(a: &[u64]) {
            match a {
                [] => {
                    assert(a.len() == 0);
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                    assert(false); // FAILS
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                }
                _ => {
                    assert(a.len() > 3);
                }
            }
        }

        fn test_fail5(a: &[u64]) {
            match a {
                [] => {
                    assert(a.len() == 0);
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                    assert(false); // FAILS
                }
                _ => {
                    assert(a.len() > 3);
                }
            }
        }

        fn test_fail6(a: &[u64]) {
            match a {
                [] => {
                    assert(a.len() == 0);
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                }
                _ => {
                    assert(a.len() > 3);
                    assert(false); // FAILS
                }
            }
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file! {
    #[test] match_slice_box verus_code! {
        use vstd::prelude::*;

        fn test(a: Box<[u64]>) {
            match *a {
                [] => {
                    assert(a.len() == 0);
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                }
                _ => {
                    assert(a.len() > 3);
                }
            }
        }

        fn test_fail1(a: Box<[u64]>) {
            match *a {
                [] => {
                    assert(a.len() == 0);
                    assert(false); // FAILS
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                }
                _ => {
                    assert(a.len() > 3);
                }
            }
        }

        fn test_fail2(a: Box<[u64]>) {
            match *a {
                [] => {
                    assert(a.len() == 0);
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                    assert(false); // FAILS
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                }
                _ => {
                    assert(a.len() > 3);
                }
            }
        }

        fn test_fail3(a: Box<[u64]>) {
            match *a {
                [] => {
                    assert(a.len() == 0);
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                    assert(false); // FAILS
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                }
                _ => {
                    assert(a.len() > 3);
                }
            }
        }

        fn test_fail4(a: Box<[u64]>) {
            match *a {
                [] => {
                    assert(a.len() == 0);
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                    assert(false); // FAILS
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                }
                _ => {
                    assert(a.len() > 3);
                }
            }
        }

        fn test_fail5(a: Box<[u64]>) {
            match *a {
                [] => {
                    assert(a.len() == 0);
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                    assert(false); // FAILS
                }
                _ => {
                    assert(a.len() > 3);
                }
            }
        }

        fn test_fail6(a: Box<[u64]>) {
            match *a {
                [] => {
                    assert(a.len() == 0);
                }
                [x] => {
                    assert(a.len() == 1 && a[0] == x);
                }
                [x, 1] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == 1);
                }
                [x, y] => {
                    assert(a.len() == 2 && a[0] == x && a[1] == y && y != 1);
                }
                [x, y, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == y && a[2] == z);
                }
                _ => {
                    assert(a.len() > 3);
                    assert(false); // FAILS
                }
            }
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file! {
    #[test] match_slice_mut_ref_bind_by_copy verus_code! {
        use vstd::prelude::*;

        fn test(a: &mut [u64]) {
            match *a {
                [] => {
                    assert(a.len() == 0);
                }
                [x, 1, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == 1 && a[2] == z);
                }
                _ => {
                    assert((a.len() != 0 && a.len() != 3) || (a.len() == 3 && a[1] != 1));
                }
            }
        }

        fn test_fails(a: &mut [u64]) {
            match *a {
                [] => {
                    assert(a.len() == 0);
                    assert(false); // FAILS
                }
                [x, 1, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == 1 && a[2] == z);
                    assert(false); // FAILS
                }
                _ => {
                    assert((a.len() != 0 && a.len() != 3) || (a.len() == 3 && a[1] != 1));
                }
            }
        }

        fn test_fails2(a: &mut [u64]) {
            match *a {
                [] => {
                    assert(a.len() == 0);
                }
                [x, 1, z] => {
                    assert(a.len() == 3 && a[0] == x && a[1] == 1 && a[2] == z);
                }
                _ => {
                    assert((a.len() != 0 && a.len() != 3) || (a.len() == 3 && a[1] != 1));
                    assert(false); // FAILS
                }
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] match_slice_mut_ref_bind_by_mut verus_code! {
        use vstd::prelude::*;

        fn test(a: &mut [u64]) {
            let ghost old_a = &*a;
            match a {
                [] => {
                    assert(old_a.len() == 0);
                }
                [x, 1, z] => {
                    assert(old_a.len() == 3 && old_a[0] == *x && old_a[1] == 1 && old_a[2] == *z);
                    *x = 20;
                    *z = 40;
                }
                _ => {
                    assert((old_a.len() != 0 && old_a.len() != 3) || (old_a.len() == 3 && old_a[1] != 1));
                }
            }

            assert(old(a).len() == 3 && old(a)[1] == 1 ==>
                a.len() == 3 && a[0] == 20 && a[2] == 40);
            assert(old(a).len() == 0 ==> a.len() == 0);
            assert((a.len() != 0 && a.len() != 3) || (a.len() == 3 && a[1] != 1) ==> old(a)@ == a@);
        }

        fn test_fails1(a: &mut [u64]) {
            let ghost old_a = &*a;
            match a {
                [] => {
                    assert(old_a.len() == 0);
                }
                [x, 1, z] => {
                    assert(old_a.len() == 3 && old_a[0] == *x && old_a[1] == 1 && old_a[2] == *z);
                    *x = 20;
                    *z = 40;
                }
                _ => {
                    assert((old_a.len() != 0 && old_a.len() != 3) || (old_a.len() == 3 && old_a[1] != 1));
                }
            }

            assert(old(a).len() == 3 && old(a)[1] == 1 ==> false); // FAILS
        }

        fn test_fails2(a: &mut [u64]) {
            let ghost old_a = &*a;
            match a {
                [] => {
                    assert(old_a.len() == 0);
                }
                [x, 1, z] => {
                    assert(old_a.len() == 3 && old_a[0] == *x && old_a[1] == 1 && old_a[2] == *z);
                    *x = 20;
                    *z = 40;
                }
                _ => {
                    assert((old_a.len() != 0 && old_a.len() != 3) || (old_a.len() == 3 && old_a[1] != 1));
                }
            }

            assert(old(a).len() == 0 ==> false); // FAILS
        }

        fn test_fails3(a: &mut [u64]) {
            let ghost old_a = &*a;
            match a {
                [] => {
                    assert(old_a.len() == 0);
                }
                [x, 1, z] => {
                    assert(old_a.len() == 3 && old_a[0] == *x && old_a[1] == 1 && old_a[2] == *z);
                    *x = 20;
                    *z = 40;
                }
                _ => {
                    assert((old_a.len() != 0 && old_a.len() != 3) || (old_a.len() == 3 && old_a[1] != 1));
                }
            }

            assert((a.len() != 0 && a.len() != 3) || (a.len() == 3 && a[1] != 1) ==> false); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] match_slice_box_bind_by_mut verus_code! {
        use vstd::prelude::*;

        fn test(mut a: Box<[u64]>) {
            let ghost old_a = &*a;
            match *a {
                [] => {
                    assert(old_a.len() == 0);
                }
                [ref mut x, 1, ref mut z] => {
                    assert(old_a.len() == 3 && old_a[0] == *x && old_a[1] == 1 && old_a[2] == *z);
                    *x = 20;
                    *z = 40;
                }
                _ => {
                    assert((old_a.len() != 0 && old_a.len() != 3) || (old_a.len() == 3 && old_a[1] != 1));
                }
            }

            assert(old_a.len() == 3 && old_a[1] == 1 ==>
                a.len() == 3 && a[0] == 20 && a[2] == 40);
            assert(old_a.len() == 0 ==> a.len() == 0);
            assert((a.len() != 0 && a.len() != 3) || (a.len() == 3 && a[1] != 1) ==> old_a@ == a@);
        }

        fn test_fails1(mut a: Box<[u64]>) {
            let ghost old_a = &*a;
            match *a {
                [] => {
                    assert(old_a.len() == 0);
                }
                [ref mut x, 1, ref mut z] => {
                    assert(old_a.len() == 3 && old_a[0] == *x && old_a[1] == 1 && old_a[2] == *z);
                    *x = 20;
                    *z = 40;
                }
                _ => {
                    assert((old_a.len() != 0 && old_a.len() != 3) || (old_a.len() == 3 && old_a[1] != 1));
                }
            }

            assert(old_a.len() == 3 && old_a[1] == 1 ==> false); // FAILS
        }

        fn test_fails2(mut a: Box<[u64]>) {
            let ghost old_a = &*a;
            match *a {
                [] => {
                    assert(old_a.len() == 0);
                }
                [ref mut x, 1, ref mut z] => {
                    assert(old_a.len() == 3 && old_a[0] == *x && old_a[1] == 1 && old_a[2] == *z);
                    *x = 20;
                    *z = 40;
                }
                _ => {
                    assert((old_a.len() != 0 && old_a.len() != 3) || (old_a.len() == 3 && old_a[1] != 1));
                }
            }

            assert(old_a.len() == 0 ==> false); // FAILS
        }

        fn test_fails3(mut a: Box<[u64]>) {
            let ghost old_a = &*a;
            match *a {
                [] => {
                    assert(old_a.len() == 0);
                }
                [ref mut x, 1, ref mut z] => {
                    assert(old_a.len() == 3 && old_a[0] == *x && old_a[1] == 1 && old_a[2] == *z);
                    *x = 20;
                    *z = 40;
                }
                _ => {
                    assert((old_a.len() != 0 && old_a.len() != 3) || (old_a.len() == 3 && old_a[1] != 1));
                }
            }

            assert((a.len() != 0 && a.len() != 3) || (a.len() == 3 && a[1] != 1) ==> false); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] match_slice_box_bind_by_move verus_code! {
        use vstd::prelude::*;

        struct X { }

        // Moving out of a non-copy slice is disallowed.
        // If this were allowed, it would need consideration in resolution_inference,
        // so this test catches it in case some future version of Rust supports this.
        fn test(a: Box<[X]>) {
            match *a {
                [] => {
                }
                [x, _, z] => {
                }
                _ => { }
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of type `[X]`, a non-copy slice")
}

test_verify_one_file! {
    #[test] match_slice_box_bind_by_move_tracked verus_code! {
        use vstd::prelude::*;

        struct X { }

        // Moving out of a non-copy slice is disallowed.
        // If this were allowed, it would need consideration in resolution_inference,
        // so this test catches it in case some future version of Rust supports this.
        proof fn test(tracked a: Box<[X]>) {
            match *a {
                [] => {
                }
                [x, _, z] => {
                }
                _ => { }
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of type `[X]`, a non-copy slice")
}

test_verify_one_file! {
    #[test] match_slice_with_tracked verus_code! {
        use vstd::prelude::*;

        struct X { }

        proof fn consume(tracked x: &X) { }

        proof fn test(tracked a: &[X]) {
            match a {
                [x] => {
                    consume(x);
                }
                _ => { }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] match_slice_with_tracked2 verus_code! {
        use vstd::prelude::*;

        struct X { }

        proof fn consume(tracked x: &X) { }

        proof fn test(a: &[X]) {
            match a {
                [x] => {
                    consume(x);
                }
                _ => { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] match_slice_with_tracked_mut verus_code! {
        use vstd::prelude::*;

        struct X { i: Ghost<u64> }

        proof fn update_m(tracked x: &mut X)
            ensures final(x).i == 20,
        {
            x.i = Ghost(20);
        }

        proof fn test(tracked a: &mut [X])
            requires a.len() == 1 && a[0].i == 5,
        {
            match a {
                [x] => {
                    update_m(x);
                }
                _ => { }
            }
            assert(a.len() == 1 && a[0].i == 20);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] match_slice_with_spec_mut verus_code! {
        use vstd::prelude::*;
        struct X { }
        proof fn test(a: &mut [X])
        {
            match a {
                [x] => {
                }
                _ => { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a 'mut ref' binding in a pattern is not allowed in spec mode")
}

test_verify_one_file! {
    #[test] match_slice_in_spec verus_code! {
        use vstd::prelude::*;
        spec fn foo(a: &[u64]) -> Option<u64> {
            match a {
                [] => None,
                [x] => Some(*x),
                [x, y] => Some(2),
                _ => None,
            }
        }

        fn test() {
            assert(foo(&[]) == None);
            assert(foo(&[4]) == Some(4));
            assert(foo(&[4, 5]) == Some(2));
            assert(foo(&[4, 5, 6]) == None);
        }
    } => Ok(())
}
