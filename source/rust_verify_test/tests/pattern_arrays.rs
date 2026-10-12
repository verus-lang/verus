#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] match_array_shr_ref verus_code! {
        use vstd::prelude::*;

        fn test(a: &[u64; 4]) {
            match a {
                [x, y, 1, w] => {
                    assert(a[0] == x);
                    assert(a[1] == y);
                    assert(a[2] == 1);
                    assert(a[3] == w);
                }
                [x, y, z, w] => {
                    assert(a[0] == x);
                    assert(a[1] == y);
                    assert(a[2] == z);
                    assert(a[3] == w);
                    assert(z != 1);
                }
            }
        }

        fn test_fails(a: &[u64; 4]) {
            match a {
                [x, y, 1, w] => {
                    assert(a[0] == x);
                    assert(a[1] == y);
                    assert(a[2] == 1);
                    assert(a[3] == w);
                    assert(false); // FAILS
                }
                [x, y, z, w] => {
                    assert(a[0] == x);
                    assert(a[1] == y);
                    assert(a[2] == z);
                    assert(a[3] == w);
                    assert(z != 1);
                    assert(false); // FAILS
                }
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] match_array_plain verus_code! {
        use vstd::prelude::*;

        fn test(a: [u64; 4]) {
            match a {
                [x, y, 1, w] => {
                    assert(a[0] == x);
                    assert(a[1] == y);
                    assert(a[2] == 1);
                    assert(a[3] == w);
                }
                [x, y, z, w] => {
                    assert(a[0] == x);
                    assert(a[1] == y);
                    assert(a[2] == z);
                    assert(a[3] == w);
                    assert(z != 1);
                }
            }
        }

        fn test_fails(a: &[u64; 4]) {
            match a {
                [x, y, 1, w] => {
                    assert(a[0] == x);
                    assert(a[1] == y);
                    assert(a[2] == 1);
                    assert(a[3] == w);
                    assert(false); // FAILS
                }
                [x, y, z, w] => {
                    assert(a[0] == x);
                    assert(a[1] == y);
                    assert(a[2] == z);
                    assert(a[3] == w);
                    assert(z != 1);
                    assert(false); // FAILS
                }
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] match_array_mut_refs verus_code! {
        use vstd::prelude::*;
        fn test() {
            let mut x: [u64; 2] = [0, 1];
            match &mut x {
                [a, b] => {
                    assert(*a == 0);
                    assert(*b == 1);
                    *a = 20;
                    *b = 21;
                }
            }
            assert(x@ == seq![20, 21]);
        }
        fn fails() {
            let mut x: [u64; 2] = [0, 1];
            match &mut x {
                [a, b] => {
                    assert(*a == 0);
                    assert(*b == 1);
                    *a = 20;
                    *b = 21;
                }
            }
            assert(x@ == seq![20, 21]);
            assert(false); // FAILS
        }

        fn test2() {
            let mut x: [u64; 2] = [0, 1];
            match x {
                [ref mut a, ref mut b] => {
                    assert(*a == 0);
                    assert(*b == 1);
                    *a = 20;
                    *b = 21;
                }
            }
            assert(x@ == seq![20, 21]);
        }
        fn fails2() {
            let mut x: [u64; 2] = [0, 1];
            match x {
                [ref mut a, ref mut b] => {
                    assert(*a == 0);
                    assert(*b == 1);
                    *a = 20;
                    *b = 21;
                }
            }
            assert(x@ == seq![20, 21]);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] match_array_count_mismatch verus_code! {
        use vstd::prelude::*;

        fn test(a: &[u64; 3]) {
            match a {
                [x, y, z, w] => {
                }
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "pattern requires 4 elements but array has 3")
}

test_verify_one_file! {
    #[test] match_array_count_generic verus_code! {
        use vstd::prelude::*;

        fn test<const N: usize>(a: &[u64; N]) {
            match a {
                [x, y, z, w] => {
                }
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file! {
    #[test] match_array_bind_by_move_tracked verus_code! {
        tracked struct X { }

        proof fn test(tracked a: [X; 2]) {
            match a {
                [b, _] => { }
            }
            match a {
                [_, b] => { }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] match_array_bind_by_move_tracked2 verus_code! {
        tracked struct X { }

        proof fn test(tracked a: [X; 2]) {
            match a {
                [b, _] => { }
            }
            match a {
                [b, _] => { }
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `a[..]`")
}

test_verify_one_file! {
    #[test] match_array_try_to_move_out_of_index_without_pattern verus_code! {
        struct X { }

        fn test(a: [X; 2]) {
            let r = a[0];
            let r = a[1];
        }
    } => Err(err) => assert_rust_error_msgs(err, &[
        "cannot move out of type `[X; 2]`, a non-copy array",
        "cannot move out of type `[X; 2]`, a non-copy array",
    ])
}

test_verify_one_file! {
    #[test] match_array_with_tracked verus_code! {
        use vstd::prelude::*;

        struct X { }

        proof fn consume(tracked x: &X) { }

        proof fn test(tracked a: &[X; 1]) {
            match a {
                [x] => {
                    consume(x);
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] match_array_with_tracked2 verus_code! {
        use vstd::prelude::*;

        struct X { }

        proof fn consume(tracked x: &X) { }

        proof fn test(a: &[X; 1]) {
            match a {
                [x] => {
                    consume(x);
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] match_array_with_tracked_mut verus_code! {
        use vstd::prelude::*;

        struct X { i: Ghost<u64> }

        proof fn update_m(tracked x: &mut X)
            ensures final(x).i == 20,
        {
            x.i = Ghost(20);
        }

        proof fn test(tracked a: &mut [X; 1])
            requires a.len() == 1 && a[0].i == 5,
        {
            match a {
                [x] => {
                    update_m(x);
                }
            }
            assert(a.len() == 1 && a[0].i == 20);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] match_array_with_spec_mut verus_code! {
        use vstd::prelude::*;
        struct X { }
        proof fn test(a: &mut [X; 1])
        {
            match a {
                [x] => {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a 'mut ref' binding in a pattern is not allowed in spec mode")
}

test_verify_one_file! {
    #[test] spec_match verus_code! {
        use vstd::prelude::*;
        spec fn foo(a: &[Option<u64>; 2]) -> Option<int> {
            match a {
                [None, Some(a)] => Some(a as int),
                [Some(a), None] => Some(a + 1),
                [Some(a), Some(b)] => Some(*a + *b),
                [None, None] => None,
            }
        }

        fn test() {
            assert(foo(&[None, None]) == None);
            assert(foo(&[None, Some(4)]) == Some(4));
            assert(foo(&[Some(4), None]) == Some(5));
            assert(foo(&[Some(7), Some(8)]) == Some(15));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] array_of_mut_refs verus_code! {
        fn test() {
            let mut a = 0;
            let mut b = 1;

            let array = [&mut a, &mut b];

            match array {
                [a_ref, _] => {
                    assert(*a_ref == 0);
                    *a_ref = 20;
                }
            }

            match array {
                [_, b_ref] => {
                    assert(*b_ref == 1);
                    *b_ref = 21;
                }
            }

            assert(a == 20);
            assert(b == 21);
        }

        fn test_fails() {
            let mut a = 0;
            let mut b = 1;

            let array = [&mut a, &mut b];

            match array {
                [a_ref, _] => {
                    assert(*a_ref == 0);
                    *a_ref = 20;
                }
            }

            match array {
                [_, b_ref] => {
                    assert(*b_ref == 1);
                    *b_ref = 21;
                }
            }

            assert(a == 20);
            assert(b == 21);
            assert(false); // FAILS
        }

    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] array_of_mut_refs2 verus_code! {
        fn test() {
            let mut a = 0;
            let mut b = 1;

            let array = [&mut a, &mut b];

            match array {
                [a_ref, b_ref] => {
                    assert(*a_ref == 0);
                    *a_ref = 20;

                    assert(*b_ref == 1);
                    *b_ref = 21;
                }
            }

            assert(a == 20);
            assert(b == 21);
        }

        fn test_fails() {
            let mut a = 0;
            let mut b = 1;

            let array = [&mut a, &mut b];

            match array {
                [a_ref, b_ref] => {
                    assert(*a_ref == 0);
                    *a_ref = 20;

                    assert(*b_ref == 1);
                    *b_ref = 21;
                }
            }

            assert(a == 20);
            assert(b == 21);
            assert(false); // FAILS
        }

    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] array_of_mut_refs3 verus_code! {
        fn test() {
            let mut a = 0;
            let mut b = 1;

            let array = [&mut a, &mut b];

            match array {
                [a_ref, _] => {
                    assert(*a_ref == 0);
                    *a_ref = 20;
                }
            }

            assert(a == 20);
            assert(b == 1);
        }

        fn test_fails() {
            let mut a = 0;
            let mut b = 1;

            let array = [&mut a, &mut b];

            match array {
                [a_ref, _] => {
                    assert(*a_ref == 0);
                    *a_ref = 20;
                }
            }

            assert(a == 20);
            assert(b == 1);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] array_of_mut_refs4 verus_code! {
        fn test() {
            let mut a = 0;
            let mut b = 1;

            let array = [&mut a, &mut b];

            match array {
                [a_ref, b_ref] => {
                    assert(*a_ref == 0);
                    *a_ref = 20;
                }
            }

            assert(a == 20);
            assert(b == 1);
        }

        fn test_fails() {
            let mut a = 0;
            let mut b = 1;

            let array = [&mut a, &mut b];

            match array {
                [a_ref, b_ref] => {
                    assert(*a_ref == 0);
                    *a_ref = 20;
                }
            }

            assert(a == 20);
            assert(b == 1);
            assert(false); // FAILS
        }

    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] array_of_mut_refs_let_decl1 verus_code! {
        fn test() {
            let mut a = 0;
            let mut b = 1;

            let array = [&mut a, &mut b];

            let [a_ref, b_ref] = array;
            assert(*a_ref == 0);
            *a_ref = 20;

            assert(a == 20);
            assert(b == 1);
        }

        fn test_fails() {
            let mut a = 0;
            let mut b = 1;

            let array = [&mut a, &mut b];

            let [a_ref, b_ref] = array;
            assert(*a_ref == 0);
            *a_ref = 20;

            assert(a == 20);
            assert(b == 1);
            assert(false); // FAILS
        }

    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] array_of_mut_refs_let_decl2 verus_code! {
        fn test() {
            let mut a = 0;
            let mut b = 1;

            let array = [&mut a, &mut b];

            let [a_ref, _] = array;
            assert(*a_ref == 0);
            *a_ref = 20;

            let [_, b_ref] = array;
            assert(*b_ref == 1);
            *b_ref = 21;

            assert(a == 20);
            assert(b == 21);
        }

        fn fails() {
            let mut a = 0;
            let mut b = 1;

            let array = [&mut a, &mut b];

            let [a_ref, _] = array;
            assert(*a_ref == 0);
            *a_ref = 20;

            let [_, b_ref] = array;
            assert(*b_ref == 1);
            *b_ref = 21;

            assert(a == 20);
            assert(b == 21);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] array_of_mut_refs_let_else verus_code! {
        fn test(b_in: u64) {
            let mut a = 0;
            let mut b = b_in;

            let array = [&mut a, &mut b];

            let [a_ref, 1] = array else {
                assert(b_in != 1);
                return;
            };

            assert(b_in == 1);
            *a_ref = 20;

            assert(a == 20);
        }

        fn fails(b_in: u64) {
            let mut a = 0;
            let mut b = b_in;

            let array = [&mut a, &mut b];

            let [a_ref, 1] = array else {
                assert(b_in != 1);
                assert(false); // FAILS
                return;
            };

            assert(b_in == 1);
            *a_ref = 20;

            assert(a == 20);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] array_of_mut_refs_if_let verus_code! {
        fn test(b_in: u64) {
            let mut a = 0;
            let mut b = b_in;

            let array = [&mut a, &mut b];

            if let [a_ref, 1] = array {
                assert(b_in == 1);
                *a_ref = 20;
                assert(a == 20);
            } else {
                assert(b_in != 1);
            }
        }

        fn fails(b_in: u64) {
            let mut a = 0;
            let mut b = b_in;

            let array = [&mut a, &mut b];

            if let [a_ref, 1] = array {
                assert(b_in == 1);
                *a_ref = 20;
                assert(a == 20);
                assert(false); // FAILS
            } else {
                assert(b_in != 1);
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}
