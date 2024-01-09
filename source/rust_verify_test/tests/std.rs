#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] rc_arc verus_code! {
        use std::rc::Rc;
        use std::sync::Arc;

        fn foo() {
            let x = Rc::new(5);
            assert(*x == 5) by {}

            let x1 = x.clone();
            assert(*x1 == 5) by {}

            let y = Arc::new(5);
            assert(*y == 5) by {}

            let y1 = y.clone();
            assert(*y1 == 5) by {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ref_clone verus_code! {
        struct X { }

        fn test2(x: &X) { }

        fn test(x: &X) {
            // Since X is not clone, Rust resolves this to a clone of the reference type &X
            // So this is basically the same as `let y = x;`
            let y = x.clone();
            assert(x == y);
            test2(y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] external_clone_fail verus_code! {
        // Make sure the support for &X clone doesn't mistakenly trigger in other situations

        struct X { }

        #[verifier(external)]
        impl Clone for X {
            fn clone(&self) -> Self {
                X { }
            }
        }

        fn foo(x: &X) {
            let y = x.clone();
        }
    } => Err(err) => assert_vir_error_msg(err, "`crate::X::clone` is not supported")
}

test_verify_one_file! {
    #[test] box_new verus_code! {
        fn foo() {
            let x:Box<u32> = Box::new(5);
            assert(*x == 5);
        }
    } => Ok(())
}

// Indexing into vec

test_verify_one_file! {
    #[test] index_vec_out_of_bounds verus_code! {
        use vstd::*;

        fn stuff<T>(v: Vec<T>) {
            let x = &v[0]; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] index_vec_out_of_bounds2 verus_code! {
        use vstd::*;

        fn stuff<T>(v: &Vec<T>) {
            let x = &v[0]; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] index_vec_out_of_bounds3 verus_code! {
        use vstd::*;

        fn stuff<T>(v: &Vec<T>) {
            let x = v[0]; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] index_vec_in_bounds verus_code! {
        use vstd::*;

        fn stuff(v: &Vec<u8>)
            requires v.len() > 0,
        {
            let a = v[0] < v[0];
            assert(a == false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] index_vec_in_bounds2 verus_code! {
        use vstd::prelude::*;

        fn stuff(v: &mut Vec<u8>)
            requires old(v).len() > 0,
        {
            let a = v[0];
            assert(a == v.view().index(0));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] index_vec_in_bounds3 verus_code! {
        use vstd::prelude::*;

        fn stuff(v: &mut Vec<u8>)
            requires old(v).len() > 0,
        {
            let a = &v[0];
            assert(*a == v.view().index(0));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] index_vec_move_error verus_code! {
        use vstd::*;

        fn stuff<T>(v: Vec<T>) {
            let x = v[0];
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of index of `std::vec::Vec<T>`")
}

test_verify_one_file! {
    #[test] index_vec_move_error2 verus_code! {
        use vstd::*;

        fn stuff<T>(v: &mut Vec<T>) {
            let x = v[0];
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of index of `std::vec::Vec<T>`")
}

test_verify_one_file! {
    #[test] index_vec_mut_error verus_code! {
        use vstd::*;

        fn foo(t: &mut u8) { }

        fn stuff(v: Vec<u8>) {
            foo(&mut v[0]);
        }
    } => Err(err) => assert_vir_error_msg(err, "index for &mut not supported")
}

test_verify_one_file! {
    #[test] signed_wrapping_mul verus_code! {
        use vstd::*;

        fn test() {
            let i = (1000 as i64).wrapping_mul(2000);
            assert(i == 2000000);

            let i = (1000 as i64).wrapping_mul(-2000);
            assert(i == -2000000);

            let i = (12345678901 as i64).wrapping_mul(45678912301);
            assert(i == -7911882469911038895);

            let i = (92345678901 as i64).wrapping_mul(175678912301);
            assert(i == 8500384234389190737);

            let i = (12 as i64).wrapping_mul(2305843009213693952);
            assert(i == -9223372036854775808);

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
