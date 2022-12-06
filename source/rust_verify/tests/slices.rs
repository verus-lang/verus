#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        use pervasive::slice::*;
        use pervasive::vec::*;

        fn foo(x: &[u64])
            requires x@.len() == 2, x[0] == 19,
        {
            let t = *slice_index_get(x, 0);
            assert(t == 19);
        }

        fn foo2(x: Vec<u64>)
            requires x@.len() == 2, x[0] == 19,
        {
            foo(x.as_slice());
        }

        fn foo3(x: &[u64])
        {
            let t = *slice_index_get(x, 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
