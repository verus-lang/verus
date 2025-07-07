#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_vec_into_iter verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::vec::*;

        fn test() {
            let mut v1: Vec<u32> = Vec::new();
            let mut v2: Vec<u32> = Vec::new();
            v1.push(3);
            v1.push(4);
            assert(v1@ == seq![3u32, 4u32]);

            v2.push(5);
            assert(v2.len() == 1);
            v2.push(7);
            assert(v2@.len() == 2);
            v2.insert(1, 6);
            assert(v2@ == seq![5u32, 6u32, 7u32]);

            v1.append(&mut v2);
            assert(v2@.len() == 0);
            assert(v1@.len() == 5);
            assert(v1@ == seq![3u32, 4u32, 5u32, 6u32, 7u32]);
            v1.remove(2);
            assert(v1@ == seq![3u32, 4u32, 6u32, 7u32]);

            v1.push(8u32);
            v1.push(9u32);
            assert(v1@ == seq![3u32, 4u32, 6u32, 7u32, 8u32, 9u32]);

            v1.swap_remove(5);
            assert(v1@ == seq![3u32, 4u32, 6u32, 7u32, 8u32]);

            let mut i: usize = 0;
            for x in it: v1
                invariant
                    i == it.pos,
                    it.elements == seq![3u32, 4u32, 6u32, 7u32, 8u32],
            {
                assert(x > 2);
                assert(x < 10);
                i = i + 1;
            }
        }
    } => Ok(())
}
