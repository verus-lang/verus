#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] index_trait verus_code! {
        use core::ops::{Index, IndexMut};
        use vstd::prelude::*;

        use vstd::std_specs::core::IndexSpecImpl;

        pub struct One<T>(pub T);

        impl<T> IndexSpecImpl<usize> for One<T> {
            open spec fn index_req(&self, index: &usize) -> bool {
                *index == 0
            }
        }

        impl<T> Index<usize> for One<T> {
            type Output = T;

            fn index(&self, _index: usize) -> (output: &Self::Output)
            ensures
                *output == self.0,
            {
                &self.0
            }
        }

        impl<T> IndexMut<usize> for One<T> {
            fn index_mut(&mut self, _index: usize) -> (output: &mut Self::Output)
            ensures
                *output == old(self).0,
                *final(output) == final(self).0,
            {
                &mut self.0
            }
        }

        fn test_immut(x: &One<u32>) requires x.0 == 3 {
            let value = x[0];
            assert(value == 3);

            let _ = x[1]; // FAILS
        }

        fn test_mut(x: &mut One<u32>)
            requires x.0 == 3
            ensures final(x).0 == 4
        {
            x[0] += 1;
        }
    } => Err(err) => assert_one_fails(err)
}
