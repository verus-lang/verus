#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] set_literal_0 code! {
        #[allow(unused)]
        use set::*;

        #[proof]
        fn sl() {
            let s1: Set<int> = set![];
            let s2: Set<int> = set![];
            assert(s1.ext_equal(s2));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] set_literal_1 code! {
        #[allow(unused)]
        use set::*;

        #[proof]
        fn sl() {
            let s1 = set![2];
            let s2 = set![2];
            assert(s1.ext_equal(s2));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] set_literal_2 code! {
        #[allow(unused)]
        use set::*;

        #[proof]
        fn sl() {
            let s1 = set![2, 4];
            let s2 = set![4, 2];
            assert(s1.ext_equal(s2));
        }
    } => Ok(())
}
