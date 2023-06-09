#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] set_literal_0 verus_code! {
        #[allow(unused)]
        use vstd::set::*;

        proof fn sl() {
            let s1: Set<int> = set![];
            let s2: Set<int> = set![];
            assert(s1 =~= s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] set_literal_1 verus_code! {
        #[allow(unused)]
        use vstd::set::*;

        proof fn sl() {
            let s1 = set![2int];
            let s2 = set![2int];
            assert(s1 =~= s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] set_literal_2 verus_code! {
        #[allow(unused)]
        use vstd::set::*;

        proof fn sl() {
            let s1: Set<int> = set![2, 4];
            let s2: Set<int> = set![4, 2];
            assert(s1 =~= s2);
        }

        proof fn comma_at_end() {
            let s1: Set<int> = set![2, 4,];
            let s2: Set<int> = set![4, 2,];
            assert(s1 =~= s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] seq_literals verus_code! {
        #[allow(unused)]
        use vstd::seq::*;

        proof fn sl() {
            let s1: Seq<int> = seq![2, 4, 6, 8, 10];
            assert(s1.index(2) == 6);
        }


        proof fn comma_at_end() {
            let s1: Seq<int> = seq![2, 4, 6, 8, 10,];
            assert(s1.index(2) == 6);
        }

    } => Ok(())
}
