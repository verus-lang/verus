#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_189a verus_code! {
        use set::*;

        proof fn test_sets_1() {
            let s1: Set<i32> = Set::empty().insert(1);
            let s2: Set<i32> = Set::empty();
            assert(!s2.contains(1));
            // assert(!s1.ext_equal(s2));
            assert(s1 !== s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_189b verus_code! {
        use set::*;

        spec fn different_set<V>(s: Set<V>) -> Set<V> { s }

        proof fn test_sets_1() {
            let s1: Set<i32> = Set::empty().insert(1);

            assert (exists|s3: Set<i32>| different_set(s3) !== s1) by {
                assert(!different_set(Set::empty()).contains(1i32));
            }
        }
    } => Ok(())
}
