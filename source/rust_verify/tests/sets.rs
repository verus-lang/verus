#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 code! {
        use crate::pervasive::set::*;

        #[spec]
        pub fn set_map<A, F: Fn(A) -> A>(s: Set<A>, f: F) -> Set<A> {
            set_new(|a: A| exists(|x: A| s.contains(x) && equal(a, f(x))))
        }

        #[proof]
        fn test_set() {
            let nonneg = set_new(|i: int| i >= 0);
            assert(forall(|i: int| nonneg.contains(i) == (i >= 0)));
            let pos1 = nonneg.filter(|i: int| i > 0);
            assert(forall(|i: int| pos1.contains(i) == (i > 0)));
            let pos2 = set_map(nonneg, |i: int| i + 1);
            forall(|i: int| {
                ensures(pos2.contains(i) == (i > 0));
                assert(pos2.contains(i) == nonneg.contains(i - 1));
            });
            assert(forall(|i: int| pos2.contains(i) == (i > 0)));
            assert(pos1.ext_equal(pos2));
            assert(equal(pos1, pos2));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 code! {
        use crate::pervasive::set::*;

        #[spec]
        pub fn set_map<A, F: Fn(A) -> A>(s: Set<A>, f: F) -> Set<A> {
            set_new(|a: A| exists(|x: A| s.contains(x) && equal(a, f(x))))
        }

        #[proof]
        fn test_set() {
            let nonneg = set_new(|i: int| i >= 0);
            assert(forall(|i: int| nonneg.contains(i) == (i >= 0)));
            let pos1 = nonneg.filter(|i: int| i > 0);
            assert(forall(|i: int| pos1.contains(i) == (i > 0)));
            let pos2 = set_map(nonneg, |i: int| i + 1);
            forall(|i: int| {
                ensures(pos2.contains(i) == (i > 0)); // FAILS
            });
            assert(forall(|i: int| pos2.contains(i) == (i > 0)));
            assert(pos1.ext_equal(pos2));
            assert(equal(pos1, pos2));
        }
    } => Err(err) => assert_one_fails(err)
}
