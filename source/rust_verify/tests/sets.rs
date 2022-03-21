#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_len code! {
        use crate::pervasive::set::*;

        #[proof]
        fn test_len<A>(s: Set<A>) {
            assert(s.len() as int >= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_len_fails code! {
        use crate::pervasive::set::*;

        #[proof]
        fn test_len<A>(s1: Set<A>, s2: Set<A>) {
            assert(s1.len() == s2.len()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1 code! {
        use crate::pervasive::set::*;
        use crate::pervasive::set_lib::*;

        #[proof]
        fn test_set() {
            let nonneg = Set::new(|i: int| i >= 0);
            assert(forall(|i: int| nonneg.contains(i) == (i >= 0)));
            let pos1 = nonneg.filter(|i: int| i > 0);
            assert(forall(|i: int| pos1.contains(i) == (i > 0)));
            let pos2 = nonneg.map(|i: int| i + 1);
            assert_forall_by(|i: int| {
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
            Set::new(|a: A| exists(|x: A| s.contains(x) && equal(a, f(x))))
        }

        #[proof]
        fn test_set() {
            let nonneg = Set::new(|i: int| i >= 0);
            assert(forall(|i: int| nonneg.contains(i) == (i >= 0)));
            let pos1 = nonneg.filter(|i: int| i > 0);
            assert(forall(|i: int| pos1.contains(i) == (i > 0)));
            let pos2 = set_map(nonneg, |i: int| i + 1);
            assert_forall_by(|i: int| {
                ensures(pos2.contains(i) == (i > 0)); // FAILS
            });
            assert(forall(|i: int| pos2.contains(i) == (i > 0)));
            assert(pos1.ext_equal(pos2));
            assert(equal(pos1, pos2));
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_choose_assert_witness code! {
        use crate::pervasive::set::*;

        #[verifier(opaque)]
        #[spec]
        fn f(x: int) -> bool {
            true
        }

        #[proof]
        fn test_witness() {
            assume(exists(|x: int| f(x)));

            let s = Set::new(|x: int| f(x));
            assert(exists(|x: int| f(x) && s.contains(x)));

            assert(s.contains(s.choose()));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_choose_fails_witness code! {
        use crate::pervasive::set::*;

        #[verifier(opaque)]
        #[spec]
        fn f(x: int) -> bool {
            true
        }

        #[proof]
        fn test_witness() {
            assume(exists(|x: int| f(x)));

            let s = Set::new(|x: int| f(x));

            assert(s.contains(s.choose())); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
