#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        use vstd::set::*;
        use vstd::map::*;

        proof fn test_map() {
            let s1 = Set::<int>::empty().insert(1).insert(2).insert(3);
            let m1 = s1.mk_map(|k: int| 10 * k);
            assert(m1.index(2) == 20);
            let s2 = Set::<int>::empty().insert(1).insert(3).insert(2);
            let m2 = s2.mk_map(|k: int| 3 * k + 7 * k);
            assert(m1 =~= m2);
            let m3 = map![10int => true ==> false, 20int => false ==> true];
            assert(!m3.index(10));
            assert(m3.index(20));
            let m4 = map![10int => true ==> false, 20int => false ==> true,];
            assert(!m4.index(10));
            assert(m4.index(20));
        }

        proof fn testfun_eq() {
            let s = Set::<int>::empty().insert(1).insert(2).insert(3);
            let m1 = s.mk_map(|x: int| x + 4);
            let m2 = s.mk_map(|y: int| y + (2 + 2));
            // m1 and m2 are equal even without extensional equality:
            assert(equal(m1, m2));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 verus_code! {
        use vstd::set::*;
        use vstd::map::*;

        proof fn test_map() {
            let s1 = Set::<int>::empty().insert(1).insert(2).insert(3);
            let m1 = s1.mk_map(|k: int| 10 * k);
            assert(m1.index(2) == 20);
            assert(m1.index(4) == 40); // FAILS
            let s2 = Set::<int>::empty().insert(1).insert(3).insert(2);
            let m2 = s2.mk_map(|k: int| 3 * k + 7 * k);
            assert(m1 =~= m2);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2 verus_code! {
        use vstd::set::*;
        use vstd::map::*;

        proof fn test_map() {
            let s1 = Set::<int>::empty().insert(1).insert(2).insert(3);
            let m1 = s1.mk_map(|k: int| 10 * k);
            assert(m1.index(2) == 20);
            let s2 = Set::<int>::empty().insert(1).insert(3).insert(2);
            let m2 = s2.mk_map(|k: int| 3 * k + 7 * k);
            assert(equal(m1, m2)) by {} // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails_subtype verus_code! {
        use vstd::set::*;
        use vstd::map::*;

        proof fn test_map() {
            let s1 = Set::<int>::empty().insert(1).insert(2).insert(3);
            let m1 = s1.mk_map(|k: int| 10 * k);
            let m3: Map<int, int> = m1;
            let m4: Map<nat, int> = m1; // FAILS: see https://github.com/FStarLang/FStar/issues/1542
        }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file! {
    #[test] test1_fails_eq verus_code! {
        use vstd::set::*;
        use vstd::map::*;

        proof fn testfun_eq() {
            let s = Set::<int>::empty().insert(1).insert(2).insert(3);
            let m1 = s.mk_map(|x: int| x + 4);
            let m2 = s.mk_map(|y: int| (2 + 2) + y);
            // would require extensional equality:
            assert(m1 === m2) by {} // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] map_contains verus_code! {
        use vstd::set::*;
        use vstd::map::*;

        proof fn test() {
            let m = map![10int => 100int, 20int => 200int];
            assert(m.contains_key(10));
            assert(m.contains_value(100));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] set_choose_regression_408 verus_code! {
        use vstd::set::Set;
        proof fn choose_contains_set(m: Set<nat>)
            requires m.finite(), m.len() > 0
        {
            let c = m.choose();
            assert(m.contains(c));
        }
    } => Ok(())
}
